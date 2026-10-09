use std::sync::{Arc, Mutex};

use must_python::{Action, ErrorKind, Message, PythonModule, PythonProcess};

use crate::proc::{Factory, Outputs, Process};

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub status: &'static str,
    pub message: String,
}

#[derive(Clone, Default)]
pub struct Diagnostics(Arc<Mutex<Option<Diagnostic>>>);

impl Diagnostics {
    pub fn clear(&self) {
        *self.0.lock().unwrap() = None;
    }

    pub fn get(&self) -> Option<Diagnostic> {
        self.0.lock().unwrap().clone()
    }

    fn record(&self, error: Diagnostic) {
        self.0.lock().unwrap().get_or_insert(error);
    }
}

fn diagnostic(error: must_python::Error) -> Diagnostic {
    Diagnostic {
        status: match error.kind() {
            ErrorKind::Unsupported => "unsupported",
            ErrorKind::Resource => "inconclusive",
            ErrorKind::Execution | ErrorKind::Transport => "error",
        },
        message: error.to_string(),
    }
}

pub fn factory(module: PythonModule, diagnostics: Diagnostics) -> Factory {
    Arc::new(move |id, nodes| {
        let ids = (0..nodes)
            .map(|n| format!("\"{n}\""))
            .collect::<Vec<_>>()
            .join(",");
        let result = module
            .create(&format!("[\"{id}\",[{ids}]]"))
            .and_then(|mut process| {
                let actions = process.on_start_shared(None)?;
                Ok((process, actions))
            });
        let (process, error) = match result {
            Ok((process, actions)) if actions.is_empty() => (Some(process), None),
            Ok(_) => (
                None,
                Some(Diagnostic {
                    status: "unsupported",
                    message: "broadcast tests do not schedule nonempty on_start effects".into(),
                }),
            ),
            Err(error) => (None, Some(diagnostic(error))),
        };
        if let Some(error) = &error {
            diagnostics.record(error.clone());
        }
        Box::new(Adapter {
            id,
            nodes,
            process,
            error,
            diagnostics: diagnostics.clone(),
        })
    })
}

struct Adapter {
    id: usize,
    nodes: usize,
    process: Option<PythonProcess>,
    error: Option<Diagnostic>,
    diagnostics: Diagnostics,
}

enum Input<'a> {
    Message {
        message: &'a Message,
        sender: &'a str,
    },
    Local(&'a str),
}

impl Adapter {
    fn fail(&mut self, error: Diagnostic, outputs: &mut Outputs) {
        self.diagnostics.record(error.clone());
        outputs.error(format!("Python adapter: {}", error.message));
        self.error = Some(error);
    }

    fn actions(&mut self, actions: Arc<[Action]>, outputs: &mut Outputs) {
        for action in actions.iter() {
            let error = match action {
                Action::Send { to, message } => match to.parse::<usize>() {
                    Ok(destination)
                        if destination < self.nodes && *to == destination.to_string() =>
                    {
                        // Carry the actual sending process separately from the Python payload.
                        outputs.send_message(destination, encode_message(self.id, message));
                        continue;
                    }
                    _ => Diagnostic {
                        status: "error",
                        message: format!("unknown destination {to:?}"),
                    },
                },
                Action::Local { message } if message.kind == "DELIVER" => {
                    match message.string_field("text") {
                        Ok(Some(text)) => {
                            outputs.send_local_message(text);
                            continue;
                        }
                        Ok(None) => Diagnostic {
                            status: "error",
                            message: "DELIVER requires a string 'text' field".into(),
                        },
                        Err(error) => diagnostic(error),
                    }
                }
                Action::Local { message } => Diagnostic {
                    status: "error",
                    message: format!("expected DELIVER, got {:?}", message.kind),
                },
                Action::SetTimer { name, .. } | Action::CancelTimer { name } => Diagnostic {
                    status: "unsupported",
                    message: format!("broadcast tests do not model timers ({name:?})"),
                },
            };
            self.fail(error, outputs);
            return;
        }
    }

    fn call(&mut self, input: Input<'_>, outputs: &mut Outputs) {
        if let Some(error) = self.error.clone() {
            self.fail(error, outputs);
            return;
        }
        let process = self
            .process
            .as_mut()
            .expect("successful Python construction");
        let result = match input {
            Input::Message { message, sender } => process.on_message_shared(message, sender, None),
            Input::Local(text) => {
                let data = format!("{{\"text\":{}}}", json_string(text));
                process.on_local_message_shared(&Message::new("SEND", data), None)
            }
        };
        match result {
            Ok(actions) => self.actions(actions, outputs),
            Err(error) => self.fail(diagnostic(error), outputs),
        }
    }
}

impl Process for Adapter {
    fn receive_predicate(&self) -> Option<crate::proc::ReceivePredicate> {
        let snapshot = match self.process.as_ref()?.receive_predicate() {
            Ok(None) => return None,
            Ok(Some(snapshot)) => snapshot,
            Err(error) => {
                self.diagnostics.record(diagnostic(error));
                return Some(Arc::new(|_| false));
            }
        };
        let diagnostics = self.diagnostics.clone();
        Some(Arc::new(move |payload| {
            let Some((_, kind, data)) = decode_parts(payload) else {
                diagnostics.record(Diagnostic {
                    status: "error",
                    message: "invalid Python message envelope in receive predicate".into(),
                });
                return false;
            };
            match snapshot.matches_parts(kind, data) {
                Ok(accepted) => accepted,
                Err(error) => {
                    diagnostics.record(diagnostic(error));
                    false
                }
            }
        }))
    }

    fn on_message(&mut self, message: &str, outputs: &mut Outputs) {
        match decode_message(message) {
            Some((sender, message)) => self.call(
                Input::Message {
                    message: &message,
                    sender: &sender,
                },
                outputs,
            ),
            None => self.fail(
                Diagnostic {
                    status: "error",
                    message: "invalid Python message envelope".into(),
                },
                outputs,
            ),
        }
    }

    fn on_local_message(&mut self, message: &str, outputs: &mut Outputs) {
        self.call(Input::Local(message), outputs);
    }
}

fn encode_message(sender: usize, message: &Message) -> String {
    format!(
        "{sender}\n{}\n{}{}",
        message.kind.len(),
        message.kind,
        message.data
    )
}

fn decode_parts(value: &str) -> Option<(&str, &str, &str)> {
    let (sender, rest) = value.split_once('\n')?;
    sender.parse::<usize>().ok()?;
    let (length, payload) = rest.split_once('\n')?;
    let length = length.parse::<usize>().ok()?;
    Some((sender, payload.get(..length)?, payload.get(length..)?))
}

fn decode_message(value: &str) -> Option<(String, Message)> {
    let (sender, kind, data) = decode_parts(value)?;
    Some((sender.to_owned(), Message::new(kind, data)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn envelope_keeps_sender_and_arbitrary_payloads() {
        let message = Message::new(
            "\n\"данные",
            r#"{"text":"one\ntwo","nested":[null,{"a":true}]}"#,
        );
        let (sender, decoded) = decode_message(&encode_message(2, &message)).unwrap();
        assert_eq!(sender, "2");
        assert_eq!(decoded.kind, message.kind);
        assert_eq!(decoded.data, message.data);
        assert!(decode_message("not-a-packet").is_none());
        assert!(decode_message("2\n999\nshort").is_none());
        assert!(decode_message("2\n1\né").is_none());
        let multiline = Message::new("", "{\n  \"value\": 1\n}");
        let encoded = encode_message(0, &multiline);
        assert_eq!(
            decode_parts(&encoded),
            Some(("0", "", multiline.data.as_str()))
        );
    }

    #[test]
    fn python_and_rust_causal_broadcast_explore_the_same_case() {
        let rust: Factory = Arc::new(crate::solutions::causal::new);
        let native_events = crate::tests::concurrent::run(rust).unwrap();
        for workers in [1, 12] {
            let module = PythonModule::new(
                concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/examples/broadcast/fixtures/causal.py"
                ),
                "BroadcastProcess",
                must_python::PythonOptions {
                    workers,
                    ..Default::default()
                },
            )
            .unwrap();
            let diagnostics = Diagnostics::default();
            let python_events =
                crate::tests::concurrent::run(factory(module, diagnostics.clone())).unwrap();
            assert!(diagnostics.get().is_none());
            assert_eq!(python_events, native_events);
        }
    }

    #[test]
    fn selective_python_receives_preserve_broadcast_properties() {
        let module = PythonModule::new(
            concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/examples/broadcast/fixtures/causal_filtered.py"
            ),
            "BroadcastProcess",
            must_python::PythonOptions {
                workers: 12,
                ..Default::default()
            },
        )
        .unwrap();
        let diagnostics = Diagnostics::default();
        let factory = factory(module, diagnostics.clone());
        for (name, scenario) in crate::tests::SCENARIOS {
            scenario(factory.clone()).unwrap_or_else(|error| panic!("{name}: {error}"));
            assert!(diagnostics.get().is_none());
        }
    }

    #[test]
    fn predicate_exceptions_reach_diagnostics() {
        let module = PythonModule::new(
            concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/examples/broadcast/fixtures/predicate_error.py"
            ),
            "BroadcastProcess",
            must_python::PythonOptions::default(),
        )
        .unwrap();
        let diagnostics = Diagnostics::default();
        let _ = crate::tests::concurrent::run(factory(module, diagnostics.clone()));
        let error = diagnostics
            .get()
            .expect("predicate errors must not disappear as filtering");
        assert_eq!(error.status, "error");
        assert!(error.message.contains("broken receive predicate"));
    }
}

pub(crate) fn json_string(value: &str) -> String {
    use std::fmt::Write;
    let mut result = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '\x00'..='\x1f' => {
                write!(result, "\\u{:04x}", ch as u32).unwrap();
            }
            _ => result.push(ch),
        }
    }
    result.push('"');
    result
}
