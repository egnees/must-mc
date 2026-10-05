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

    fn call(
        &mut self,
        input: Option<(&Message, &str)>,
        local: Option<&str>,
        outputs: &mut Outputs,
    ) {
        if let Some(error) = self.error.clone() {
            self.fail(error, outputs);
            return;
        }
        let process = self
            .process
            .as_mut()
            .expect("successful Python construction");
        let result = if let Some((message, sender)) = input {
            process.on_message_shared(message, sender, None)
        } else {
            let data = format!("{{\"text\":{}}}", crate::json_string(local.unwrap()));
            process.on_local_message_shared(&Message::new("SEND", data), None)
        };
        match result {
            Ok(actions) => self.actions(actions, outputs),
            Err(error) => self.fail(diagnostic(error), outputs),
        }
    }
}

impl Process for Adapter {
    fn on_message(&mut self, message: &str, outputs: &mut Outputs) {
        match decode_message(message) {
            Some((sender, message)) => self.call(Some((&message, &sender)), None, outputs),
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
        self.call(None, Some(message), outputs);
    }
}

fn hex(value: &str) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(value.len() * 2);
    for byte in value.bytes() {
        result.push(char::from(DIGITS[usize::from(byte >> 4)]));
        result.push(char::from(DIGITS[usize::from(byte & 15)]));
    }
    result
}

fn unhex(value: &str) -> Option<String> {
    if value.len() % 2 != 0 {
        return None;
    }
    let mut bytes = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().chunks_exact(2) {
        let digit = |b| match b {
            b'0'..=b'9' => Some(b - b'0'),
            b'a'..=b'f' => Some(b - b'a' + 10),
            _ => None,
        };
        bytes.push(digit(pair[0])? * 16 + digit(pair[1])?);
    }
    String::from_utf8(bytes).ok()
}

fn encode_message(sender: usize, message: &Message) -> String {
    format!("{sender}\n{}\n{}", hex(&message.kind), hex(&message.data))
}

fn decode_message(value: &str) -> Option<(String, Message)> {
    let mut parts = value.split('\n');
    let sender = parts.next()?.to_owned();
    sender.parse::<usize>().ok()?;
    let message = Message::new(unhex(parts.next()?)?, unhex(parts.next()?)?);
    if parts.next().is_some() {
        return None;
    }
    Some((sender, message))
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
    }

    #[test]
    fn python_and_rust_causal_broadcast_explore_the_same_safety_case() {
        let module = PythonModule::new(
            concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/examples/broadcast/fixtures/causal.py"
            ),
            "BroadcastProcess",
            must_python::PythonOptions::default(),
        )
        .unwrap();
        let diagnostics = Diagnostics::default();
        let python = factory(module, diagnostics.clone());
        let rust: Factory = Arc::new(crate::solutions::causal::new);
        let native_events = crate::tests::safety::concurrent::run(rust).unwrap();
        let python_events = crate::tests::safety::concurrent::run(python).unwrap();
        assert!(diagnostics.get().is_none());
        assert_eq!(python_events, native_events);
    }
}
