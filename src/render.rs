//! Text rendering of executions and of a recorded run.
//!
//! Everything here is read-only and total: it never panics on any graph the explorer
//! can produce.

use std::fmt::Write as _;

use crate::event::{EventId, Label};
use crate::explorer::Execution;
use crate::graph::ExecutionGraph;
use crate::observer::{RecordingObserver, Step, StepKind};
use crate::program::TraceLabel;

/// Render one event's label compactly, e.g. `S p2p->2 "1"` or `err "..."`.
fn label_cell(l: &Label) -> String {
    match l {
        Label::Send {
            model,
            dst,
            val,
            window,
        } => {
            // Append the window only for a timed send, so untimed output is unchanged.
            let win = if window.is_untimed() {
                String::new()
            } else {
                format!(" {window}")
            };
            format!("S {model}→{dst} \"{}\"{win}", crate::intern::resolve(*val))
        }
        Label::Recv {
            pred,
            blocking,
            timing,
        } => {
            let b = if *blocking { "b" } else { "nb" };
            let suffix = if timing.is_timed() {
                format!(" {timing}")
            } else {
                String::new()
            };
            format!("R{b}[{}]{suffix}", pred.repr())
        }
        Label::Nondet { set } => {
            let vals: Vec<&str> = set.iter().map(|s| crate::intern::resolve(*s)).collect();
            format!("ND[{}]", vals.join("|"))
        }
        Label::Error { msg } => format!("err \"{msg}\""),
    }
}

/// Render a graph as thread columns (one row per po index) plus its rf edges.
pub fn render_graph(g: &ExecutionGraph) -> String {
    render_annotated_graph(g, &[])
}

fn render_annotated_graph(g: &ExecutionGraph, labels: &[TraceLabel]) -> String {
    let n = labels
        .iter()
        .map(|label| label.tid + 1)
        .max()
        .unwrap_or(0)
        .max(g.num_threads());
    if n == 0 {
        return "(empty graph)\n".to_string();
    }
    let columns: Vec<Vec<String>> = (0..n)
        .map(|tid| {
            let mut column = Vec::new();
            let mut local = labels.iter().filter(|label| label.tid == tid).peekable();
            for idx in 0..=g.thread_len(tid) {
                while let Some(label) = local.next_if(|label| label.position == idx) {
                    column.push(format!("label[{}]", crate::intern::resolve(label.value)));
                }
                if idx < g.thread_len(tid) {
                    let cell = label_cell(g.label(EventId::new(tid, idx)));
                    // Annotation rows have no EventId. Keep the real po indices
                    // visible so rf references still identify the correct cells.
                    column.push(if labels.is_empty() {
                        cell
                    } else {
                        format!("#{idx} {cell}")
                    });
                }
            }
            column
        })
        .collect();
    let rows = columns.iter().map(Vec::len).max().unwrap_or(0);
    let headers: Vec<String> = (0..n).map(|t| format!("T{t}")).collect();
    let widths: Vec<usize> = (0..n)
        .map(|t| {
            let body = columns[t].iter().map(String::len).max().unwrap_or(0);
            body.max(headers[t].len())
        })
        .collect();

    let mut out = String::new();
    for t in 0..n {
        let _ = write!(out, "{:<width$}  ", headers[t], width = widths[t]);
    }
    out.push('\n');
    for row in 0..rows {
        for (t, column) in columns.iter().enumerate() {
            let cell = column.get(row).map_or("", String::as_str);
            let _ = write!(out, "{:<width$}  ", cell, width = widths[t]);
        }
        out.push('\n');
    }

    out.push_str("rf:");
    let recvs = g.recvs();
    if recvs.is_empty() {
        out.push_str(" (none)");
    }
    for r in recvs {
        match g.reads_from(r) {
            Some(s) => {
                let _ = write!(out, " {}←{}", fmt_id(r), fmt_id(s));
            }
            None => {
                let _ = write!(out, " {}←⊥", fmt_id(r));
            }
        }
    }
    out.push('\n');
    out
}

fn fmt_id(e: EventId) -> String {
    format!("⟨{},{}⟩", e.tid, e.idx)
}

/// Render a completed execution with local labels inline in the thread columns,
/// followed by rf edges and the list of pending (unread) sends.
pub fn render_execution(exec: &Execution) -> String {
    render_execution_view(exec.graph(), exec.labels())
}

/// Render a borrowed terminal graph and its ordered local annotations.
pub fn render_execution_view(graph: &ExecutionGraph, labels: &[TraceLabel]) -> String {
    let mut out = render_annotated_graph(graph, labels);
    out.push_str("pending sends:");
    let pending = graph.unread_sends();
    if pending.is_empty() {
        out.push_str(" (none)");
    }
    for s in pending {
        let _ = write!(out, " {}", fmt_id(s));
    }
    out.push('\n');
    out
}

/// One-line description of a recorded step's kind.
fn step_headline(kind: &StepKind) -> String {
    match kind {
        StepKind::EventAdded { e } => format!("+ event {}", fmt_id(*e)),
        StepKind::RfChoice { r, src } => match src {
            Some(s) => format!("rf {}←{}", fmt_id(*r), fmt_id(*s)),
            None => format!("rf {}←⊥", fmt_id(*r)),
        },
        StepKind::Inconsistent => "inconsistent (dropped)".to_string(),
        StepKind::BackwardRevisit { r, s, deleted } => {
            let del: Vec<String> = deleted.iter().map(|&e| fmt_id(e)).collect();
            format!(
                "backward revisit {}←{} (deleted {})",
                fmt_id(*r),
                fmt_id(*s),
                del.join(",")
            )
        }
        StepKind::RevisitRejected { r, s } => {
            format!("revisit rejected {}←{}", fmt_id(*r), fmt_id(*s))
        }
        StepKind::Execution { kind } => format!("== {kind:?} execution =="),
        StepKind::ExecutionFiltered { kind } => {
            format!("== {kind:?} execution (time-filtered) ==")
        }
        StepKind::ThreadBlocked { tid } => format!("thread T{tid} blocked"),
    }
}

/// Render a recorded run as a sequence of numbered steps.
pub fn render_log(rec: &RecordingObserver) -> String {
    let mut out = String::new();
    for (i, step) in rec.steps().iter().enumerate() {
        let _ = writeln!(out, "── step {i}: {} ──", step_headline(&step.kind));
        out.push_str(&render_graph(&step.graph));
        out.push('\n');
    }
    out
}

/// Render a whole step (headline plus graph), useful for tracing a single step.
pub fn render_step(step: &Step) -> String {
    let mut out = format!("{}\n", step_headline(&step.kind));
    out.push_str(&render_graph(&step.graph));
    out
}
