//! Text rendering of executions and of a recorded run.
//!
//! Everything here is read-only and total: it never panics on any graph the explorer
//! can produce.

use std::fmt::Write as _;

use crate::event::{EventId, Label};
use crate::explorer::Execution;
use crate::graph::ExecutionGraph;
use crate::observer::{RecordingObserver, Step, StepKind};

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
        Label::Recv { pred, blocking } => {
            let b = if *blocking { "b" } else { "nb" };
            format!("R{b}[{}]", pred.repr())
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
    let n = g.num_threads();
    if n == 0 {
        return "(empty graph)\n".to_string();
    }
    let heights: Vec<usize> = (0..n).map(|t| g.thread_len(t)).collect();
    let rows = heights.iter().copied().max().unwrap_or(0);

    // Build the cell text for every (thread, row), then pad each column to its width.
    let mut cells: Vec<Vec<String>> = vec![vec![String::new(); n]; rows];
    for (idx, row) in cells.iter_mut().enumerate() {
        for (t, cell) in row.iter_mut().enumerate() {
            if idx < heights[t] {
                *cell = label_cell(g.label(EventId::new(t, idx)));
            }
        }
    }
    let headers: Vec<String> = (0..n).map(|t| format!("T{t}")).collect();
    let widths: Vec<usize> = (0..n)
        .map(|t| {
            let body = (0..rows).map(|r| cells[r][t].len()).max().unwrap_or(0);
            body.max(headers[t].len())
        })
        .collect();

    let mut out = String::new();
    for t in 0..n {
        let _ = write!(out, "{:<width$}  ", headers[t], width = widths[t]);
    }
    out.push('\n');
    for row in cells.iter().take(rows) {
        for (t, cell) in row.iter().enumerate() {
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

/// Render a completed execution: its graph plus the list of pending (unread) sends.
pub fn render_execution(exec: &Execution) -> String {
    let mut out = render_graph(exec.graph());
    out.push_str("pending sends:");
    let pending = exec.pending_sends();
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
