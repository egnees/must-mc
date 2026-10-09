use must::{Program, ThreadNext, TraceLabel, Val};

struct LegacyPrefixes;

impl Program for LegacyPrefixes {
    fn num_threads(&self) -> usize {
        1
    }

    fn next(&self, _traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
        vec![ThreadNext::Finished]
    }

    fn labels_at_prefixes(&self, tokens: &[u64]) -> Option<Vec<TraceLabel>> {
        match tokens {
            [0] => Some(Vec::new()),
            [1] => Some(vec![
                TraceLabel {
                    tid: 0,
                    position: 1,
                    value: "first".into(),
                },
                TraceLabel {
                    tid: 0,
                    position: 1,
                    value: "second".into(),
                },
            ]),
            _ => None,
        }
    }
}

#[test]
fn default_adapter_replaces_and_clears_reused_storage() {
    let program = LegacyPrefixes;
    let mut out = Vec::with_capacity(16);
    for tokens in [&[1][..], &[0], &[1], &[], &[1], &[1, 0], &[99]] {
        let expected = program.labels_at_prefixes(tokens);
        assert_eq!(
            program.labels_at_prefixes_into(tokens, &mut out),
            expected.is_some()
        );
        assert_eq!(out, expected.unwrap_or_default());
        assert_eq!(out.capacity(), 16);
    }
}

#[test]
fn unavailable_default_clears_previous_annotations() {
    struct Unknown;
    impl Program for Unknown {
        fn num_threads(&self) -> usize {
            0
        }
        fn next(&self, _traces: &[Vec<Option<Val>>]) -> Vec<ThreadNext> {
            Vec::new()
        }
    }
    let mut out = LegacyPrefixes.labels_at_prefixes(&[1]).unwrap();
    assert!(!Unknown.labels_at_prefixes_into(&[], &mut out));
    assert!(out.is_empty());
}
