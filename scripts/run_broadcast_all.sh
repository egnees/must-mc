#!/usr/bin/env bash
# Run one frozen release checker across the full corpus, one submission at a time.
set -u

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd) || exit 2
submissions=${1:-"$repo/../submissions-2025/04-broadcast"}
output=${2:-"$repo/target/broadcast-all/$(date -u +%Y%m%dT%H%M%SZ)-$$"}
if [[ $# -gt 2 || ! -d "$submissions" ]]; then
    printf 'Usage: %s [submission-directory] [output-directory]\n' "$0" >&2
    exit 2
fi
submissions=$(cd -- "$submissions" && pwd) || exit 2
mkdir -p -- "$output" || exit 2
output=$(cd -- "$output" && pwd) || exit 2

cd -- "$repo" || exit 2
if [[ -n "${CARGO_TOOLCHAIN:-}" ]]; then
    cargo_command=(cargo "+$CARGO_TOOLCHAIN")
else
    cargo_command=(cargo)
fi
printf 'Building release checker; output: %s\n' "$output"
"${cargo_command[@]}" build --release --example broadcast || exit $?
cp -- "$repo/target/release/examples/broadcast" "$output/broadcast" || exit 2
chmod +x "$output/broadcast" || exit 2
mkdir -p -- "$output/work" || exit 2
cd -- "$output/work" || exit 2

command=(python3 "$repo/scripts/test_broadcast_submissions.py" "$submissions"
    --binary "$output/broadcast" --output "$output"
    --jobs 1 --timeout 90)
printf 'Starting full corpus with one checker at a time (90s per submission).\n'
if command -v caffeinate >/dev/null 2>&1; then
    exec caffeinate -i "${command[@]}"
fi
exec "${command[@]}"
