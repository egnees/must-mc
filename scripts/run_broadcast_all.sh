#!/usr/bin/env bash
# Run one frozen release checker across the full corpus, one case at a time.
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
    --jobs 1 --threads 12 --timeout 90)
priority_directory=$submissions
if [[ -d "$submissions/04-broadcast" ]]; then
    priority_directory="$submissions/04-broadcast"
fi
for name in artyukhov_dmitriy_a baydakov_kirill_a artemov_mikhail_s; do
    if [[ -f "$priority_directory/$name/broadcast.py" ]]; then
        command+=(--first-submission "$name")
    fi
done
printf 'Starting full corpus with one checker at a time (12 threads, 90s per case).\n'
if command -v caffeinate >/dev/null 2>&1; then
    exec caffeinate -i "${command[@]}"
fi
exec "${command[@]}"
