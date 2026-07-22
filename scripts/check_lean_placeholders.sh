#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
cd -- "$repo_root"

if command -v rg >/dev/null 2>&1; then
  scanner="rg"
elif command -v grep >/dev/null 2>&1; then
  scanner="grep"
else
  echo "error: rg or grep is required for the Lean placeholder scan" >&2
  exit 2
fi

allowlist_path="${LEAN_PLACEHOLDER_ALLOWLIST:-scripts/lean_placeholder_allowlist.txt}"
if [[ "$allowlist_path" != /* ]]; then
  allowlist_path="$repo_root/$allowlist_path"
fi
if [[ ! -f "$allowlist_path" ]]; then
  echo "error: Lean placeholder allowlist not found: $allowlist_path" >&2
  exit 2
fi

if (( $# > 0 )); then
  roots=("$@")
else
  roots=(Revres Lemma53)
fi

for root in "${roots[@]}"; do
  if [[ ! -d "$root" ]]; then
    echo "error: Lean source root not found: $root" >&2
    exit 2
  fi
done

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/revres-lean-placeholder.XXXXXX")"
cleanup() {
  rm -rf -- "$tmp_dir"
}
trap cleanup EXIT

observed_raw="$tmp_dir/observed-raw.txt"
observed="$tmp_dir/observed.txt"
allowed_raw="$tmp_dir/allowed-raw.txt"
allowed="$tmp_dir/allowed.txt"
duplicates="$tmp_dir/duplicates.txt"
unexpected="$tmp_dir/unexpected.txt"
stale="$tmp_dir/stale.txt"

set +e
if [[ "$scanner" == "rg" ]]; then
  rg --no-heading --color never --with-filename --glob '*.lean' \
    '\b(sorry|admit|axiom)\b' "${roots[@]}" >"$observed_raw"
else
  grep -R -H -E -w --include='*.lean' \
    '(sorry|admit|axiom)' "${roots[@]}" >"$observed_raw"
fi
scan_status=$?
set -e

case "$scan_status" in
  0 | 1) ;;
  *)
    echo "error: $scanner failed while scanning Lean sources" >&2
    exit "$scan_status"
    ;;
esac

LC_ALL=C sort -u "$observed_raw" >"$observed"

while IFS= read -r record || [[ -n "$record" ]]; do
  trimmed="${record#"${record%%[![:space:]]*}"}"
  if [[ -z "$trimmed" || "$trimmed" == \#* ]]; then
    continue
  fi
  printf '%s\n' "$record"
done <"$allowlist_path" >"$allowed_raw"

LC_ALL=C sort "$allowed_raw" >"$allowed"
LC_ALL=C uniq -d "$allowed" >"$duplicates"
if [[ -s "$duplicates" ]]; then
  echo "error: duplicate Lean placeholder allowlist records:" >&2
  sed 's/^/  /' "$duplicates" >&2
  exit 1
fi

LC_ALL=C comm -23 "$observed" "$allowed" >"$unexpected"
LC_ALL=C comm -13 "$observed" "$allowed" >"$stale"

failed=0
if [[ -s "$unexpected" ]]; then
  failed=1
  echo "error: unexpected Lean placeholder or axiom source lines:" >&2
  while IFS= read -r record; do
    path="${record%%:*}"
    source_line="${record#*:}"
    if [[ -f "$path" ]]; then
      if [[ "$scanner" == "rg" ]]; then
        rg -n --no-heading --color never --with-filename --fixed-strings -- \
          "$source_line" "$path" >&2
      else
        grep -n -H -F -- "$source_line" "$path" >&2
      fi
    else
      printf '  %s\n' "$record" >&2
    fi
  done <"$unexpected"
fi

if [[ -s "$stale" ]]; then
  failed=1
  echo "error: stale Lean placeholder allowlist records:" >&2
  sed 's/^/  /' "$stale" >&2
fi

if (( failed != 0 )); then
  exit 1
fi

match_count="$(wc -l <"$observed" | tr -d '[:space:]')"
roots_display="$(printf '%s, ' "${roots[@]}")"
roots_display="${roots_display%, }"
printf 'Lean placeholder scan passed: %s reviewed prose-only matches in %s using %s.\n' \
  "$match_count" "$roots_display" "$scanner"
