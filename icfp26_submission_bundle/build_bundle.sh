#!/usr/bin/env bash
# Build a clean, anonymous Agda supplementary bundle for ICFP 2026 submission.
# Usage: bash icfp26_submission_bundle/build_bundle.sh
# Output: icfp26_submission_bundle/out/  (ready to zip and upload to HotCRP)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
AGDA_SRC="$(cd "$SCRIPT_DIR/../formalization/agda" && pwd)"
OUT="$SCRIPT_DIR/out"

warn_if_out_modified() {
  [[ -d "$OUT" ]] || return 0

  local mismatches=()
  local src dst

  check_pair() {
    src="$1"
    dst="$2"
    if [[ -f "$dst" ]] && ! cmp -s "$src" "$dst"; then
      mismatches+=("$dst")
    fi
  }

  check_pair "$AGDA_SRC/SubAsync.agda" "$OUT/SubAsync.agda"
  check_pair "$AGDA_SRC/WellFormedness.agda" "$OUT/WellFormedness.agda"
  check_pair "$AGDA_SRC/Reductions.agda" "$OUT/Reductions.agda"
  check_pair "$AGDA_SRC/WFPreservation.agda" "$OUT/WFPreservation.agda"
  check_pair "$AGDA_SRC/Types.agda" "$OUT/Types.agda"
  check_pair "$AGDA_SRC/TypePreservation.agda" "$OUT/TypePreservation.agda"
  check_pair "$AGDA_SRC/Examples.agda" "$OUT/Examples.agda"
  check_pair "$AGDA_SRC/sub-async-formalization.agda-lib" "$OUT/sub-async-formalization.agda-lib"
  check_pair "$SCRIPT_DIR/README-submission.md" "$OUT/README.md"
  check_pair "$SCRIPT_DIR/check.sh" "$OUT/check.sh"

  if (( ${#mismatches[@]} > 0 )); then
    echo "WARNING: Existing out/ differs from source inputs." >&2
    echo "This usually means out/ was manually edited or has stale generated files." >&2
    echo "Changed files detected in out/:" >&2
    for f in "${mismatches[@]}"; do
      echo "  - $f" >&2
    done
    echo "Rebuild will overwrite out/." >&2
    echo "" >&2
  fi
}

# ── Clean previous build ──────────────────────────────────────────────
warn_if_out_modified
rm -rf "$OUT"
mkdir -p "$OUT"

# ── Copy Agda source files (7 modules: 4 core + Types + TypePres + Examples) ──
MODULES=(
  SubAsync.agda
  WellFormedness.agda
  Reductions.agda
  WFPreservation.agda
  Types.agda
  TypePreservation.agda
  Examples.agda
)

for f in "${MODULES[@]}"; do
  if [[ ! -f "$AGDA_SRC/$f" ]]; then
    echo "ERROR: $f not found in $AGDA_SRC" >&2
    exit 1
  fi
  cp "$AGDA_SRC/$f" "$OUT/"
done

# ── Copy library descriptor ──────────────────────────────────────────
cp "$AGDA_SRC/sub-async-formalization.agda-lib" "$OUT/"

# ── Copy submission README (anonymous) ───────────────────────────────
cp "$SCRIPT_DIR/README-submission.md" "$OUT/README.md"

# ── Copy verification script ─────────────────────────────────────────
cp "$SCRIPT_DIR/check.sh" "$OUT/"

# ── Summary ───────────────────────────────────────────────────────────
echo "Bundle built in $OUT/"
echo "Contents:"
ls -1 "$OUT/"
echo ""
echo "LOC: $(cat "$OUT"/*.agda | wc -l) lines across ${#MODULES[@]} modules"
echo ""
echo "To create zip: cd $OUT && zip -r ../agda-mechanization.zip ."
