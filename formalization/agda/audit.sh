#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT_DIR"

STAMP="$(date +%Y%m%d-%H%M%S)"
OUT_DIR="$ROOT_DIR/artifacts"
OUT_FILE="$OUT_DIR/postulate-inventory-$STAMP.txt"

echo "== Agda version =="
agda --version

echo ""
echo "== Clean type-check: WFPreservation =="
agda --ignore-interfaces WFPreservation.agda

echo ""
echo "== Clean type-check: TypePreservation =="
agda --ignore-interfaces TypePreservation.agda

echo ""
echo "== Postulate inventory =="
grep -RIn "^[[:space:]]*postulate\b" ./*.agda | tee "$OUT_FILE"

echo ""
echo "Saved inventory to: $OUT_FILE"
