#!/usr/bin/env bash
# Verify the Agda mechanization type-checks from scratch.
# Prerequisites: Agda ≥ 2.6.4 with agda-stdlib (standard-library) installed.
# Usage: bash check.sh

set -euo pipefail

echo "=== Agda version ==="
agda --version

echo ""
echo "=== Type-checking WFPreservation (postulate-free) ==="
agda --ignore-interfaces WFPreservation.agda
WF_EXIT=$?
echo "WFPreservation exit code: $WF_EXIT"

echo ""
echo "=== Type-checking TypePreservation ==="
agda --ignore-interfaces TypePreservation.agda
TP_EXIT=$?
echo "TypePreservation exit code: $TP_EXIT"

echo ""
echo "=== Type-checking Examples ==="
agda --ignore-interfaces Examples.agda
EX_EXIT=$?
echo "Examples exit code: $EX_EXIT"

echo ""
echo "=== Postulate inventory ==="
grep -n "postulate" *.agda | grep -v "^--" || true

echo ""
echo "=== Summary ==="
echo "WFPreservation:   $([ $WF_EXIT -eq 0 ] && echo 'PASS' || echo 'FAIL')"
echo "TypePreservation: $([ $TP_EXIT -eq 0 ] && echo 'PASS' || echo 'FAIL')"
echo "Examples:         $([ $EX_EXIT -eq 0 ] && echo 'PASS' || echo 'FAIL')"
