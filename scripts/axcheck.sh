#!/usr/bin/env bash
# Usage: scripts/axcheck.sh Decl1 Decl2 ...   (names inside namespace VisionTracking)
# Passes iff `lake build` succeeds and every declaration's axioms are exactly
# [propext, Classical.choice, Quot.sound] (no sorryAx).
set -uo pipefail
cd "$(dirname "$0")/.."
lake build > scratch/build.log 2>&1 || { tail -20 scratch/build.log; echo "AXCHECK: FAIL (build)"; exit 1; }
grep -E 'Build completed' scratch/build.log
f=scratch/axcheck_tmp.lean
{ echo "import VisionTracking"; for d in "$@"; do echo "#print axioms VisionTracking.$d"; done; } > "$f"
out=$(lake env lean "$f" 2>&1); rm -f "$f"
echo "$out"
if echo "$out" | grep -q 'sorryAx\|error:'; then echo "AXCHECK: FAIL"; exit 1; fi
n=$(echo "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
if [ "$n" -ne "$#" ]; then echo "AXCHECK: FAIL ($n/$# clean)"; exit 1; fi
echo "AXCHECK: PASS ($n/$#)"
