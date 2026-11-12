#!/usr/bin/env bash
set -euo pipefail

TASK_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$TASK_DIR/../.." && pwd)"
USER_ROOT="$(cd "$TASK_DIR/../../../.." && pwd)"
CARRY_ROOT="${CARRY_SELF_ADJOINT_OPERATOR_ROOT:-$USER_ROOT/carry-self-adjoint-operator}"
GEOMETRY_ROOT="${GEOMETRY_OF_NUMBERS_ROOT:-$USER_ROOT/geometry-of-numbers}"
LEAN_BIN="${LEAN_BIN:-lean}"

cd "$CARRY_ROOT"
base_lean_path="$(lake env printenv LEAN_PATH)"
cache_paths="$(find "$ROOT/research" "$CARRY_ROOT/research" \
  "$GEOMETRY_ROOT/research" \
  "$USER_ROOT/geometry-of-numbers-c3-source-orientation/research" \
  "$USER_ROOT/geometry-of-numbers-critical-tilt-prime/research" \
  -type d \( -name .cache -o -path '*/.cache/*' \) \
  -printf '%p:' 2>/dev/null || true)"
research_build_paths="$(find "$GEOMETRY_ROOT/.lake/build/research" \
  "$CARRY_ROOT/.lake/build/research" -mindepth 1 -maxdepth 1 -type d \
  -printf '%p:' 2>/dev/null || true)"
export LEAN_PATH="$TASK_DIR/.cache:$cache_paths$research_build_paths$GEOMETRY_ROOT/.lake/build/lib/lean:$CARRY_ROOT/.lake/build/lib/lean:$base_lean_path"

mkdir -p "$TASK_DIR/.cache"
compile() {
  local module="$1"
  local source="$2"
  "$LEAN_BIN" -DwarningAsError=true --root="$TASK_DIR" \
    -o "$TASK_DIR/.cache/$module.olean" "$source"
}

for module in CorrelationGate ChartReciprocal BaseCoefficient CompletedCoefficient \
  CorrelationInterval LeftJetMagnitudeLow LeftJetMagnitudeHigh LeftJetMagnitude \
  BoundaryTransport FiniteReferenceTable; do
  compile "$module" "$TASK_DIR/$module.lean"
done

"$LEAN_BIN" -DwarningAsError=true \
  --root="$ROOT/research/c3-cofactor-chiral-certification" \
  -o "$ROOT/research/c3-cofactor-chiral-certification/.cache/SourceGate.olean" \
  "$ROOT/research/c3-cofactor-chiral-certification/SourceGate.lean"
compile SourceCoefficientGreen "$TASK_DIR/SourceCoefficientGreen.lean"

python3 "$TASK_DIR/diagnose_correlated_coefficients.py"
python3 "$TASK_DIR/emit_exact_interval_tables.py" > "$TASK_DIR/.cache/exact_interval_tables.txt"
git -C "$ROOT" diff --check
