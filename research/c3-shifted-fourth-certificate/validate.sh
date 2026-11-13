#!/usr/bin/env bash
set -euo pipefail

TASK_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GEOMETRY_ROOT="${GEOMETRY_ROOT:-/home/thlinux/geometry-of-numbers}"
CARRY_ROOT="${CARRY_ROOT:-/home/thlinux/carry-self-adjoint-operator}"
PRIOR_RESEARCH_ROOT="${PRIOR_RESEARCH_ROOT:-/home/thlinux/worktrees/pade-sem-divisao-20261112/research}"
SOURCE_ORIENTATION_DIR="${SOURCE_ORIENTATION_DIR:-/home/thlinux/geometry-of-numbers-c3-source-orientation/research/c3-source-orientation}"
CHIRAL_SOURCE_DIR="${CHIRAL_SOURCE_DIR:-/home/thlinux/worktrees/c3-cofactor-chiral-certification-20261112/research/c3-odd-head-source}"
CORRELATION_DIR="$PRIOR_RESEARCH_ROOT/c3-cofactor-correlation-gate"
CHIRAL_DIR="$PRIOR_RESEARCH_ROOT/c3-cofactor-chiral-certification"

for path in "$GEOMETRY_ROOT" "$CARRY_ROOT" "$CORRELATION_DIR" "$CHIRAL_DIR" "$SOURCE_ORIENTATION_DIR" "$CHIRAL_SOURCE_DIR"; do
  [[ -d "$path" ]] || { printf 'missing dependency path: %s\n' "$path" >&2; exit 2; }
done

mkdir -p "$TASK_DIR/.cache"
base_lean_path="$(cd "$CARRY_ROOT" && lake env printenv LEAN_PATH)"
cache_paths="$(find "$TASK_DIR" "$GEOMETRY_ROOT/research" "$CARRY_ROOT/research" \
  "$PRIOR_RESEARCH_ROOT" "$SOURCE_ORIENTATION_DIR" "$CHIRAL_SOURCE_DIR" -type d -path '*/.cache*' -printf '%p:' 2>/dev/null || true)"
research_build_paths="$(find "$GEOMETRY_ROOT/.lake/build/research" "$CARRY_ROOT/.lake/build/research" \
  -mindepth 1 -maxdepth 1 -type d -printf '%p:' 2>/dev/null || true)"
export LEAN_PATH="$TASK_DIR/.cache:$CORRELATION_DIR/.cache:$CHIRAL_DIR/.cache:$SOURCE_ORIENTATION_DIR/.cache:$CHIRAL_SOURCE_DIR/.cache:$cache_paths$research_build_paths$GEOMETRY_ROOT/.lake/build/lib/lean:$CARRY_ROOT/.lake/build/lib/lean:$base_lean_path"

cd "$CARRY_ROOT"
modules=(
  TightHeadSource
  GammaSeventeen
  M80SourceTransport
  M80CompletedSource
  CorrelatedJets17
  GammaCrosswalk17
  SourceTransport17
  HighChartReciprocal17
  TightNormalizedChart17
  HighSampleAmplitude17
  TightInputTable17
  TightInputCertificates17
  GridArithmetic17
  FastHeadEvaluation17
  GridHeadEvaluation17
  GridJetTable17
  GridJetCertificates17
  HighCoefficientBoxes17
  JetMagnitude17
  CoefficientBoxes17
  FourthGate17
  FourthSourceGate17
  FourthIntervalGate17
)
for module in "${modules[@]}"; do
  printf 'Lean: %s\n' "$module"
  lean -DwarningAsError=true --root="$TASK_DIR" \
    -o "$TASK_DIR/.cache/$module.olean" "$TASK_DIR/$module.lean"
done

printf 'Python integer-grid jet table regeneration check\n'
python3 "$TASK_DIR/generate_grid_jets17.py" --check

printf 'Python rational table regeneration check\n'
python3 "$TASK_DIR/generate_high_amplitudes.py"

printf 'Lean axioms audit\n'
lean -DwarningAsError=true --root="$TASK_DIR" "$TASK_DIR/Audit17.lean"

if rg -n '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom\b' "$TASK_DIR" --glob '*.lean'; then
  printf 'forbidden proof placeholder or axiom found\n' >&2
  exit 1
fi

python3 "$TASK_DIR/preflight_correlated_coefficients.py"
python3 "$TASK_DIR/preflight_source_boxes.py"
git -C "$TASK_DIR/../.." diff --check
