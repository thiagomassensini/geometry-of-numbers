#!/usr/bin/env python3
"""Emit a one-node proof certificate from exact Lean #eval floor output."""
from pathlib import Path
import re

case = Path(__file__).resolve().parent
repo = case.parents[5]
log = case / "core-node-pilot.log"
text = log.read_text()
if "BUILD_EXIT=0" not in text:
    raise SystemExit("the exact rational-core probe did not build successfully")
values = {}
for key in ("core.lo", "core.hi"):
    found = re.findall(rf'^\"?{re.escape(key)}=([0-9]+)\"?$', text, re.M)
    if len(found) != 1:
        raise SystemExit(f"expected one exact integer for {key}")
    values[key] = found[0]
lo, hi = values["core.lo"], values["core.hi"]
if int(hi) != int(lo) + 1:
    raise SystemExit("the dyadic enclosure is not the expected adjacent-integer interval")
source = f'''import SigmaC5GammaCoreNodePilot
import Mathlib.Tactic

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5GammaCoreNodePilotBox : ComplexInterval :=
  {{ re := {{ lo := ({lo} : ℚ) / (2 : ℚ) ^ 1024,
            hi := ({hi} : ℚ) / (2 : ℚ) ^ 1024,
            le := by
              have hnum : ({lo} : ℚ) ≤ ({hi} : ℚ) := by norm_num
              exact div_le_div_of_nonneg_right hnum (by positivity) }},
    im := Interval.exact 0 }}

theorem c5GammaCoreNodePilot_scaled_floor :
    Int.floor c5GammaCoreNodePilotScaled = {lo} := by
  norm_num (config := {{ maxSteps := 10000000 }})
    [c5GammaCoreNodePilotScaled, c5GammaCoreNodePilot,
      gammaFiniteRationalCore, ratGammaTerm, ratComplexInv, ratComplexMul,
      Finset.sum_range_succ]

theorem c5GammaCoreNodePilot_rational_core_contains :
    c5GammaCoreNodePilotBox.contains
      (ratComplexToComplex c5GammaCoreNodePilot) := by
  have hden : (0 : ℚ) < (2 : ℚ) ^ 1024 := by positivity
  have hlo : ({lo} : ℚ) ≤ c5GammaCoreNodePilotScaled := by
    have h := Int.floor_le c5GammaCoreNodePilotScaled
    rw [c5GammaCoreNodePilot_scaled_floor] at h
    exact_mod_cast h
  have hhi : c5GammaCoreNodePilotScaled ≤ ({hi} : ℚ) := by
    have h := Int.lt_floor_add_one c5GammaCoreNodePilotScaled
    rw [c5GammaCoreNodePilot_scaled_floor] at h
    have h' : ({lo} : ℚ) + 1 = ({hi} : ℚ) := by norm_num
    have h'' : c5GammaCoreNodePilotScaled < ({hi} : ℚ) := by
      calc
        c5GammaCoreNodePilotScaled < ({lo} : ℚ) + 1 := h
        _ = ({hi} : ℚ) := h'
    exact le_of_lt h''
  have hq : ({lo} : ℚ) / (2 : ℚ) ^ 1024 ≤ c5GammaCoreNodePilot.1 ∧
      c5GammaCoreNodePilot.1 ≤ ({hi} : ℚ) / (2 : ℚ) ^ 1024 := by
    constructor
    · rw [div_le_iff₀ hden]
      simpa [c5GammaCoreNodePilotScaled] using hlo
    · rw [le_div_iff₀ hden]
      simpa [c5GammaCoreNodePilotScaled] using hhi
  have him : c5GammaCoreNodePilot.2 = 0 := by
    simp [c5GammaCoreNodePilot, gammaFiniteRationalCore, Finset.sum_apply,
      ratGammaTerm, ratComplexInv, ratComplexMul]
  simp only [ComplexInterval.contains, Interval.contains,
    c5GammaCoreNodePilotBox, Interval.exact, ratComplexToComplex]
  constructor
  · constructor
    · exact_mod_cast hq.1
    · exact_mod_cast hq.2
  · simp [him]

#print axioms c5GammaCoreNodePilot_scaled_floor
#print axioms c5GammaCoreNodePilot_rational_core_contains
'''
target = repo / "research/native-moving-schur-sigma/SigmaC5GammaCoreNodeCertificate.lean"
target.write_text(source)
(case / target.name).write_text(source)
print(f"wrote {target}")
