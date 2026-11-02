import SourceGate
import SourceSchurShift

namespace CarrySourceDimensionThree
open CarrySourceBezout CarrySelfAdjointOperator
open scoped Matrix
noncomputable section
set_option autoImplicit false

theorem even_ceiling_unchanged (c : ℕ → ℝ) (d : ℝ) :
    evenSourceCeiling (perturb c 5 d) = evenSourceCeiling c := by
  unfold evenSourceCeiling
  rw [even_prefix_unchanged,even_coupling_unchanged]
  simp [perturb]

theorem odd_ceiling_unchanged (c : ℕ → ℝ) (d : ℝ) :
    oddSourceCeiling (perturb c 6 d) = oddSourceCeiling c := by
  unfold oddSourceCeiling
  rw [odd_prefix_unchanged,odd_coupling_unchanged]
  simp [perturb]

theorem even_critical_unchanged (c : ℕ → ℝ) (d : ℝ) :
    sourceCritical (perturb c 5 d) false 2 = sourceCritical c false 2 := by
  unfold sourceCritical
  rw [even_prefix_unchanged,even_coupling_unchanged]

theorem odd_critical_unchanged (c : ℕ → ℝ) (d : ℝ) :
    sourceCritical (perturb c 6 d) true 2 = sourceCritical c true 2 := by
  unfold sourceCritical
  rw [odd_prefix_unchanged,odd_coupling_unchanged]

#print axioms even_critical_unchanged
#print axioms odd_critical_unchanged
#print axioms even_ceiling_unchanged
#print axioms odd_ceiling_unchanged
end
end CarrySourceDimensionThree
