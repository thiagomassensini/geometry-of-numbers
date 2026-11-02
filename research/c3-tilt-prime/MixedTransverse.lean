import MixedInfinite
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Derivada transversal do tilt C3 em deslocamento arbitrário

Este módulo demonstra a derivada célula a célula em qualquer deslocamento.
A troca da derivada com a soma infinita não decorre apenas deste teorema; a
continuação em `TransverseSwap.lean` prova essa troca por convergência dominada,
com cota somável uniforme dos quocientes de diferença.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Derivada em `δ` do tilt C3 em qualquer deslocamento (a fonte só tinha `δ=0`). -/
def cpTiltThreeDeriv (c δ : ℝ) : ℝ :=
  -Real.log (c - 1) * (c - 1) ^ (-δ) - Real.log (c + 1) * (c + 1) ^ (-δ) +
    2 * Real.log c * c ^ (-δ)

theorem hasDerivAt_cpTilt_three (c : ℝ) (hc : 1 < c) (δ : ℝ) :
    HasDerivAt (fun d : ℝ => cpTilt 3 d c) (cpTiltThreeDeriv c δ) δ := by
  have hleft : HasDerivAt (fun d : ℝ => (c - 1) ^ (-d))
      (-Real.log (c - 1) * (c - 1) ^ (-δ)) δ := by
    have h := (hasDerivAt_neg' δ).const_rpow (show (0:ℝ) < c - 1 by linarith)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hright : HasDerivAt (fun d : ℝ => (c + 1) ^ (-d))
      (-Real.log (c + 1) * (c + 1) ^ (-δ)) δ := by
    have h := (hasDerivAt_neg' δ).const_rpow (show (0:ℝ) < c + 1 by linarith)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hmiddle : HasDerivAt (fun d : ℝ => c ^ (-d))
      (-Real.log c * c ^ (-δ)) δ := by
    have h := (hasDerivAt_neg' δ).const_rpow (show (0:ℝ) < c by linarith)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  rw [show (fun d : ℝ => cpTilt 3 d c) =
      (fun d : ℝ => (c - 1) ^ (-d) + (c + 1) ^ (-d) - 2 * c ^ (-d)) by
    funext d
    rw [cpTilt_three_eq_cpPairTilt_one]
    simp [cpPairTilt]]
  refine ((hleft.add hright).sub (hmiddle.const_mul 2)).congr_deriv ?_
  unfold cpTiltThreeDeriv
  ring

#print axioms hasDerivAt_cpTilt_three

end
end CarryTiltSlice
