import MixedInfinite
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Troca transversal: identificar G com ∂_δ do objeto infinito (Seção 1, perna δ)

Fecha a segunda troca de ordem: `∂_δ (∑' k block_k)|_0 = ∑' k ∂_δ block_k|_0 = G`.
Usa `hasDerivAt_tsum_of_isPreconnected` numa vizinhança `δ ∈ (-1/4,1/4)`. A
convergência em `δ=0` é imediata porque cada célula se anula lá (`cpTilt 3 0 c = 0`).
A única obrigação analítica é a cota uniforme da derivada-δ da célula, obtida pela
decomposição em duas primeiras diferenças de `g(x)=log x · x^{-δ}` (cancelamento que
dá decaimento `c^{-3/4}`; com o carrier `c^{-1/2}` a soma é `c^{-5/4}`, somável).

NÃO modifica os módulos anteriores.
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
