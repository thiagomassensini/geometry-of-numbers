import ComplementRows
import Mathlib.Data.Nat.Choose.Sum

namespace CarryCenteredStirling
open CarrySelfAdjointOperator CarryStencilBoundary CarryOddCauchy NativeLaguerre
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The rational beta sum is recovered directly from the physical complement
and the original Cauchy features, with no replacement kernel. -/
theorem physical_stencil_cauchy_beta (m j : ℕ) :
    (∑ k ∈ Finset.range (m+1), completedGreenForwardWeight m k /
      (((j+k+2:ℕ):ℝ):ℂ)) =
    (-1:ℂ)^m*(m.factorial:ℂ)*((j+1).factorial:ℂ)/((j+m+2).factorial:ℂ) := by
  have hp := congrArg (fun v => inner ℂ (completedNativeChiralCauchyFeature j) v)
    (raw_stencil_complement m)
  simp only [inner_smul_right] at hp
  change inner ℂ (completedNativeChiralCauchyFeature j) (physicalCauchySynthesis (rawStencil m)) =
    (-1:ℂ)^m * complementRow m j at hp
  rw [complement_row_factorial] at hp
  unfold rawStencil at hp
  simp only [map_sum, map_smul, physicalCauchySynthesis, Finsupp.linearCombination_single,
    inner_sum,inner_smul_right,inner_completedNativeChiralCauchyFeature] at hp
  push_cast at hp ⊢
  simpa only [div_eq_mul_inv, mul_assoc, one_mul] using hp

end
end CarryCenteredStirling
