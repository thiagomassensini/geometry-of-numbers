import ProjectionControl
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CarrySelfAdjointOperator.CompletedNativeTaylorResidualNoGo

/-! Quarantined low-order regressions. The construction and all-order
source-kernel identities do NOT depend on these theta-based inequalities.
The counterexample concerns only the normalized scalar-trace projection. -/
namespace CarryCompletedPairing
open CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

theorem projected_gram_zero_ne_canonical (M : ℕ) :
    (inner ℂ (projectedEvenJet M 0) (projectedEvenJet M 0)).re ≠
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [projected_even_gram_00]
  have hb := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  have he : ((1/2 : ℂ)).re = (1/2 : ℝ) := by norm_num
  rw [he]
  linarith

theorem projected_gram_cross_ne_canonical (M : ℕ) :
    inner ℂ (projectedEvenJet M 0) (projectedEvenJet M 1) ≠
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
  rw [projected_even_gram_01]
  intro h
  have he : canonicalCompletedNativeLogDerivativeMoment 1 = 0 := by
    exact_mod_cast h.symm
  exact canonicalCompletedNativeLogDerivativeMoment_one_ne_zero he

theorem not_projected_even_gram_representation (M : ℕ) :
    ¬ ∀ i j : ℕ,
      (inner ℂ (projectedEvenJet M i) (projectedEvenJet M j)).re =
        canonicalCompletedNativeLogDerivativeMoment (i+j) := by
  intro h
  exact projected_gram_zero_ne_canonical M (h 0 0)

end
end CarryCompletedPairing
