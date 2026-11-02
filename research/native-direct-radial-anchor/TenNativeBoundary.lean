import TenExplicitCutoff
import SixBoundary

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryCriticalTfvd CarryOddEnergy CarrySummableRadial
open CarryBoundaryReconstruction CarryCriticalRadialMargin NativeMomentOrthogonalization
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem ten_critical_form_positive_from_finite_source :
    0 < oddCanonicalForm (Finset.range 5) (coefficientFromFin (criticalFin 4)) := by
  apply finite_odd_boundary_positive_of_anchor (Finset.range 5) (coefficientFromFin (criticalFin 4)) tenCriticalCutoff
  · exact ten_anchor_cutoff.trans (le_max_left _ _)
  · have h := ten_critical_anchor_at_explicit_cutoff tenCriticalCutoff le_rfl
    simpa only [finiteSourceEnergy,physicalFiniteError,mul_comm] using h

/-- The fifth shifted odd Schur value follows from the finite physical anchor
and its tail. No new-pivot positivity is an input. -/
theorem fifth_odd_schur_positive_via_direct_source :
    0 < sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 4 := by
  have h := ten_critical_form_positive_from_finite_source
  rw [finite_odd_form_eq_quadratic] at h
  change 0 < sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 (4+1)
    (Fin.snoc (-((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 4)⁻¹ *ᵥ
      sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment 1 4)) 1) at h
  rw [sourceMomentSchur_critical_direction_of_isUnit _ _ _ ten_old_block_isUnit] at h
  exact h

/-- The same critical source transported to the ORIGINAL odd boundary,
with the factor four from PR #41 unchanged. -/
theorem ten_original_boundary_positive_via_direct_source :
    let a : Fin 5 → ℝ := criticalFin 4
    0 < nativeSourceFiniteBoundaryEnergy 10
      (nativeSourceBoundaryFromParity 5 0 (fun i => (a i:ℂ))) := by
  have hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment (1 : Fin 2).val 4) :=
    ten_old_block_isUnit
  have he := native_inverseSchur_boundary_energy (1 : Fin 2) 4 hA
  have hs : (1 : Fin 2) ≠ 0 := by decide
  simp only [hs,if_false] at he
  have he' : nativeSourceFiniteBoundaryEnergy 10
      (nativeSourceBoundaryFromParity 5 0 (fun i => (criticalFin 4 i:ℂ))) =
      4*sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 4 := by
    simpa [criticalFin] using he
  dsimp only
  rw [he']
  exact mul_pos (by norm_num) fifth_odd_schur_positive_via_direct_source

end
end CarryDirectAnchor
