import TwelveBridge
import SixBoundary

namespace CarrySixthRelative
open CarrySelfAdjointOperator CarryDirectAnchor CarryIntegralCertificate CarryVariationalSchur
open CarryCriticalSource CarrySummableRadial CarryOddEnergy CarryBoundaryReconstruction
open CarryCriticalRadialMargin NativeMomentOrthogonalization
open Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem twelve_critical_anchor_exists_after_grid : ∃ k : ℕ,
    oddGridCutoff (Finset.range 6) ≤ k ∧
      physicalFiniteError 6 (criticalFin 5) k < finiteSourceEnergy 6 (criticalFin 5) k := by
  have hh : ∀ᶠ k : ℕ in atTop,
      oddGridCutoff (Finset.range 6) ≤ k ∧
      physicalFiniteError 6 (criticalFin 5) k < finiteSourceEnergy 6 (criticalFin 5) k := by
    filter_upwards [twelve_critical_anchor_eventually,
      eventually_ge_atTop (oddGridCutoff (Finset.range 6))] with k ha hk
    exact ⟨hk,ha⟩
  exact hh.exists

theorem twelve_critical_form_positive_from_anchor :
    0 < oddCanonicalForm (Finset.range 6) (coefficientFromFin (criticalFin 5)) := by
  obtain ⟨k,hk,ha⟩ := twelve_critical_anchor_exists_after_grid
  apply finite_odd_boundary_positive_of_anchor (Finset.range 6) (coefficientFromFin (criticalFin 5)) k hk
  simpa only [finiteSourceEnergy,physicalFiniteError,mul_comm] using ha

theorem sixth_odd_schur_positive_via_relative_source :
    0 < sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 5 := by
  have h := twelve_critical_form_positive_from_anchor
  rw [finite_odd_form_eq_quadratic] at h
  change 0 < sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 (5+1)
    (Fin.snoc (-((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 5)⁻¹ *ᵥ
      sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment 1 5)) 1) at h
  rw [sourceMomentSchur_critical_direction_of_isUnit _ _ _ twelve_old_isUnit] at h
  exact h

theorem twelve_original_boundary_positive_via_relative_source :
    let a : Fin 6 → ℝ := criticalFin 5
    0 < nativeSourceFiniteBoundaryEnergy 12
      (nativeSourceBoundaryFromParity 6 0 (fun i => (a i:ℂ))) := by
  have hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment (1 : Fin 2).val 5) :=
    twelve_old_isUnit
  have he := native_inverseSchur_boundary_energy (1 : Fin 2) 5 hA
  have hs : (1 : Fin 2) ≠ 0 := by decide
  simp only [hs,if_false] at he
  have he' : nativeSourceFiniteBoundaryEnergy 12
      (nativeSourceBoundaryFromParity 6 0 (fun i => (criticalFin 5 i:ℂ))) =
      4*sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 5 := by
    simpa [criticalFin] using he
  dsimp only
  rw [he']
  exact mul_pos (by norm_num) sixth_odd_schur_positive_via_relative_source

end
end CarrySixthRelative
