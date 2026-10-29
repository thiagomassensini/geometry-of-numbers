import RelativeDeficit

namespace CarryCriticalRelative
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn CarryCriticalSource
open Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000

/-- The source normalization is inherited, not fitted to a target moment. -/
theorem amp_zero : amp 0 = Complex.I * (Real.sqrt 2 : ℂ)⁻¹ := by
  change canonicalCompletedC3FullWronskianChiralNormalization 0 *
    completedNativePositiveHermiteBiehlerCoordinate 0 = _
  rw [completedNativePositiveHermiteBiehlerCoordinate_zero]
  unfold canonicalCompletedC3FullWronskianChiralNormalization
  field_simp [completedNativeOperatorCharacteristic_zero_ne_zero]

theorem amp_zero_norm_sq : ‖amp 0‖^2 = (1:ℝ)/2 := by
  rw [amp_zero, norm_mul, Complex.norm_I, one_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem first_feature_norm_sq : ‖completedNativeChiralCauchyFeature 0‖^2 = (1:ℝ)/2 := by
  have hi := congrArg Complex.re (inner_completedNativeChiralCauchyFeature 0 0)
  norm_num [inner_self_eq_norm_sq_to_K] at hi
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using hi

theorem first_leading_state : criticalLeadingState 0 0 =
    amp 0 • completedNativeChiralCauchyFeature 0 := by
  simp [criticalLeadingState, criticalOrder, radialIncidentSynthesis, Fin.sum_univ_two,
    completedGreenForwardWeight, completedNativeRadialChiralCauchyState]

theorem first_leading_energy : ‖criticalLeadingState 0 0‖^2 = (1:ℝ)/4 := by
  rw [first_leading_state, norm_smul, mul_pow, amp_zero_norm_sq, first_feature_norm_sq]
  norm_num

theorem empty_prefix_posDef (s : Fin 2) : (sourceMomentMatrix h s.val 0).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian _ _ _)
  intro x hx
  exact (hx (Subsingleton.elim _ _)).elim

theorem first_gap_coefficient : criticalGapCoefficient 0 0 = 8*h 0 := by
  simp [criticalGapCoefficient, first_leading_energy, sourceMomentSchur, dotProduct]
  ring

/-- Positive shrinking relative gap derived from the original central source.
This is an initial-direction calibration, not an all-order sign theorem. -/
theorem first_scaled_relative_deficit :
    Tendsto (fun k : ℕ => ((k:ℝ)+1) * relativeDeficit 0 0 k)
      atTop (nhds (8*h 0)) := by
  simpa only [first_gap_coefficient, physicalGrowth, criticalOrder, Fin.val_zero,
    Nat.mul_zero, zero_add, zero_mul, zero_add, pow_one] using
    critical_scaled_relative_deficit 0 0 (empty_prefix_posDef 0).isUnit

/-- A concrete shrinking contraction, with no pivot-positivity premise. -/
theorem first_source_relative_contraction :
    ∀ᶠ k : ℕ in atTop,
      ‖criticalReturned 0 0 k‖^2 ≤
        (1 - 4*h 0 / ((k:ℝ)+1)) * ‖criticalIncident 0 0 k‖^2 := by
  have hh : 0 < h 0 := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have ht := (tendsto_order.mp first_scaled_relative_deficit).1 (4*h 0) (by linarith)
  have hne := incident_eventually_ne_zero 1 (criticalOrder 0 0)
    (criticalCoordinates 0 0) (criticalOrder_lt 0 0)
    (criticalCoordinates_above 0 0) (criticalCoordinates_top_ne 0 0)
  filter_upwards [ht, hne] with k hlo hk
  rw [critical_pair_exact] at hk
  have hn : 0 < ‖criticalIncident 0 0 k‖^2 := by
    apply sq_pos_of_ne_zero
    simpa only [Submodule.norm_coe] using norm_ne_zero_iff.mpr hk
  have hg : 0 < (k:ℝ)+1 := by positivity
  have hbound : ‖criticalReturned 0 0 k‖^2 / ‖criticalIncident 0 0 k‖^2 <
      1 - 4*h 0/((k:ℝ)+1) := by
    unfold relativeDeficit at hlo
    have hdiv : 4*h 0/((k:ℝ)+1) <
        1 - ‖criticalReturned 0 0 k‖^2 / ‖criticalIncident 0 0 k‖^2 :=
      (div_lt_iff₀ hg).mpr (by nlinarith)
    linarith
  exact le_of_lt ((div_lt_iff₀ hn).mp hbound)

end
end CarryCriticalRelative
