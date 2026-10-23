import CarrySelfAdjointOperator.CompletedC3SymplecticCrossingNormalAudit

/-! Test of the ORIGINAL full completed operator carrier, after its
already prescribed chart and characteristic normalizations. No metric,
source coefficient or moment is used to define the vectors. -/
namespace CarryFullSource
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

abbrev FullCarrier := CanonicalCompletedC3FullWronskianOperatorCarrier

def originalNormalizedState (M : ℕ) (z : ℂ) : FullCarrier :=
  canonicalCompletedC3FullWronskianChiralNormalization z •
    canonicalCompletedC3NormalizedFullWronskianOperatorState M z

def sourceNormalization (z : ℂ) : ℂ :=
  canonicalCompletedC3FullWronskianChiralNormalization z *
    (canonicalC3ChartFactorHeight z)⁻¹

theorem original_state_eq_scaled (M : ℕ) (z : ℂ) :
    originalNormalizedState M z =
      sourceNormalization z • canonicalCompletedC3FullWronskianOperatorState M z := by
  unfold originalNormalizedState canonicalCompletedC3NormalizedFullWronskianOperatorState
    sourceNormalization
  rw [smul_smul]

theorem original_state_zero (M : ℕ) :
    originalNormalizedState M 0 =
      sourceNormalization 0 • canonicalCompletedC3FullWronskianCentralState := by
  rw [original_state_eq_scaled,
    canonicalCompletedC3FullWronskianOperatorState_zero_eq_centralState]

/-- The three value coordinates are equal but retain distinct roles in
the raw, archimedean and chart channels. They are NOT deleted as duplicates. -/
theorem three_value_coordinates (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    let x := originalNormalizedState M z
    (x.fst.snd, x.snd.fst.snd, x.snd.snd.snd) =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹,
       (((Real.sqrt 2 : ℝ) : ℂ))⁻¹,
       (((Real.sqrt 2 : ℝ) : ℂ))⁻¹) := by
  dsimp only
  rw [original_state_eq_scaled,
    canonicalCompletedC3FullWronskianOperatorState_eq_analyticState M hz]
  have hc := canonicalC3ChartFactorHeight_ne_zero hz
  have hr : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  have hFA : nativeXiCompletionFactor z * nativeHeightScalar z ≠ 0 := hF
  have hsimp :
      sourceNormalization z *
        (nativeXiCompletionFactor z * canonicalC3ChartFactorHeight z * nativeHeightScalar z) =
        (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
    unfold sourceNormalization canonicalCompletedC3FullWronskianChiralNormalization
    change (((((Real.sqrt 2 : ℝ) : ℂ)) *
      (nativeXiCompletionFactor z * nativeHeightScalar z))⁻¹ *
      (canonicalC3ChartFactorHeight z)⁻¹) * _ = _
    field_simp [hFA, hc, hr]
    exact div_self hFA
  change
    (sourceNormalization z * (nativeXiCompletionFactor z *
        (canonicalC3ChartFactorHeight z * nativeHeightScalar z)),
     sourceNormalization z * ((nativeHeightScalar z * canonicalC3ChartFactorHeight z) *
        nativeXiCompletionFactor z),
     sourceNormalization z * ((nativeHeightScalar z * nativeXiCompletionFactor z) *
        canonicalC3ChartFactorHeight z)) = _
  have h1 : sourceNormalization z * (nativeXiCompletionFactor z *
      (canonicalC3ChartFactorHeight z * nativeHeightScalar z)) =
      (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
    convert hsimp using 1
    ring
  have h2 : sourceNormalization z * ((nativeHeightScalar z * canonicalC3ChartFactorHeight z) *
      nativeXiCompletionFactor z) = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
    convert hsimp using 1
    ring
  have h3 : sourceNormalization z * ((nativeHeightScalar z * nativeXiCompletionFactor z) *
      canonicalC3ChartFactorHeight z) = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
    convert hsimp using 1
    ring
  rw [h1,h2,h3]

theorem forced_value_norm_sq : ‖((((Real.sqrt 2 : ℝ) : ℂ))⁻¹)‖^2 = (1/2 : ℝ) := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Exact full energy: all three companion coordinates remain as positive
terms. This carrier is the old orthogonal product, not a new metric. -/
theorem full_state_mass_exact (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    let x := originalNormalizedState M z
    ‖x‖^2 = 3/2 + ‖x.fst.fst‖^2 + ‖x.snd.fst.fst‖^2 + ‖x.snd.snd.fst‖^2 := by
  dsimp only
  have hv := three_value_coordinates M hz hF
  have h0 := congrArg Prod.fst hv
  have h1 := congrArg (fun p => p.2.1) hv
  have h2 := congrArg (fun p => p.2.2) hv
  dsimp only at h0 h1 h2
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2, h0, h1, h2, forced_value_norm_sq]
  ring

theorem full_state_mass_lower (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    3/2 ≤ ‖originalNormalizedState M z‖^2 := by
  have h := full_state_mass_exact M hz hF
  dsimp only at h
  nlinarith [sq_nonneg ‖(originalNormalizedState M z).fst.fst‖,
    sq_nonneg ‖(originalNormalizedState M z).snd.fst.fst‖,
    sq_nonneg ‖(originalNormalizedState M z).snd.snd.fst‖]

theorem center_mass_lower (M : ℕ) : 3/2 ≤ ‖originalNormalizedState M 0‖^2 :=
  full_state_mass_lower M zero_mem_completedNativeHeightDomain
    completedNativeOperatorCharacteristic_zero_ne_zero

/-- Keeping just one of the three forced value readouts already enforces
mass at least 1/2, even if all invisible coordinates are changed. -/
theorem value_preserving_mass_lower (M : ℕ) (y : FullCarrier)
    (hy : y.fst.snd = (originalNormalizedState M 0).fst.snd) :
    1/2 ≤ ‖y‖^2 := by
  have hv := congrArg Prod.fst
    (three_value_coordinates M zero_mem_completedNativeHeightDomain
      completedNativeOperatorCharacteristic_zero_ne_zero)
  dsimp only at hv
  have hnorm : ‖y.fst.snd‖ ≤ ‖y‖ :=
    (WithLp.norm_snd_le (p := 2) ℂ y.fst).trans
      (WithLp.norm_fst_le (p := 2) _ y)
  have hs := sq_le_sq₀ (norm_nonneg y.fst.snd) (norm_nonneg y)
  have hsq := hs.mpr hnorm
  rw [hy, hv, forced_value_norm_sq] at hsq
  exact hsq

end
end CarryFullSource
