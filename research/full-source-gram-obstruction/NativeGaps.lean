import NormalizedCrossing
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy

/-! The native h0 bounds are used only to refute the tested realizations.
They do not enter the definitions of state, normal, tangent or projection,
nor are finite certificates extrapolated to all-order Hankel positivity. -/
namespace CarryFullSource
open CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

theorem full_state_native_mass_gap (M : ℕ) :
    23/16 < ‖originalNormalizedState M 0‖^2 - canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hm := center_mass_lower M
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

theorem normal_component_strict_small :
    normalComponentEnergy < canonicalCompletedNativeLogDerivativeMoment 0 / 24 := by
  have hu := normal_component_energy_upper
  have hp := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  have hm := mul_pos hp (sub_pos.mpr hh)
  nlinarith

theorem normal_component_not_native_mass :
    normalComponentEnergy ≠ canonicalCompletedNativeLogDerivativeMoment 0 := by
  have h := normal_component_strict_small
  have hp := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  linarith

/-- No isometric transport of THIS whole normalized source can make its
zeroth Gram entry canonical. This quantifies over real isometries so that
both real quadratures are preserved. It does not exclude different native
jet operators or nonisometric synthesis maps. -/
theorem isometric_transport_not_native_mass
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (U : FullCarrier →ₗᵢ[ℝ] E) (M : ℕ) :
    ‖U (originalNormalizedState M 0)‖^2 ≠ canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [U.norm_map]
  have h := full_state_native_mass_gap M
  linarith

/-- Any ambient operation preserving even ONE forced value coordinate
retains mass at least 1/2, including an orthogonal projection. -/
theorem value_preserving_operation_native_gap (M : ℕ) (P : FullCarrier → FullCarrier)
    (hP : (P (originalNormalizedState M 0)).fst.snd = (originalNormalizedState M 0).fst.snd) :
    7/16 < ‖P (originalNormalizedState M 0)‖^2 - canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hm := value_preserving_mass_lower M _ hP
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

/-- Orthogonally adding independent channels cannot repair the excess
zeroth mass of this state. No assertion about general multibase sewing is
made: a synthesis with actual cross terms is a different construction. -/
theorem orthogonal_extension_not_native_mass
    {E : Type*} [NormedAddCommGroup E] (M : ℕ) (extra : E) :
    ‖WithLp.toLp 2 (originalNormalizedState M 0, extra)‖^2 ≠
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hn := WithLp.norm_fst_le (p := 2) FullCarrier
    (WithLp.toLp 2 (originalNormalizedState M 0, extra))
  change ‖originalNormalizedState M 0‖ ≤ ‖WithLp.toLp 2 (originalNormalizedState M 0, extra)‖ at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  have hg := full_state_native_mass_gap M
  linarith

/-- Necessary gain of a value readout in ANY putative native Gram carrier.
The gain is a conclusion forced by the source normalization and h0 bound,
not a new readout chosen to manufacture positivity. -/
theorem native_mass_value_readout_gain
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (readout : E →L[ℝ] ℂ) (v : E)
    (hmass : ‖v‖^2 = canonicalCompletedNativeLogDerivativeMoment 0)
    (hvalue : readout v = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹) :
    8 < ‖readout‖^2 := by
  have hn := readout.le_opNorm v
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  rw [hvalue, forced_value_norm_sq, mul_pow, hmass] at hs
  have hp : 0 ≤ canonicalCompletedNativeLogDerivativeMoment 0 := by rw [← hmass]; positivity
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  by_contra h
  have hg : ‖readout‖^2 ≤ 8 := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_right hg hp
  linarith

end
end CarryFullSource
