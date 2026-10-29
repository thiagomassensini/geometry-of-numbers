import FullCarrierMass

namespace CarryFullSource
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- The normalization is the existing chart/response normalization, not a
factor inferred from the moments. -/
theorem source_normalization_cancels_collision :
    conj (sourceNormalization 0) * sourceNormalization 0 *
      canonicalCompletedC3FullOperatorRealCollisionNormalization 0 = 1 := by
  have hc := canonicalC3ChartFactorHeight_ne_zero zero_mem_completedNativeHeightDomain
  have hF := completedNativeOperatorCharacteristic_zero_ne_zero
  have hr : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  have hcStar : conj (canonicalC3ChartFactorHeight 0) ≠ 0 := by simpa using hc
  have hFStar : conj (completedNativeOperatorCharacteristic 0) ≠ 0 := by simpa using hF
  have hrSq : (((Real.sqrt 2 : ℝ) : ℂ))^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  unfold sourceNormalization canonicalCompletedC3FullWronskianChiralNormalization
    canonicalCompletedC3FullOperatorRealCollisionNormalization
    canonicalCompletedC3FixedCenterLedgerNormalization mixedHermitianWeight
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  field_simp
  rw [hrSq]
  norm_num only [Complex.ofReal_zero]
  ring

def normalizedNormal : FullCarrier :=
  -canonicalCompletedC3FullWronskianOperator (originalNormalizedState 0 0)

/-- Constant-normalized ORIGINAL physical tangent. A derivative of the
varying normalizing scalar would add a central-state term, orthogonal to
the crossing normal; that term is not asserted absent from the full curve. -/
def normalizedPhysicalTangent : FullCarrier :=
  sourceNormalization 0 • canonicalCompletedC3FullWronskianRealSourceTangent

theorem normalized_normal_eq_scaled :
    normalizedNormal = sourceNormalization 0 • canonicalCompletedC3FullOperatorCrossingNormal := by
  unfold normalizedNormal
  rw [original_state_zero, map_smul,
    canonicalCompletedC3FullOperatorCrossingNormal_eq_neg_operator, smul_neg]

theorem normalized_normal_norm : ‖normalizedNormal‖ = ‖originalNormalizedState 0 0‖ := by
  rw [normalizedNormal, norm_neg, norm_canonicalCompletedC3FullWronskianOperator]

theorem normalized_normal_mass_lower : 3/2 ≤ ‖normalizedNormal‖^2 := by
  rw [normalized_normal_norm]
  exact center_mass_lower 0

theorem normalized_normal_ne_zero : normalizedNormal ≠ 0 := by
  intro hz
  have h := normalized_normal_mass_lower
  rw [hz, norm_zero] at h
  norm_num at h

/-- The source's linear polarized crossing, with every normalization
cancelled by its original identity. No sign of h0 is required. -/
theorem normalized_normal_tangent_pair :
    inner ℂ normalizedNormal normalizedPhysicalTangent =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [normalized_normal_eq_scaled, normalizedPhysicalTangent,
    inner_smul_left, inner_smul_right,
    inner_crossingNormal_realSourceTangent_eq_normalization_mul_h0]
  calc
    _ = (conj (sourceNormalization 0) * sourceNormalization 0 *
        canonicalCompletedC3FullOperatorRealCollisionNormalization 0) *
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by ring
    _ = _ := by rw [source_normalization_cancels_collision, one_mul]

def normalComponent : FullCarrier :=
  (inner ℂ normalizedNormal normalizedPhysicalTangent /
    ((‖normalizedNormal‖^2 : ℝ) : ℂ)) • normalizedNormal

def normalComponentEnergy : ℝ := ‖normalComponent‖^2

/-- Characterization as an orthogonal component in the ORIGINAL metric. -/
theorem normal_component_orthogonal_remainder :
    inner ℂ normalizedNormal (normalizedPhysicalTangent-normalComponent) = 0 := by
  have hn := norm_ne_zero_iff.mpr normalized_normal_ne_zero
  have hnSq : ((‖normalizedNormal‖^2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 hn)
  unfold normalComponent
  rw [inner_sub_right, inner_smul_right]
  have hnn : inner ℂ normalizedNormal normalizedNormal =
      ((‖normalizedNormal‖^2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hnn, div_mul_cancel₀ _ hnSq, sub_self]

theorem normal_center_inner_zero :
    inner ℂ normalizedNormal (originalNormalizedState 0 0) = 0 := by
  have hu := canonicalCompletedC3FullWronskianOperator_center_collision 0
  rw [canonicalCompletedC3FullWronskianOperatorState_zero_eq_centralState] at hu
  have hn : inner ℂ canonicalCompletedC3FullOperatorCrossingNormal
      canonicalCompletedC3FullWronskianCentralState = 0 := by
    rw [← canonicalCompletedC3FullOperatorCrossingFunctional_apply_eq_inner_normal]
    exact hu
  rw [normalized_normal_eq_scaled, original_state_zero, inner_smul_left, inner_smul_right,
    hn, mul_zero, mul_zero]

/-- Thus the omitted derivative of a varying scalar normalization cannot
change this normal component: its contribution is a central-state term. -/
theorem normal_component_invariant_along_center (a : ℂ) :
    (inner ℂ normalizedNormal
      (normalizedPhysicalTangent + a • originalNormalizedState 0 0) /
        ((‖normalizedNormal‖^2 : ℝ) : ℂ)) • normalizedNormal = normalComponent := by
  rw [inner_add_right, inner_smul_right, normal_center_inner_zero, mul_zero, add_zero]
  rfl

theorem normal_component_mem_normal_line : normalComponent ∈ ℂ ∙ normalizedNormal := by
  rw [Submodule.mem_span_singleton]
  exact ⟨_, rfl⟩

/-- Exact energy, rather than a claimed identification with the linear
crossing. The sign information has been squared. -/
theorem normal_component_energy_exact :
    normalComponentEnergy = canonicalCompletedNativeLogDerivativeMoment 0 ^ 2 /
      ‖normalizedNormal‖^2 := by
  have hn := norm_ne_zero_iff.mpr normalized_normal_ne_zero
  unfold normalComponentEnergy normalComponent
  rw [norm_smul, norm_div, mul_pow, div_pow, normalized_normal_tangent_pair]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_real,
    norm_pow, abs_of_nonneg (norm_nonneg _)]
  field_simp

theorem normal_component_energy_upper :
    normalComponentEnergy ≤ (2/3 : ℝ) * canonicalCompletedNativeLogDerivativeMoment 0 ^ 2 := by
  rw [normal_component_energy_exact]
  have hm := normalized_normal_mass_lower
  have hn : 0 < ‖normalizedNormal‖^2 := by nlinarith
  apply (div_le_iff₀ hn).2
  nlinarith [sq_nonneg (canonicalCompletedNativeLogDerivativeMoment 0)]

end
end CarryFullSource
