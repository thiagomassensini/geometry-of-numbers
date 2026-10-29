import MixedLedger
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A source-derived sign for the retained-leg divided difference at the
center. Only the existing FIRST material Hilbert derivative is used. -/
namespace CarryMixedGreen
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryMaterialResponseComparison Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

theorem value_probe_origin : valueProbe 0 = 0 := by
  simp [valueProbe, carryMaterialClock_compressed_pair_origin]

/-- The full original value leg is differentiated before its scalar probe. -/
theorem compressed_value_origin_derivative :
    HasDerivAt (fun t : ℝ => (carryMaterialClockCompressedPair t).2)
      ((-2*Complex.I*baseTwoCanonicalDressingScalar 0) • carryMaterialClockCentralForcing) 0 := by
  have hd := (baseTwoCanonicalDressingScalar_analyticAt 0).differentiableAt.hasDerivAt
  have hv : HasDerivAt
      (fun t : ℝ => (2:ℂ) • (baseTwoCanonicalDressingScalar t • carryMaterialClockComplementState t))
      ((2:ℂ) • (baseTwoCanonicalDressingScalar 0 • (-Complex.I • carryMaterialClockCentralForcing) +
        deriv baseTwoCanonicalDressingScalar 0 • carryMaterialClockComplementState 0)) 0 :=
    (hd.smul carryMaterialClock_complement_origin_derivative).const_smul (2:ℂ)
  have he : (fun t : ℝ => (carryMaterialClockCompressedPair t).2) =
      (fun t : ℝ => (2:ℂ) • (baseTwoCanonicalDressingScalar t • carryMaterialClockComplementState t)) := by
    funext t
    simp only [carryMaterialClockCompressedPair, carryMaterialPairDressing, smul_smul]
    congr 1
    ring
  rw [he]
  apply hv.congr_deriv
  simp only [carryMaterialClock_complement_origin, smul_zero, add_zero, smul_smul]
  congr 1
  ring

theorem value_probe_origin_derivative :
    HasDerivAt valueProbe
      ((-2*Complex.I*baseTwoCanonicalDressingScalar 0)*
        inner ℂ carryMaterialClockCentralForcing carryMaterialClockCentralForcing) 0 := by
  have h := ((innerSL ℂ carryMaterialClockCentralForcing).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    compressed_value_origin_derivative
  change HasDerivAt valueProbe
    (inner ℂ carryMaterialClockCentralForcing
      ((-2*Complex.I*baseTwoCanonicalDressingScalar 0) • carryMaterialClockCentralForcing)) 0 at h
  simpa only [inner_smul_right] using h

theorem forcing_scalar_differentiable (t : ℝ) :
    DifferentiableAt ℝ carryMaterialClockForcingScalar t := by
  have hY := (carryMaterialClockCentralCoefficient.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (completedBoundaryState_hasDerivAt_clock t)
  exact ((differentiableAt_const (Complex.I:ℂ)).mul
    (baseTwoCanonicalDressingScalar_analyticAt t).differentiableAt).mul hY.differentiableAt

theorem value_ratio_origin : valueRatio 0 = 0 := by
  simp [valueRatio, value_probe_origin]

/-- The common dressing cancels in THIS observation only. The full
companion and its hidden Green balance still retain the completion. -/
theorem value_ratio_undressed (t : ℝ)
    (hα : carryMaterialClockCentralCoefficient (baseTwoCompletedBoundaryHilbertState t) ≠ 0) :
    valueRatio t = 2*Complex.I*
      inner ℂ carryMaterialClockCentralForcing (carryMaterialClockComplementState t) /
        carryMaterialClockCentralCoefficient (baseTwoCompletedBoundaryHilbertState t) := by
  simp only [valueRatio, valueProbe, carryMaterialClockCompressedPair, carryMaterialPairDressing,
    inner_smul_right, carryMaterialClockForcingScalar]
  have hd := baseTwoCanonicalDressingScalar_ne_zero t
  field_simp
  simp only [Complex.I_sq]
  ring

/-- Strictly positive, fixed by the original physical forcing; no theta
box, moment pivot, height or positive Hankel is an input. -/
theorem value_ratio_origin_derivative :
    HasDerivAt valueRatio ((2*‖carryMaterialClockCentralForcing‖^2:ℝ):ℂ) 0 := by
  have h := value_probe_origin_derivative.neg.div
    (forcing_scalar_differentiable 0).hasDerivAt forcing_scalar_zero_ne
  change HasDerivAt valueRatio _ 0 at h
  apply h.congr_deriv
  dsimp only [Pi.neg_apply]
  rw [value_probe_origin, neg_zero, zero_mul, sub_zero]
  have hf : carryMaterialClockForcingScalar 0 = Complex.I*baseTwoCanonicalDressingScalar 0 := by
    simp [carryMaterialClockForcingScalar, carryMaterialClock_central_coefficient_zero]
  have hw : inner ℂ carryMaterialClockCentralForcing carryMaterialClockCentralForcing =
      ((‖carryMaterialClockCentralForcing‖^2:ℝ):ℂ) := by
    apply Complex.ext
    · exact material_inner_self_re _
    · exact inner_self_im (𝕜 := ℂ) carryMaterialClockCentralForcing
  rw [hf, hw]
  have hd := baseTwoCanonicalDressingScalar_ne_zero 0
  push_cast
  field_simp

theorem forcing_slope_pos : 0 < 2*‖carryMaterialClockCentralForcing‖^2 :=
  mul_pos (by norm_num) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr carryMaterialClock_forcing_nonzero))

theorem forcing_slope_material_lower : (1/16:ℝ) < 2*‖carryMaterialClockCentralForcing‖^2 := by
  have h := carryMaterialCentralClock_complement_norm_lower
  change (1/32:ℝ) < ‖carryMaterialClockCentralForcing‖^2 at h
  linarith

theorem value_ratio_slope_tendsto :
    Tendsto (fun t : ℝ => valueRatio t/(t:ℂ)) (nhdsWithin 0 ({0}ᶜ))
      (nhds ((2*‖carryMaterialClockCentralForcing‖^2:ℝ):ℂ)) := by
  have h := value_ratio_origin_derivative.tendsto_slope
  change Tendsto (fun t : ℝ => slope valueRatio 0 t) _ _ at h
  simpa only [slope_def_module, value_ratio_origin, sub_zero, Complex.real_smul,
    Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using h

theorem value_ratio_positive_near :
    ∀ᶠ t : ℝ in nhdsWithin 0 ({0}ᶜ),
      ‖carryMaterialClockCentralForcing‖^2 < (valueRatio t/(t:ℂ)).re := by
  have hp : ‖carryMaterialClockCentralForcing‖^2 < 2*‖carryMaterialClockCentralForcing‖^2 := by
    have h := forcing_slope_pos
    linarith
  have h := Complex.continuous_re.continuousAt.tendsto.comp value_ratio_slope_tendsto
  simp only [Function.comp_def, Complex.ofReal_re] at h
  exact h.eventually (lt_mem_nhds hp)

/-- Only the first-order phase vanishes. This is NOT a proof that the
whole native observation is real, or that the two-variable kernel is PSD. -/
theorem value_ratio_phase_first_order_zero :
    Tendsto (fun t : ℝ => (valueRatio t-conj (valueRatio t))/(t:ℂ))
      (nhdsWithin 0 ({0}ᶜ)) (nhds (0:ℂ)) := by
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp value_ratio_slope_tendsto
  have hs := value_ratio_slope_tendsto.sub hc
  simpa only [Function.comp_def, map_div₀, Complex.conj_ofReal, sub_self, sub_div] using hs

/-- A genuinely off-diagonal source check, with both quadratures retained.
It is one approach to the center, not a joint confluent extension. -/
theorem retained_two_ray_tendsto :
    Tendsto (fun t : ℝ => (valueRatio (2*t)-conj (valueRatio t))/(t:ℂ))
      (nhdsWithin 0 ({0}ᶜ)) (nhds ((2*‖carryMaterialClockCentralForcing‖^2:ℝ):ℂ)) := by
  have hm : Tendsto (fun t : ℝ => 2*t) (nhdsWithin 0 ({0}ᶜ)) (nhdsWithin 0 ({0}ᶜ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh : Continuous (fun t : ℝ => (2:ℝ)*t) := continuous_const.mul continuous_id
      simpa only [mul_zero] using (hh.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) (show t ≠ 0 by simpa using ht)
  have h2 := value_ratio_slope_tendsto.comp hm
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp value_ratio_slope_tendsto
  have hs := (h2.const_mul (2:ℂ)).sub hc
  have he : (2:ℂ)*((2*‖carryMaterialClockCentralForcing‖^2:ℝ):ℂ) -
      conj ((2*‖carryMaterialClockCentralForcing‖^2:ℝ):ℂ) =
      ((2*‖carryMaterialClockCentralForcing‖^2:ℝ):ℂ) := by
    rw [Complex.conj_ofReal]
    ring
  rw [he] at hs
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by simpa using ht)
  simp only [Function.comp_def, map_div₀, Complex.conj_ofReal, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp

end
end CarryMixedGreen
