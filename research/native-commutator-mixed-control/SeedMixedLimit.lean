import GreenSeed
import CarrySelfAdjointOperator.CompletedNativeCentralProductDressingAudit

namespace CarryCommutatorControl
open CarrySelfAdjointOperator CarryNativeTfvd NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- A reused finite source coefficient; it does not define a physical state. -/
theorem incident_amplitude_hasDerivAt_h0 :
    HasDerivAt completedNativeNormalizedPositiveChiralAmplitude
      (2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) / (Real.sqrt 2 : ℂ)) 0 := by
  have h := (((completedNativeGreenNormalizedResponse_hasDerivAt_h0.const_mul (2 : ℂ)).add_const
    Complex.I).div_const (Real.sqrt 2 : ℂ))
  apply h.congr_of_eventuallyEq
  filter_upwards [completedNativeChiralPickFactorization_eventually_regular] with z hz
  exact incident_amplitude_response z hz.2.1

private theorem radial_punctured_zero :
    Tendsto (fun k => canonicalCompletedC3RadialTiltPoint k 0)
      atTop (nhdsWithin 0 ({0} : Set ℂ)ᶜ) :=
  tendsto_nhdsWithin_iff.mpr
    ⟨canonicalCompletedC3RadialTiltPoint_tendsto_zero 0,
      Filter.Eventually.of_forall fun k => by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
          (fun h : canonicalCompletedC3RadialTiltPoint k 0=0 =>
            canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0 (by rw [h]; rfl))⟩

/-- Exact scale of the first ORIGINAL amplitude difference. -/
theorem incident_amplitude_step_tendsto :
    Tendsto (fun k : ℕ => ((((k : ℝ)+1) : ℂ) * (incidentWeight k 0-incidentWeight k 1)))
      atTop (nhds (-Complex.I *
        (2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) / (Real.sqrt 2 : ℂ)))) := by
  let a := 2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) / (Real.sqrt 2 : ℂ)
  have hA := incident_amplitude_hasDerivAt_h0
  have hA2 : HasDerivAt completedNativeNormalizedPositiveChiralAmplitude a ((2 : ℂ)*0) := by
    simpa [a] using hA
  have hd := (hA2.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul 2)).sub hA
  have hs := hd.tendsto_slope.comp radial_punctured_zero
  have ht := (tendsto_const_nhds (x := -Complex.I)).mul hs
  convert ht using 1
  · funext k
    simp only [Function.comp_def, Pi.sub_apply, slope_def_field, mul_zero, sub_self, sub_zero]
    have hp : (2 : ℂ)*canonicalCompletedC3RadialTiltPoint k 0 =
        canonicalCompletedC3RadialTiltPoint k 1 := by simp [canonicalCompletedC3RadialTiltPoint]
    rw [hp]
    unfold incidentWeight canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep
      canonicalGreenJetStep
    push_cast
    have hk : (k : ℂ)+1 ≠ 0 := by exact_mod_cast (show (k : ℝ)+1 ≠ 0 by positivity)
    field_simp [hk, Complex.I_ne_zero]
    ring
  · dsimp [a]
    congr 1
    ring

private theorem chiral_tangent_product (eta h : ℝ) :
    (eta : ℂ) * conj chiralDifference *
      (-Complex.I * (2 * (h : ℂ) / (Real.sqrt 2 : ℂ))) = ((-2 * eta * h : ℝ) : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hsn : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold chiralDifference
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  field_simp [hsn]
  linear_combination (eta : ℂ) * (h : ℂ) * hs +
    2 * (eta : ℂ) * (h : ℂ) * Complex.I_sq

/-- The actual complete mixed correction has a finite signed limit. -/
theorem seed_mixed_tendsto (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    Tendsto (seedMixed eta h0 h1) atTop
      (nhds (-2 * eta * canonicalCompletedNativeLogDerivativeMoment 0 *
        (inner ℂ (completedNativeChiralCauchyFeature 0)
          (physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1))).re)) := by
  let J := inner ℂ (completedNativeChiralCauchyFeature 0)
    (physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1))
  have hcomplex := ((tendsto_const_nhds (x := (eta : ℂ)*conj chiralDifference)).mul
    incident_amplitude_step_tendsto).mul_const J
  have ht := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  have hl : (((eta : ℂ)*conj chiralDifference)*
      (-Complex.I * (2*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)/(Real.sqrt 2 : ℂ)))*J).re =
      -2*eta*canonicalCompletedNativeLogDerivativeMoment 0*J.re := by
    rw [chiral_tangent_product]
    simp [Complex.mul_re]
  rw [hl] at ht
  apply ht.congr'
  filter_upwards [radial_weight_difference_eventually 2] with k hk
  rw [seed_mixed_exact eta h0 h1 k hk]
  dsimp [J]
  congr 1
  ring

/-- The sign is obtained from the already proved h0>0 only for this finite seed. -/
theorem seed_mixed_eventually_negative (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    ∀ᶠ k : ℕ in atTop, seedMixed eta h0 h1 k < 0 := by
  have hJ := green_seed_cross_re_pos eta h0 h1
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hn : -2*eta*canonicalCompletedNativeLogDerivativeMoment 0 *
      (inner ℂ (completedNativeChiralCauchyFeature 0)
        (physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1))).re < 0 := by
    have hp := mul_pos (mul_pos h0 hh) hJ
    nlinarith
  exact (seed_mixed_tendsto eta h0 h1).eventually (eventually_lt_nhds hn)

theorem seed_commutator_eventually_nonzero (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    ∀ᶠ k : ℕ in atTop, completedSourceParts eta h0 h1 k (Finsupp.single 0 1) 2 ≠ 0 := by
  filter_upwards [seed_mixed_eventually_negative eta h0 h1] with k hk
  intro hz
  simp [seedMixed, hz, canonicalCompletedNativeProjectiveChiralForm] at hk

end
end CarryCommutatorControl
