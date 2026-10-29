import FirstOddJet

namespace CarryFirstOddGreen
open CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre MeasureTheory Set
open scoped unitInterval ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

def successorProfile (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) : C(unitInterval,ℂ) :=
  (-((η : ℂ)^2)) • (physicalResolventCoefficient η hη0 hη1*
    (physicalResolventCoefficient η hη0 hη1*completedNativeChiralCauchyContinuousFeature 3))

theorem successor_port_toLp (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) :
    (successorPort η : CanonicalCompletedNativeChiralCauchyCarrier)=
      ContinuousMap.toLp 2 volume ℂ (successorProfile η hη0 hη1) := by
  rw [successorPort]
  simp only [Submodule.coe_smul,green_resolvent_one_original η hη0 hη1,physicalCauchyFeature_coe]
  unfold successorProfile physicalGreenResolvent completedNativeChiralCauchyFeature
  rw [intervalMultiplier_toLp,intervalMultiplier_toLp]
  exact (map_smul (ContinuousMap.toLp 2 volume ℂ) _ _).symm

theorem successor_profile_apply (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) (u : unitInterval) :
    successorProfile η hη0 hη1 u=
      ((-η^2/(1-η*(u : ℝ))^2*Real.sqrt (u : ℝ)*(u : ℝ)^3 : ℝ) : ℂ) := by
  simp only [successorProfile,physicalResolventCoefficient,
    completedNativeChiralCauchyContinuousFeature,ContinuousMap.coe_mk,
    ContinuousMap.smul_apply,ContinuousMap.mul_apply,smul_eq_mul]
  push_cast
  simp only [div_eq_mul_inv,← inv_pow]
  ring

/-- Extracted from the original TWO physical ports, not chosen from moments. -/
def oddDensity (η x : ℝ) : ℝ :=
  η*x^2*(1-x)*(2-η*x+η*x^2)/(1-η*x)^2

def oddCoefficient (η : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, oddDensity η x

theorem odd_port_overlap (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) :
    inner ℂ (physicalCauchyFeature 1-physicalCauchyFeature 0)
      (successorPort η-greenPort η)=(oddCoefficient η : ℂ) := by
  change inner ℂ ((physicalCauchyFeature 1 : CanonicalCompletedNativeChiralCauchyCarrier)-
      (physicalCauchyFeature 0 : CanonicalCompletedNativeChiralCauchyCarrier))
    ((successorPort η : CanonicalCompletedNativeChiralCauchyCarrier)-
      (greenPort η : CanonicalCompletedNativeChiralCauchyCarrier))=_
  rw [physicalCauchyFeature_coe,physicalCauchyFeature_coe,
    successor_port_toLp η hη0 hη1,green_port_toLp η hη0 hη1]
  unfold completedNativeChiralCauchyFeature
  rw [← map_sub (ContinuousMap.toLp 2 volume ℂ),← map_sub (ContinuousMap.toLp 2 volume ℂ),L2.inner_def]
  have he : (fun u : unitInterval => inner ℂ
      (ContinuousMap.toLp 2 volume ℂ (completedNativeChiralCauchyContinuousFeature 1-
        completedNativeChiralCauchyContinuousFeature 0) u)
      (ContinuousMap.toLp 2 volume ℂ (successorProfile η hη0 hη1-greenPortProfile η hη0 hη1) u)) =ᵐ[volume]
      (fun u => (oddDensity η (u : ℝ) : ℂ)) := by
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
      (completedNativeChiralCauchyContinuousFeature 1-completedNativeChiralCauchyContinuousFeature 0),
      ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
      (successorProfile η hη0 hη1-greenPortProfile η hη0 hη1)] with u hf hg
    rw [hf,hg]
    simp only [ContinuousMap.sub_apply,successor_profile_apply,green_port_profile_apply,
      completedNativeChiralCauchyContinuousFeature,ContinuousMap.coe_mk,pow_one,pow_zero,mul_one,
      RCLike.inner_apply,Complex.conj_ofReal,← Complex.ofReal_sub,← Complex.ofReal_mul]
    congr 1
    have hs : Real.sqrt (u : ℝ)*Real.sqrt (u : ℝ)=(u : ℝ) := Real.mul_self_sqrt u.property.1
    calc
      _ = (Real.sqrt (u : ℝ)*Real.sqrt (u : ℝ))*
          ((u : ℝ)-1)*(-η^2*(u : ℝ)^3-η*(2-η*(u : ℝ))*(u : ℝ))/(1-η*(u : ℝ))^2 := by ring
      _ = oddDensity η (u : ℝ) := by rw [hs]; unfold oddDensity; ring
  rw [integral_congr_ae he,integral_complex_ofReal]
  congr 1
  have hsub := integral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Icc (0 : ℝ) 1) measurableSet_Icc (oddDensity η)
  calc
    _ = ∫ u in Icc (0 : ℝ) 1, oddDensity η u := by
      simpa only [unitInterval.volume_def] using hsub
    _ = oddCoefficient η := by
      unfold oddCoefficient
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),integral_Icc_eq_integral_Ioc]

theorem overlap_difference (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) :
    portOverlap η 1-portOverlap η 0=(oddCoefficient η : ℂ) := by
  simpa [portOverlap,basisPort,inner_sub_right] using odd_port_overlap η hη0 hη1

theorem odd_density_continuousOn (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) :
    ContinuousOn (oddDensity η) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  have h : η*x<1 := lt_of_le_of_lt (mul_le_of_le_one_right hη0 hx.2) hη1
  exact pow_ne_zero 2 (by linarith)

theorem odd_density_lower (η : ℝ) (hη0 : 0≤η) (hη1 : η<1)
    (x : ℝ) (hx : x∈Icc (0 : ℝ) 1) : η*(x^2-x^3)≤oddDensity η x := by
  have ht0 : 0≤η*x := mul_nonneg hη0 hx.1
  have ht1 : η*x<1 := lt_of_le_of_lt (mul_le_of_le_one_right hη0 hx.2) hη1
  have hden : 0<(1-η*x)^2 := sq_pos_of_pos (by linarith)
  have ht2 : (η*x)^2≤η*x := by nlinarith
  have hq : 1≤(2-η*x+η*x^2)/(1-η*x)^2 := by
    apply (le_div_iff₀ hden).mpr
    have hηx2 : 0≤η*x^2 := by positivity
    nlinarith
  have hx1 : 0≤1-x := sub_nonneg.mpr hx.2
  have hw : 0≤η*x^2*(1-x) := by positivity
  have hm := mul_le_mul_of_nonneg_left hq hw
  calc
    η*(x^2-x^3)=η*x^2*(1-x)*1 := by ring
    _ ≤ η*x^2*(1-x)*((2-η*x+η*x^2)/(1-η*x)^2) := hm
    _ = oddDensity η x := by unfold oddDensity; ring

/-- A source-only positive coefficient, uniformly for every physical eta. -/
theorem odd_coefficient_lower (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) :
    η/12≤oddCoefficient η := by
  have hd : IntervalIntegrable (oddDensity η) volume (0 : ℝ) 1 :=
    (odd_density_continuousOn η hη0 hη1).intervalIntegrable_of_Icc (by norm_num)
  have hp : IntervalIntegrable (fun x : ℝ => η*(x^2-x^3)) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => η*(x^2-x^3))).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ)≤1) hp hd
    (odd_density_lower η hη0 hη1)
  have he : (∫ x in (0 : ℝ)..1, η*(x^2-x^3))=η/12 := by
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub]
    · norm_num [integral_pow]
      ring
    · exact (by fun_prop : Continuous (fun x : ℝ => x^2)).intervalIntegrable 0 1
    · exact (by fun_prop : Continuous (fun x : ℝ => x^3)).intervalIntegrable 0 1
  rwa [he] at h

theorem odd_coefficient_pos (η : ℝ) (hη0 : 0<η) (hη1 : η<1) :
    0<oddCoefficient η := lt_of_lt_of_le (by positivity) (odd_coefficient_lower η hη0.le hη1)

end
end CarryFirstOddGreen
