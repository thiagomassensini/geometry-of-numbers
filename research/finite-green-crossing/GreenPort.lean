import GreenIntertwiner
import GreenBudget

namespace CarryFiniteGreen
open CarryRadialGreen CarryMeanContrast CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre MeasureTheory Set
open scoped unitInterval ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The literal old Green resolvent applied to the surviving residual port.
It is not defined from a moment or a target scalar pairing. -/
def greenPort (η : ℝ) : PhysicalCauchySpace :=
  (η : ℂ) • greenResolvent 1 η (greenResolvent 1 η
    ((2 : ℂ) • physicalCauchyFeature 1-(η : ℂ) • nativeAdvance (physicalCauchyFeature 1)))

def greenPortProfile (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) : C(unitInterval,ℂ) :=
  (η : ℂ) • (physicalResolventCoefficient η hη0 hη1*
    (physicalResolventCoefficient η hη0 hη1*
      ((2 : ℂ) • completedNativeChiralCauchyContinuousFeature 1-
       (η : ℂ) • completedNativeChiralCauchyContinuousFeature 2)))

/-- Identification in the original physical Lp, before pairing. -/
theorem green_port_toLp (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) :
    (greenPort η : CanonicalCompletedNativeChiralCauchyCarrier)=
      ContinuousMap.toLp 2 volume ℂ (greenPortProfile η hη0 hη1) := by
  rw [greenPort,native_advance_feature]
  simp only [Submodule.coe_smul,green_resolvent_one_original η hη0 hη1,
    Submodule.coe_sub,physicalCauchyFeature_coe]
  unfold greenPortProfile physicalGreenResolvent completedNativeChiralCauchyFeature
  rw [← map_smul (ContinuousMap.toLp 2 volume ℂ),
    ← map_smul (ContinuousMap.toLp 2 volume ℂ),
    ← map_sub (ContinuousMap.toLp 2 volume ℂ)]
  rw [intervalMultiplier_toLp,intervalMultiplier_toLp]
  exact (map_smul (ContinuousMap.toLp 2 volume ℂ) _ _).symm

/-- The pointwise expression is derived from the actual inverse multiplier. -/
theorem green_port_profile_apply (η : ℝ) (hη0 : 0≤η) (hη1 : η<1)
    (u : unitInterval) :
    greenPortProfile η hη0 hη1 u=
      ((η*(2-η*(u : ℝ))/(1-η*(u : ℝ))^2*Real.sqrt (u : ℝ)*(u : ℝ) : ℝ) : ℂ) := by
  simp only [greenPortProfile,physicalResolventCoefficient,
    completedNativeChiralCauchyContinuousFeature,ContinuousMap.coe_mk,
    ContinuousMap.smul_apply,ContinuousMap.mul_apply,ContinuousMap.sub_apply,
    smul_eq_mul,pow_one]
  push_cast
  simp only [div_eq_mul_inv,← inv_pow]
  ring

/-- The mixed coefficient J is now an overlap of the ORIGINAL physical
column and the ORIGINAL corrected Green port, not a fitted integral. -/
theorem green_port_inner (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) :
    inner ℂ (physicalCauchyFeature 0) (greenPort η)=(greenBudget η : ℂ) := by
  change inner ℂ (physicalCauchyFeature 0 : CanonicalCompletedNativeChiralCauchyCarrier)
    (greenPort η : CanonicalCompletedNativeChiralCauchyCarrier)=_
  rw [physicalCauchyFeature_coe,green_port_toLp η hη0 hη1,L2.inner_def]
  have he : (fun u : unitInterval => inner ℂ
      (completedNativeChiralCauchyFeature 0 u)
      (ContinuousMap.toLp 2 volume ℂ (greenPortProfile η hη0 hη1) u)) =ᵐ[volume]
      (fun u => (greenDensity η (u : ℝ) : ℂ)) := by
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
      (completedNativeChiralCauchyContinuousFeature 0),
      ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
      (greenPortProfile η hη0 hη1)] with u hf hg
    change inner ℂ (ContinuousMap.toLp 2 volume ℂ
      (completedNativeChiralCauchyContinuousFeature 0) u) _=_
    rw [hf,hg,green_port_profile_apply]
    simp only [completedNativeChiralCauchyContinuousFeature,ContinuousMap.coe_mk,
      pow_zero,mul_one,RCLike.inner_apply,Complex.conj_ofReal,← Complex.ofReal_mul]
    congr 1
    have hs : Real.sqrt (u : ℝ)*Real.sqrt (u : ℝ)=(u : ℝ) := Real.mul_self_sqrt u.property.1
    calc
      _ = (η*(2-η*(u : ℝ))/(1-η*(u : ℝ))^2)*(u : ℝ)*
        (Real.sqrt (u : ℝ)*Real.sqrt (u : ℝ)) := by ring
      _ = greenDensity η (u : ℝ) := by rw [hs]; unfold greenDensity; ring
  rw [integral_congr_ae he,integral_complex_ofReal]
  congr 1
  have hsub := integral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Icc (0 : ℝ) 1) measurableSet_Icc (greenDensity η)
  calc
    _ = ∫ u in Icc (0 : ℝ) 1, greenDensity η u := by
      simpa only [unitInterval.volume_def] using hsub
    _ = greenBudget η := by
      unfold greenBudget
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),integral_Icc_eq_integral_Ioc]

end
end CarryFiniteGreen
