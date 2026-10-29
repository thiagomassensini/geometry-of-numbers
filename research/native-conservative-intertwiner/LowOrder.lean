import PR41Transport

namespace CarryConservativeIntertwiner
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre ChiralReturn
open CarryCriticalRelative CarryForcingResidual NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators lp ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

def firstEvenBoundary : Fin 2 → ℂ := ![1,0]
def firstOddBoundary : Fin 2 → ℂ := ![0,1]

theorem first_even_is_pr41 : firstEvenBoundary=nativeResidualBoundary 0 0 := by
  funext a
  fin_cases a <;> norm_num [firstEvenBoundary,nativeResidualBoundary,nativeSourceBoundaryFromParity,
    orthogonalPolynomial,residualPolynomial]

theorem first_odd_is_pr41 : firstOddBoundary=nativeResidualBoundary 1 0 := by
  funext a
  fin_cases a <;> norm_num [firstOddBoundary,nativeResidualBoundary,nativeSourceBoundaryFromParity,
    orthogonalPolynomial,residualPolynomial]

def evenLeading : PhysicalCauchySpace := amp 0 • physicalCauchyFeature 0
def oddLeading : PhysicalCauchySpace := amp 0 • (physicalCauchyFeature 1-physicalCauchyFeature 0)

theorem even_leading_exact : physicalLeading 1 0 firstEvenBoundary (by norm_num)=evenLeading := by
  apply Subtype.ext
  rw [physicalLeading_coe]
  simp [leadingState,leadingCoefficients,firstEvenBoundary,radialIncidentSynthesis,
    nativeSourceJetOrderPhase,completedGreenForwardWeight,completedNativeRadialChiralCauchyState,
    Fin.sum_univ_two,evenLeading,physicalCauchyFeature_coe]

theorem odd_leading_exact : physicalLeading 1 1 firstOddBoundary (by norm_num)=oddLeading := by
  apply Subtype.ext
  rw [physicalLeading_coe]
  simp [leadingState,leadingCoefficients,firstOddBoundary,radialIncidentSynthesis,
    nativeSourceJetOrderPhase,completedGreenForwardWeight,completedNativeRadialChiralCauchyState,
    Fin.sum_univ_two,oddLeading,physicalCauchyFeature_coe,smul_sub]
  abel

theorem even_support (a : Fin 2) (ha : 0<a.val) : firstEvenBoundary a=0 := by
  fin_cases a
  · simp at ha
  · rfl

theorem first_incident_ray (k : ℕ) : physicalIncident 1 k firstEvenBoundary=
    ((Real.sqrt ((k:ℝ)+1):ℂ)*amp (canonicalCompletedC3RadialTiltPoint k 0)) • physicalCauchyFeature 0 := by
  apply Subtype.ext
  rw [physicalIncident_coe,nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource]
  simp [nativeSourceChiralJetInput,nativeSourceChiralJetInputMatrix,
    firstEvenBoundary,radialIncidentSynthesis,nativeSourceJetOrderPhase,
    completedGreenForwardWeight,completedNativeRadialChiralCauchyState,
    physicalCauchyFeature_coe,amp,mul_comm]
  module

/-- The constant is inherited from the completed amplitude; not fitted. -/
theorem central_amp_norm : ‖amp 0‖^2=(1:ℝ)/2 := by
  have he : amp 0=Complex.I*(Real.sqrt 2:ℂ)⁻¹ := by
    change canonicalCompletedC3FullWronskianChiralNormalization 0*
      completedNativePositiveHermiteBiehlerCoordinate 0=_
    rw [completedNativePositiveHermiteBiehlerCoordinate_zero]
    unfold canonicalCompletedC3FullWronskianChiralNormalization
    field_simp [completedNativeOperatorCharacteristic_zero_ne_zero]
  rw [he,norm_mul,Complex.norm_I,one_mul,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  norm_num

theorem physical_feature_inner (i j : ℕ) :
    inner ℂ (physicalCauchyFeature i) (physicalCauchyFeature j)=(((i+j+2:ℕ):ℝ)⁻¹:ℂ) := by
  rw [Submodule.coe_inner,physicalCauchyFeature_coe,physicalCauchyFeature_coe]
  exact inner_completedNativeChiralCauchyFeature i j

theorem evenLeading_norm : ‖evenLeading‖^2=(1:ℝ)/4 := by
  have hf : ‖physicalCauchyFeature 0‖^2=(1:ℝ)/2 := by
    calc
      ‖physicalCauchyFeature 0‖^2 =
          (inner ℂ (physicalCauchyFeature 0) (physicalCauchyFeature 0)).re :=
        norm_sq_eq_re_inner (𝕜:=ℂ) (physicalCauchyFeature 0)
      _ = (((((0+0+2:ℕ):ℝ)⁻¹):ℂ)).re :=
        congrArg Complex.re (physical_feature_inner 0 0)
      _ = (1:ℝ)/2 := by norm_num

  rw [evenLeading,norm_smul,mul_pow,central_amp_norm,hf]
  norm_num

/-- Rational finite regression of the actual leading source and candidate. -/
theorem even_leading_defect_energy : ‖leadingTransportDefect 0 evenLeading‖^2=(1:ℝ)/9 := by
  have he : leadingTransportDefect 0 evenLeading=(-2/3:ℂ) • evenLeading := by
    simp only [leadingTransportDefect,evenLeading,map_smul,physicalCauchyShift_feature,rho]
    norm_num
    module
  rw [he,norm_smul,mul_pow,evenLeading_norm]
  norm_num

theorem even_leading_head_energy : ‖conservativeHead 0 evenLeading‖^2=(2:ℝ)/9 := by
  have he : conservativeReturn 0 evenLeading=(-1/3:ℂ) • evenLeading := by
    simp only [conservativeReturn,neg_apply,evenLeading,map_smul,physicalCauchyShift_feature,rho]
    norm_num
    module
  have hh := conservative_energy 0 evenLeading
  rw [he,norm_smul,mul_pow,evenLeading_norm] at hh
  norm_num at hh
  linarith

theorem even_leading_cross : 2*(inner ℂ (conservativeReturn 0 evenLeading)
    (leadingTransportDefect 0 evenLeading)).re=(1:ℝ)/9 := by
  have he := leading_conservative_cancellation 0 evenLeading
  rw [even_leading_head_energy,even_leading_defect_energy] at he
  linarith

/-- Both original Cauchy columns and their cross, in the inherited metric. -/
theorem two_column_energy (a b : ℝ) :
    ‖(a:ℂ) • physicalCauchyFeature 0+(b:ℂ) • physicalCauchyFeature 1‖^2=
      a^2/2+2*a*b/3+b^2/4 := by
  calc
    _ = (inner ℂ ((a:ℂ) • physicalCauchyFeature 0+(b:ℂ) • physicalCauchyFeature 1)
        ((a:ℂ) • physicalCauchyFeature 0+(b:ℂ) • physicalCauchyFeature 1)).re :=
      norm_sq_eq_re_inner (𝕜:=ℂ) _
    _ = _ := by
      rw [Submodule.coe_inner]
      simp only [Submodule.coe_add,Submodule.coe_smul,physicalCauchyFeature_coe]
      simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
        inner_completedNativeChiralCauchyFeature]
      simp
      ring

theorem oddLeading_norm : ‖oddLeading‖^2=(1:ℝ)/24 := by
  have he : oddLeading=amp 0 • (((-1:ℝ):ℂ) • physicalCauchyFeature 0+
      ((1:ℝ):ℂ) • physicalCauchyFeature 1) := by
    unfold oddLeading
    module
  rw [he,norm_smul,mul_pow,central_amp_norm,two_column_energy]
  norm_num

theorem odd_leading_defect_energy : ‖leadingTransportDefect 0 oddLeading‖^2=(19:ℝ)/450 := by
  have he : leadingTransportDefect 0 oddLeading=amp 0 •
      (((2/3:ℝ):ℂ) • physicalCauchyFeature 0+((-2/5:ℝ):ℂ) • physicalCauchyFeature 1) := by
    simp only [leadingTransportDefect,oddLeading,map_smul,map_sub,physicalCauchyShift_feature,rho]
    norm_num
    module
  rw [he,norm_smul,mul_pow,central_amp_norm,two_column_energy]
  norm_num

theorem odd_leading_head_energy : ‖conservativeHead 0 oddLeading‖^2=(8:ℝ)/225 := by
  have he : conservativeReturn 0 oddLeading=amp 0 •
      (((1/3:ℝ):ℂ) • physicalCauchyFeature 0+((-3/5:ℝ):ℂ) • physicalCauchyFeature 1) := by
    simp only [conservativeReturn,neg_apply,oddLeading,map_smul,map_sub,physicalCauchyShift_feature,rho]
    norm_num
    module
  have hh := conservative_energy 0 oddLeading
  rw [he,norm_smul,mul_pow,central_amp_norm,two_column_energy,oddLeading_norm] at hh
  norm_num at hh
  linarith

/-- The mixed term has the opposite sign to the first even regression. -/
theorem odd_leading_cross : 2*(inner ℂ (conservativeReturn 0 oddLeading)
    (leadingTransportDefect 0 oddLeading)).re=-(1:ℝ)/150 := by
  have he := leading_conservative_cancellation 0 oddLeading
  rw [odd_leading_head_energy,odd_leading_defect_energy] at he
  linarith

end
end CarryConservativeIntertwiner
