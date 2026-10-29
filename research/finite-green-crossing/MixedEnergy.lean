import ZeroResidual

namespace CarryFiniteGreen
open CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Only the pre-existing chiral normalization and radial mass coefficient. -/
def chiralRadialScale (k : ℕ) : ℂ :=
  (2/(Real.sqrt 2 : ℂ))*(Real.sqrt ((k : ℝ)+1) : ℂ)

theorem residual_scale_eq (k : ℕ) : residualScale k=chiralRadialScale k*responseIncrement k := by
  unfold residualScale chiralRadialScale
  ring

theorem chiral_scale_norm_product (k : ℕ) :
    conj (chiralRadialScale k)*chiralRadialScale k=2*((k : ℂ)+1) := by
  have hs : (Real.sqrt 2 : ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have hs2 : (Real.sqrt 2 : ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have hk2 : (Real.sqrt ((k : ℝ)+1) : ℂ)^2=(k : ℂ)+1 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ)≤(k : ℝ)+1 by positivity)
  unfold chiralRadialScale
  simp only [map_mul,map_div₀,Complex.conj_ofReal,map_ofNat]
  calc
    _ = 4*(Real.sqrt ((k : ℝ)+1) : ℂ)^2/(Real.sqrt 2 : ℂ)^2 := by field_simp [hs]; ring
    _ = _ := by rw [hs2,hk2]; ring

theorem chiral_scaled_inner (k : ℕ) (a b : ℂ) (v w : PhysicalCauchySpace) :
    inner ℂ ((chiralRadialScale k*a) • v) ((chiralRadialScale k*b) • w)=
      (2*((k : ℂ)+1))*conj a*b*inner ℂ v w := by
  rw [_root_.inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace),
    _root_.inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace)]
  simp only [map_mul]
  calc
    _ = (conj (chiralRadialScale k)*chiralRadialScale k)*conj a*b*inner ℂ v w := by ring
    _ = _ := by rw [chiral_scale_norm_product]

theorem initial_source : ∀ k, completedSource k initialInput=projectiveLegs k 0 := by
  intro k
  simp [completedSource,initialInput]

theorem initial_mean (k : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0) :
    meanPort (projectiveLegs k 0)=(chiralRadialScale k*
      nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)) • physicalCauchyFeature 0 := by
  rw [projective_mean_response k 0 hF hP,radial_vector_feature,smul_smul]
  congr 1
  unfold chiralRadialScale
  ring

theorem initial_contrast (k : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0) :
    contrastPort (projectiveLegs k 0)=(chiralRadialScale k*Complex.I) • physicalCauchyFeature 0 := by
  rw [projective_contrast_response k 0 hF hP,radial_vector_feature,smul_smul]
  congr 1
  unfold chiralRadialScale
  ring

theorem initial_source_energy (k : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0) :
    (physicalForm (projectiveLegs k 0) (projectiveLegs k 0)).re=
      ((k : ℝ)+1)*(nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)).im := by
  rw [signed_energy_mean_contrast,initial_mean k hF hP,initial_contrast k hF hP,
    chiral_scaled_inner,physical_column_inner]
  norm_num [Complex.mul_re,Complex.mul_im]
  ring

theorem physical_form_equal_right (x : PhysicalPair) (e : PhysicalCauchySpace) :
    physicalForm x (e,e)=(2 : ℂ)⁻¹*inner ℂ (contrastPort x) e := by
  simp only [physicalForm,contrastPort,inner_sub_left]

theorem initial_green_split (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) :
    projectiveLegs k 0=reconstructedBulk 0 η k initialInput+
      reconstructedResidual 0 η k initialInput := by
  have h := refined_source_green_split 0 η hη0 hη1 k initialInput
  rwa [pair_power_zero,initial_source] at h

theorem initial_residual_self (η : ℝ) (k : ℕ)
    (hF0 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP0 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hF1 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1)≠0)
    (hP1 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 1)≠0) :
    physicalForm (reconstructedResidual 0 η k initialInput)
      (reconstructedResidual 0 η k initialInput)=0 := by
  rw [reconstructed_residual_initial η k hF0 hP0 hF1 hP1]
  simp only [physicalForm,sub_self,mul_zero]

/-- Exact complex mixed crossing of the original source and original Green
residual at FINITE radial grade; no imaginary-axis reality is assumed. -/
theorem initial_source_residual_pairing (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) (k : ℕ)
    (hF0 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP0 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hF1 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1)≠0)
    (hP1 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 1)≠0) :
    physicalForm (projectiveLegs k 0) (reconstructedResidual 0 η k initialInput)=
      -Complex.I*((k : ℂ)+1)*responseIncrement k*(greenBudget η : ℂ) := by
  rw [reconstructed_residual_initial η k hF0 hP0 hF1 hP1,physical_form_equal_right,
    initial_contrast k hF0 hP0,residual_scale_eq,chiral_scaled_inner,green_port_inner η hη0 hη1]
  simp only [Complex.conj_I]
  ring

theorem initial_mixed_pairing (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ)
    (hF0 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP0 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hF1 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1)≠0)
    (hP1 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 1)≠0) :
    physicalForm (reconstructedBulk 0 η k initialInput) (reconstructedResidual 0 η k initialInput)=
      -Complex.I*((k : ℂ)+1)*responseIncrement k*(greenBudget η : ℂ) := by
  have he := initial_source_residual_pairing η hη0.le hη1 k hF0 hP0 hF1 hP1
  rw [initial_green_split η hη0 hη1 k] at he
  have hadd (a b e : PhysicalPair) : physicalForm (a+b) e=physicalForm a e+physicalForm b e := by
    simp only [physicalForm,Prod.fst_add,Prod.snd_add,inner_add_left]
    ring
  rw [hadd,initial_residual_self η k hF0 hP0 hF1 hP1,add_zero] at he
  exact he

theorem initial_mixed_real (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ)
    (hF0 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP0 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hF1 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1)≠0)
    (hP1 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 1)≠0) :
    (physicalForm (reconstructedBulk 0 η k initialInput) (reconstructedResidual 0 η k initialInput)).re=
      ((k : ℝ)+1)*(responseIncrement k).im*greenBudget η := by
  rw [initial_mixed_pairing η hη0 hη1 k hF0 hP0 hF1 hP1]
  norm_num [Complex.mul_re,Complex.mul_im]

theorem initial_bulk_real (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ)
    (hF0 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP0 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hF1 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1)≠0)
    (hP1 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 1)≠0) :
    (physicalForm (reconstructedBulk 0 η k initialInput) (reconstructedBulk 0 η k initialInput)).re=
      ((k : ℝ)+1)*(nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)).im-
        2*(((k : ℝ)+1)*(responseIncrement k).im*greenBudget η) := by
  have h := congrArg Complex.re (physical_form_four_sectors
    (reconstructedBulk 0 η k initialInput) (reconstructedResidual 0 η k initialInput)
    (reconstructedBulk 0 η k initialInput) (reconstructedResidual 0 η k initialInput))
  simp only [← initial_green_split η hη0 hη1 k,
    initial_residual_self η k hF0 hP0 hF1 hP1,Complex.add_re,Complex.zero_re] at h
  rw [initial_source_energy k hF0 hP0,
    physical_form_re_symm (reconstructedResidual 0 η k initialInput) (reconstructedBulk 0 η k initialInput),
    initial_mixed_real η hη0 hη1 k hF0 hP0 hF1 hP1] at h
  linarith

end
end CarryFiniteGreen
