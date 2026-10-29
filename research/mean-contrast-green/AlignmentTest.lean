import MeanContrast

namespace CarryMeanContrast
open CarryRadialGreen CarryRadialRefinement CarryPhysicalTrace CarryCompletedTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false

abbrev nativeResponse (z : ℂ) : ℂ := completedGreenNormalizedResponse
  completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion z

theorem normalized_chiral_mean (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate z≠0) :
    (2 : ℂ)⁻¹*(completedNativeNormalizedPositiveChiralAmplitude z+
      completedNativeNormalizedPositiveChiralAmplitude z*completedNativeHermiteBiehlerChiralQuotient z)=
      (2/(Real.sqrt 2 : ℂ))*nativeResponse z := by
  have hs : (Real.sqrt 2 : ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have hm : completedNativeNormalizedPositiveChiralAmplitude z*
      completedNativeHermiteBiehlerChiralQuotient z=
      canonicalCompletedC3FullWronskianChiralNormalization z*
        completedNativeNegativeHermiteBiehlerCoordinate z := by
    unfold completedNativeNormalizedPositiveChiralAmplitude completedNativeHermiteBiehlerChiralQuotient
    field_simp [hP]
  rw [hm]
  unfold completedNativeNormalizedPositiveChiralAmplitude canonicalCompletedC3FullWronskianChiralNormalization
    completedNativePositiveHermiteBiehlerCoordinate completedNativeNegativeHermiteBiehlerCoordinate
    nativeResponse completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  field_simp [hs,hF]
  ring

theorem projective_mean_response (k j : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0) :
    meanPort (projectiveLegs k j)=
      ((2/(Real.sqrt 2 : ℂ))*nativeResponse (canonicalCompletedC3RadialTiltPoint k j)) • radialVector k j := by
  change (2 : ℂ)⁻¹ • (_ • radialVector k j+_ • radialVector k j)=_
  rw [← add_smul,smul_smul,normalized_chiral_mean _ hF hP]

theorem projective_contrast_response (k j : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0) :
    contrastPort (projectiveLegs k j)=
      ((2 : ℂ)*Complex.I/(Real.sqrt 2 : ℂ)) • radialVector k j := by
  change _ • radialVector k j-_ • radialVector k j=_
  rw [← sub_smul,normalized_chiral_gap _ hF hP]

/-- This is a necessary cross-symmetry test, not a positivity assumption. -/
def alignmentDefect (x y : PhysicalPair) : ℝ :=
  (inner ℂ (meanPort x) (contrastPort y)).re-
    (inner ℂ (contrastPort x) (meanPort y)).re

theorem alignment_defect_common_refinement (m : ℕ) (x y : PhysicalPair) :
    alignmentDefect (pairPower m x) (pairPower m y)=alignmentDefect x y := by
  rw [alignmentDefect,mean_power,contrast_power,mean_power,contrast_power,
    power_isometry_inner,power_isometry_inner]
  rfl

/-- For real response weights on the imaginary axis, the exact obstruction
is proportional to their difference. All vectors are arbitrary ORIGINAL inputs. -/
theorem weighted_alignment_defect (x y : PhysicalPair) (v w : PhysicalCauchySpace)
    (a r s : ℝ)
    (hcx : meanPort x=((a : ℂ)*Complex.I*(r : ℂ)) • v)
    (hdx : contrastPort x=((a : ℂ)*Complex.I) • v)
    (hcy : meanPort y=((a : ℂ)*Complex.I*(s : ℂ)) • w)
    (hdy : contrastPort y=((a : ℂ)*Complex.I) • w) :
    alignmentDefect x y=a^2*(r-s)*(inner ℂ v w).re := by
  rw [alignmentDefect,hcx,hdx,hcy,hdy]
  simp only [_root_.inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace),
    _root_.inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace),
    map_mul,Complex.conj_I,Complex.conj_ofReal]
  norm_num [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im]
  ring

theorem no_symmetric_alignment_of_nonzero_defect (x y : PhysicalPair)
    (hne : alignmentDefect x y≠0) :
    ¬∃ T : PhysicalCauchySpace → PhysicalCauchySpace,
      (inner ℂ (T (meanPort x)) (meanPort y)).re=
        (inner ℂ (meanPort x) (T (meanPort y))).re ∧
      T (meanPort x)=contrastPort x ∧ T (meanPort y)=contrastPort y := by
  rintro ⟨T,hs,hx,hy⟩
  apply hne
  exact sub_eq_zero.mpr (symmetric_alignment_necessary T x y hs hx hy)

/-- Covers real or complex self-adjoint operators, bounded or not, whenever
both means are in their domain. Positive T is already excluded by symmetry. -/
theorem no_symmetric_alignment_weighted (x y : PhysicalPair) (v w : PhysicalCauchySpace)
    (a r s : ℝ) (ha : a≠0) (hrs : r≠s) (hvw : (inner ℂ v w).re≠0)
    (hcx : meanPort x=((a : ℂ)*Complex.I*(r : ℂ)) • v)
    (hdx : contrastPort x=((a : ℂ)*Complex.I) • v)
    (hcy : meanPort y=((a : ℂ)*Complex.I*(s : ℂ)) • w)
    (hdy : contrastPort y=((a : ℂ)*Complex.I) • w) :
    ¬∃ T : PhysicalCauchySpace → PhysicalCauchySpace,
      (inner ℂ (T (meanPort x)) (meanPort y)).re=
        (inner ℂ (meanPort x) (T (meanPort y))).re ∧
      T (meanPort x)=contrastPort x ∧ T (meanPort y)=contrastPort y := by
  apply no_symmetric_alignment_of_nonzero_defect
  rw [weighted_alignment_defect x y v w a r s hcx hdx hcy hdy]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (sub_ne_zero.mpr hrs)) hvw

theorem radial_cross_real_ne_zero (k i j : ℕ) :
    (inner ℂ (radialVector k i) (radialVector k j)).re≠0 := by
  change (radialCrossGram k k i j).re≠0
  rw [radial_cross_gram,Complex.ofReal_re]
  apply ne_of_gt
  unfold radialMass
  positivity

/-- A source-specific conditional NO-GO. The response values and their
inequality are explicit: they are not supplied by Hankel positivity. -/
theorem no_symmetric_two_original_ports (k i j : ℕ) (r s : ℝ) (hrs : r≠s)
    (hiF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hiP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hjF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hjP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hri : nativeResponse (canonicalCompletedC3RadialTiltPoint k i)=Complex.I*(r : ℂ))
    (hrj : nativeResponse (canonicalCompletedC3RadialTiltPoint k j)=Complex.I*(s : ℂ)) :
    ¬∃ T : PhysicalCauchySpace → PhysicalCauchySpace,
      (inner ℂ (T (meanPort (projectiveLegs k i))) (meanPort (projectiveLegs k j))).re=
        (inner ℂ (meanPort (projectiveLegs k i)) (T (meanPort (projectiveLegs k j)))).re ∧
      T (meanPort (projectiveLegs k i))=contrastPort (projectiveLegs k i) ∧
      T (meanPort (projectiveLegs k j))=contrastPort (projectiveLegs k j) := by
  apply no_symmetric_alignment_weighted _ _ (radialVector k i) (radialVector k j)
    (2/Real.sqrt 2) r s (by positivity) hrs (radial_cross_real_ne_zero k i j)
  · rw [projective_mean_response k i hiF hiP,hri]
    congr 1
    push_cast
    ring
  · rw [projective_contrast_response k i hiF hiP]
    congr 1
    push_cast
    ring
  · rw [projective_mean_response k j hjF hjP,hrj]
    congr 1
    push_cast
    ring
  · rw [projective_contrast_response k j hjF hjP]
    congr 1
    push_cast
    ring

end
end CarryMeanContrast
