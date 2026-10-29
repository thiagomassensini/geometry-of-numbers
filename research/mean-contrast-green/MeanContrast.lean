import ResidualCrossings

namespace CarryMeanContrast
open CarryRadialGreen CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false

def meanPort (x : PhysicalPair) : PhysicalCauchySpace := (2 : ℂ)⁻¹ • (x.1+x.2)
def contrastPort (x : PhysicalPair) : PhysicalCauchySpace := x.1-x.2

theorem mean_contrast_reconstruct (x : PhysicalPair) :
    x.1=meanPort x+(2 : ℂ)⁻¹ • contrastPort x ∧
    x.2=meanPort x-(2 : ℂ)⁻¹ • contrastPort x := by
  constructor <;> dsimp [meanPort,contrastPort] <;> module

/-- The original signed form, with two independent complete inputs. -/
theorem signed_form_mean_contrast (x y : PhysicalPair) :
    physicalForm x y=(2 : ℂ)⁻¹*(inner ℂ (meanPort x) (contrastPort y)+
      inner ℂ (contrastPort x) (meanPort y)) := by
  simp only [physicalForm,meanPort,contrastPort,
    _root_.inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace),
    _root_.inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace),
    inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]
  norm_num [map_inv₀,map_ofNat]
  ring

theorem signed_energy_mean_contrast (x : PhysicalPair) :
    (physicalForm x x).re=(inner ℂ (meanPort x) (contrastPort x)).re := by
  rw [signed_form_mean_contrast]
  have h : (inner ℂ (meanPort x : CanonicalCompletedNativeChiralCauchyCarrier)
      (contrastPort x : CanonicalCompletedNativeChiralCauchyCarrier)).re=
      (inner ℂ (contrastPort x : CanonicalCompletedNativeChiralCauchyCarrier)
      (meanPort x : CanonicalCompletedNativeChiralCauchyCarrier)).re := by
    simpa only [RCLike.re_eq_complex_re] using (inner_re_symm (𝕜 := ℂ)
      (meanPort x : CanonicalCompletedNativeChiralCauchyCarrier)
      (contrastPort x : CanonicalCompletedNativeChiralCauchyCarrier))
  norm_num [Complex.mul_re,Complex.inv_re,Complex.inv_im]
  linarith

theorem equal_legs_contrast (b e : PhysicalPair) (he : e.1=e.2) :
    contrastPort (b+e)=contrastPort b := by
  dsimp [contrastPort]
  rw [he]
  abel

theorem equal_legs_mean (b e : PhysicalPair) (he : e.1=e.2) :
    meanPort (b+e)=meanPort b+e.1 := by
  dsimp [meanPort]
  rw [he]
  module

/-- Equal residual legs are reused AFTER the original full Green reconstruction. -/
theorem completed_equal_legs_mean_contrast (m : ℕ) (η : ℝ)
    (hη0 : 0<η) (hη1 : η<1) (k : ℕ) (x : ℕ →₀ ℂ)
    (hreg : numeratorRegular η k x) :
    contrastPort (pairPower m (completedSource k x))=
      contrastPort (reconstructedBulk m η k x) ∧
    meanPort (pairPower m (completedSource k x))=
      meanPort (reconstructedBulk m η k x)+(reconstructedResidual m η k x).1 := by
  rw [refined_source_green_split m η hη0 hη1 k x]
  exact ⟨equal_legs_contrast _ _ (reconstructed_residual_equal_legs m η k x hreg),
    equal_legs_mean _ _ (reconstructed_residual_equal_legs m η k x hreg)⟩

theorem mean_power (m : ℕ) (x : PhysicalPair) :
    meanPort (pairPower m x)=powerIsometry m (meanPort x) := by
  simp only [meanPort,pairPower,LinearMap.coe_mk,AddHom.coe_mk,map_smul,map_add]

theorem contrast_power (m : ℕ) (x : PhysicalPair) :
    contrastPort (pairPower m x)=powerIsometry m (contrastPort x) := by
  simp only [contrastPort,pairPower,LinearMap.coe_mk,AddHom.coe_mk,map_sub]

/-- Necessary even for a real symmetric operator with a restricted domain
containing both means. Linearity and positivity are not needed for this test. -/
theorem symmetric_alignment_necessary (T : PhysicalCauchySpace → PhysicalCauchySpace)
    (x y : PhysicalPair)
    (hsym : (inner ℂ (T (meanPort x)) (meanPort y)).re=
      (inner ℂ (meanPort x) (T (meanPort y))).re)
    (hx : T (meanPort x)=contrastPort x) (hy : T (meanPort y)=contrastPort y) :
    (inner ℂ (meanPort x) (contrastPort y)).re=
      (inner ℂ (contrastPort x) (meanPort y)).re := by
  simpa only [hx,hy] using hsym.symm

/-- An isotropic correction changes the mean, not the contrast. No assertion
that the correction is zero or belongs to the radical is made. -/
theorem corrected_kernel_mean_contrast (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (k l i j : ℕ) :
    correctedGreenPairing η k l i j=(2 : ℂ)⁻¹*(
      inner ℂ (meanPort (pairPower l (projectiveLegs k i)))
        (contrastPort (pairPower k (projectiveLegs l j)))+
      inner ℂ (contrastPort (pairPower l (projectiveLegs k i)))
        (meanPort (pairPower k (projectiveLegs l j)))) := by
  rw [corrected_green_pairing_is_common η hη0 hη1]
  exact signed_form_mean_contrast _ _

end
end CarryMeanContrast
