import PowerRefinement
import CrossRadialGeometry

namespace CarryRadialRefinement
open CarryPhysicalTrace CarryCompletedTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Existing radial vector, only codomain-restricted to its original closure. -/
def radialVector (k j : ℕ) : PhysicalCauchySpace :=
  ⟨completedNativeRadialChiralCauchyState k j,radialCauchyState_mem k j⟩

theorem radial_vector_feature (k j : ℕ) : radialVector k j =
    (Real.sqrt ((k : ℝ)+1) : ℂ) • physicalCauchyFeature j := by
  apply Subtype.ext
  simp only [radialVector,Submodule.coe_smul,physicalCauchyFeature_coe]
  rfl

theorem refined_mass (m k : ℕ) : (refinedAddress m k : ℝ)+1 =
    ((m : ℝ)+1)*((k : ℝ)+1) := by
  unfold refinedAddress
  push_cast
  ring

theorem refined_point (m k j : ℕ) :
    canonicalCompletedC3RadialTiltPoint (refinedAddress m k) (refinedAddress m j) =
      canonicalCompletedC3RadialTiltPoint k j := by
  rw [canonicalCompletedC3RadialTiltPoint_eq_I_mul_im (refinedAddress m k) (refinedAddress m j),
    canonicalCompletedC3RadialTiltPoint_eq_I_mul_im k j,
    canonicalCompletedC3RadialTiltPoint_im,canonicalCompletedC3RadialTiltPoint_im,
    refined_mass,refined_mass]
  congr 2
  field_simp

theorem power_isometry_radial (m k j : ℕ) :
    powerIsometry m (radialVector k j) =
      radialVector (refinedAddress m k) (refinedAddress m j) := by
  rw [radial_vector_feature,map_smul,power_isometry_feature,powerColumn,
    radial_vector_feature,refined_mass,Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (m : ℝ)+1)]
  simp only [smul_smul]
  congr 1
  push_cast
  ring

/-- Every original coefficient, phase and channel is carried unchanged;
only the address is refined. This applies simultaneously to all six fields. -/
theorem power_isometry_finite_source (m k : ℕ) {N : ℕ} (a : Fin N → ℂ) :
    powerIsometry m (∑ j, a j • radialVector k j) =
      ∑ j, a j • radialVector (refinedAddress m k) (refinedAddress m j) := by
  simp only [map_sum,map_smul,power_isometry_radial]

/-- The native completed projective state, in the SAME physical closure. -/
def projectiveLegs (k j : ℕ) : PhysicalCauchySpace × PhysicalCauchySpace :=
  (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k j) • radialVector k j,
   (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k j)*
    completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)) • radialVector k j)

theorem projective_legs_original (k j : ℕ) :
    ((projectiveLegs k j).1.val,(projectiveLegs k j).2.val) =
      canonicalCompletedNativeRadialProjectiveChiralState k j := by
  simp [projectiveLegs,radialVector,
    canonicalCompletedNativeRadialProjectiveChiralState,
    canonicalCompletedNativeRadialChiralDefectState,
    completedNativeRadialChiralMultiplierState,smul_smul]

def pairPower (m : ℕ) :
    (PhysicalCauchySpace × PhysicalCauchySpace) →ₗ[ℂ] (PhysicalCauchySpace × PhysicalCauchySpace) where
  toFun u := (powerIsometry m u.1,powerIsometry m u.2)
  map_add' u v := by apply Prod.ext <;> simp
  map_smul' c u := by apply Prod.ext <;> simp

/-- The SAME isometry transports BOTH channels, including the full completed
amplitude and return. Equality of spectral nodes is proved, not postulated. -/
theorem pair_power_refines_projective (m k j : ℕ) :
    pairPower m (projectiveLegs k j) =
      projectiveLegs (refinedAddress m k) (refinedAddress m j) := by
  apply Prod.ext <;> simp [pairPower,projectiveLegs,power_isometry_radial,refined_point]

def commonGrade (k l : ℕ) : ℕ := refinedAddress l k

theorem common_grade_comm (k l : ℕ) : commonGrade k l = commonGrade l k := by
  unfold commonGrade refinedAddress
  ring

theorem refined_address_comp (m n j : ℕ) :
    refinedAddress m (refinedAddress n j) = refinedAddress (refinedAddress m n) j := by
  unfold refinedAddress
  ring

/-- The actual common-refinement map acts in the original carrier. -/
def commonPairing (k l i j : ℕ) : ℂ :=
  (2 : ℂ)⁻¹ *
    (inner ℂ (pairPower l (projectiveLegs k i)).1 (pairPower k (projectiveLegs l j)).1 -
     inner ℂ (pairPower l (projectiveLegs k i)).2 (pairPower k (projectiveLegs l j)).2)

/-- It is an old single-grid pairing at sparse original addresses. -/
theorem common_pairing_same_grade (k l i j : ℕ) : commonPairing k l i j =
    canonicalCompletedNativeProjectiveChiralForm
      (canonicalCompletedNativeRadialProjectiveChiralState (commonGrade k l) (refinedAddress l i))
      (canonicalCompletedNativeRadialProjectiveChiralState (commonGrade k l) (refinedAddress k j)) := by
  change canonicalCompletedNativeProjectiveChiralForm
    (((pairPower l (projectiveLegs k i)).1.val),((pairPower l (projectiveLegs k i)).2.val))
    (((pairPower k (projectiveLegs l j)).1.val),((pairPower k (projectiveLegs l j)).2.val)) = _
  rw [pair_power_refines_projective,pair_power_refines_projective,
    projective_legs_original,projective_legs_original]
  change canonicalCompletedNativeProjectiveChiralForm
    (canonicalCompletedNativeRadialProjectiveChiralState (commonGrade k l) (refinedAddress l i))
    (canonicalCompletedNativeRadialProjectiveChiralState (commonGrade l k) (refinedAddress k j)) = _
  rw [common_grade_comm l k]

/-- Further COMMON refinement preserves all ordered crosses exactly. -/
theorem further_refinement_pairing (m : ℕ)
    (u v : PhysicalCauchySpace × PhysicalCauchySpace) :
    (2 : ℂ)⁻¹ * (inner ℂ (pairPower m u).1 (pairPower m v).1 -
      inner ℂ (pairPower m u).2 (pairPower m v).2) =
    (2 : ℂ)⁻¹ * (inner ℂ u.1 v.1-inner ℂ u.2 v.2) := by
  change (2 : ℂ)⁻¹ *
    (inner ℂ (powerIsometry m u.1) (powerIsometry m v.1) -
      inner ℂ (powerIsometry m u.2) (powerIsometry m v.2)) = _
  rw [power_isometry_inner,power_isometry_inner]

end
end CarryRadialRefinement
