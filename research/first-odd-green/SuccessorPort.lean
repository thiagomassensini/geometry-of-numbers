import MixedEnergy

namespace CarryFirstOddGreen
open CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

def basisInput (j : ℕ) : ℕ →₀ ℂ := Finsupp.single j 1

def increment (k j : ℕ) : ℂ :=
  nativeResponse (canonicalCompletedC3RadialTiltPoint k (j+1))-
    nativeResponse (canonicalCompletedC3RadialTiltPoint k j)

theorem basis_shift (j : ℕ) : coefficientShift (basisInput j)=basisInput (j+1) := by
  simp [basisInput,coefficientShift,Finsupp.mapDomain_single]

theorem source_basis (k j : ℕ) : completedSource k (basisInput j)=projectiveLegs k j := by
  simp [completedSource,basisInput]

theorem residual_add (k : ℕ) (x y : ℕ →₀ ℂ) :
    completedResidual k (x+y)=completedResidual k x+completedResidual k y := by
  simp only [completedResidual,map_add]
  module

theorem successor_bulk (η : ℝ) : finiteTfvdBulk η (basisInput 1)=
    (-2 : ℂ) • basisInput 1+(η : ℂ) • basisInput 2 := by
  ext j
  cases j with
  | zero => simp [finiteTfvdBulk_zero,basisInput]
  | succ j =>
    rw [finiteTfvdBulk_succ]
    cases j with
    | zero => simp [basisInput]
    | succ j =>
      cases j with
      | zero => simp [basisInput]
      | succ j => simp [basisInput,Nat.add_assoc]

/-- The missing zeroth coefficient is a boundary condition. No eta^-1 e0
is inserted into this bulk stencil. -/
theorem successor_residual_numerator (η : ℝ) (k : ℕ) :
    residualNumerator η k (basisInput 1)=
      -(η : ℂ) • pairAdvance (completedResidual k (basisInput 1)) := by
  rw [residualNumerator,successor_bulk,basis_shift,residual_add,
    completed_residual_smul,completed_residual_smul]
  module

theorem basis_regular (k j : ℕ)
    (hreg : ∀ i ∈ ({j,j+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    sourceRegular k (basisInput j) := by
  intro a ha i hi
  have he : a=j := by simpa [basisInput] using ha
  subst a
  exact hreg i hi

/-- Original residual for an arbitrary basis address, with BOTH legs. -/
theorem residual_basis_pair (k j : ℕ)
    (hreg : ∀ i ∈ ({j,j+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    completedResidual k (basisInput j)=
      ((chiralRadialScale k*increment k j) • physicalCauchyFeature (j+1),
       (chiralRadialScale k*increment k j) • physicalCauchyFeature (j+1)) := by
  have he := completed_residual_equal_legs k (basisInput j) (basis_regular k j hreg)
  have hf : (completedResidual k (basisInput j)).1=
      (chiralRadialScale k*increment k j) • physicalCauchyFeature (j+1) := by
    rw [completedResidual,basis_shift,source_basis,source_basis]
    change completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (j+1)) • radialVector k (j+1)-
      nativeAdvance (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k j) • radialVector k j)=_
    rw [map_smul,native_advance_radial,← sub_smul,radial_vector_feature,smul_smul]
    congr 1
    rw [normalized_positive_response _ (hreg (j+1) (by simp)).1,
      normalized_positive_response _ (hreg j (by simp)).1]
    unfold chiralRadialScale increment
    ring
  exact Prod.ext hf (he.symm.trans hf)

/-- The next residual port uses the unchanged old physical resolvent. -/
def successorPort (η : ℝ) : PhysicalCauchySpace :=
  (-((η : ℂ)^2)) • greenResolvent 1 η (greenResolvent 1 η (physicalCauchyFeature 3))

theorem reconstructed_successor (η : ℝ) (k : ℕ)
    (hreg : ∀ i ∈ ({1,2} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    reconstructedResidual 0 η k (basisInput 1)=
      ((chiralRadialScale k*increment k 1) • successorPort η,
       (chiralRadialScale k*increment k 1) • successorPort η) := by
  rw [reconstructedResidual,pair_power_zero,successor_residual_numerator,
    residual_basis_pair k 1 hreg]
  apply Prod.ext <;>
    change (η : ℂ) • greenResolvent 1 η (greenResolvent 1 η
      (-(η : ℂ) • nativeAdvance ((chiralRadialScale k*increment k 1) • physicalCauchyFeature 2)))=_
  all_goals
    simp only [successorPort,map_smul,native_advance_feature,smul_smul]
    module

theorem basis_contrast (k j : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0) :
    contrastPort (completedSource k (basisInput j))=
      (chiralRadialScale k*Complex.I) • physicalCauchyFeature j := by
  rw [source_basis,projective_contrast_response k j hF hP,radial_vector_feature,smul_smul]
  congr 1
  unfold chiralRadialScale
  ring

end
end CarryFirstOddGreen
