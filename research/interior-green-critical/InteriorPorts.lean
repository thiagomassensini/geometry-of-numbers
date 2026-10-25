import FirstOddJet

namespace CarryInteriorGreen
open CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- The interior stencil of the ORIGINAL finite TFVD, valid at every address. -/
theorem interior_bulk (η : ℝ) (j : ℕ) : finiteTfvdBulk η (basisInput (j+2))=
    (η : ℂ)⁻¹ • basisInput (j+1)+(-2 : ℂ) • basisInput (j+2)+
      (η : ℂ) • basisInput (j+3) := by
  ext i
  cases i with
  | zero => simp [finiteTfvdBulk_zero,basisInput]
  | succ i =>
    rw [finiteTfvdBulk_succ]
    simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,basisInput,Finsupp.single_apply]
    split_ifs <;> first | omega | ring

/-- Includes the backward residual and the advanced forward residual.
No sign, nonvanishing, truncation or moment assumption is used. -/
theorem interior_numerator (η : ℝ) (k j : ℕ) :
    residualNumerator η k (basisInput (j+2))=
      (η : ℂ)⁻¹ • completedResidual k (basisInput (j+1))-
        (η : ℂ) • pairAdvance (completedResidual k (basisInput (j+2))) := by
  rw [residualNumerator,interior_bulk,basis_shift]
  simp only [residual_add,completed_residual_smul]
  module

def greenColumn (η : ℝ) (j : ℕ) : PhysicalCauchySpace :=
  greenResolvent 1 η (greenResolvent 1 η (physicalCauchyFeature j))

def interiorPort (η : ℝ) (k j : ℕ) : PhysicalCauchySpace :=
  (chiralRadialScale k*increment k (j+1)) • greenColumn η (j+2)-
    ((η : ℂ)^2*chiralRadialScale k*increment k (j+2)) • greenColumn η (j+4)

/-- A vector equality in the unchanged old physical Cauchy space. The two
terms are extracted from the same completed source, before any pairing. -/
theorem reconstructed_interior (η : ℝ) (hη : η≠0) (k j : ℕ)
    (hr : ∀ i ∈ ({j+1,j+2,j+3} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    reconstructedResidual 0 η k (basisInput (j+2))=
      (interiorPort η k j,interiorPort η k j) := by
  have h1 : ∀ i ∈ ({j+1,(j+1)+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0 := by
    intro i hi
    exact hr i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢; omega)
  have h2 : ∀ i ∈ ({j+2,(j+2)+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0 := by
    intro i hi
    exact hr i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢; omega)
  rw [reconstructedResidual,pair_power_zero,interior_numerator,
    residual_basis_pair k (j+1) h1,residual_basis_pair k (j+2) h2]
  have hc : (η : ℂ)≠0 := by exact_mod_cast hη
  apply Prod.ext <;>
    change (η : ℂ) • greenResolvent 1 η (greenResolvent 1 η
      ((η : ℂ)⁻¹ • ((chiralRadialScale k*increment k (j+1)) • physicalCauchyFeature ((j+1)+1))-
       (η : ℂ) • nativeAdvance ((chiralRadialScale k*increment k (j+2)) • physicalCauchyFeature ((j+2)+1))))=_
  all_goals
    simp only [map_sub,map_smul,native_advance_feature,smul_sub,smul_smul,
      ← mul_assoc,mul_inv_cancel₀ hc,one_mul,interiorPort,greenColumn]
    module

theorem finite_bulk_add (η : ℝ) (x y : ℕ →₀ ℂ) :
    finiteTfvdBulk η (x+y)=finiteTfvdBulk η x+finiteTfvdBulk η y := by
  ext j
  cases j with
  | zero => simp [finiteTfvdBulk_zero]
  | succ j => simp only [finiteTfvdBulk_succ,Finsupp.add_apply]; ring

theorem numerator_add (η : ℝ) (k : ℕ) (x y : ℕ →₀ ℂ) :
    residualNumerator η k (x+y)=residualNumerator η k x+residualNumerator η k y := by
  simp only [residualNumerator,finite_bulk_add,residual_add,map_add]
  module

theorem finite_bulk_zero (η : ℝ) : finiteTfvdBulk η 0=0 := by
  ext j
  cases j <;> simp [finiteTfvdBulk_zero,finiteTfvdBulk_succ]

theorem numerator_zero (η : ℝ) (k : ℕ) : residualNumerator η k 0=0 := by
  simp only [residualNumerator,completedResidual,finite_bulk_zero,map_zero,
    sub_zero,smul_zero,add_zero]

theorem numerator_smul (η : ℝ) (k : ℕ) (a : ℂ) (x : ℕ →₀ ℂ) :
    residualNumerator η k (a • x)=a • residualNumerator η k x := by
  simpa only [sub_zero,numerator_zero] using numerator_smul_sub η k a x 0

/-- Merely the linear structure of the existing reconstruction, not a new
physical operator or an altered metric. -/
def residualMap (η : ℝ) (k : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] PhysicalPair where
  toFun := reconstructedResidual 0 η k
  map_add' x y := by simp only [reconstructedResidual,numerator_add,map_add,smul_add]
  map_smul' a x := by
    change reconstructedResidual 0 η k (a • x)=a • reconstructedResidual 0 η k x
    simp only [reconstructedResidual,numerator_smul,map_smul,smul_smul]
    module

theorem residual_map_apply (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) :
    residualMap η k x=reconstructedResidual 0 η k x := rfl

theorem bulk_eq_source_sub_residual (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (k : ℕ) (x : ℕ →₀ ℂ) :
    reconstructedBulk 0 η k x=completedSource k x-reconstructedResidual 0 η k x := by
  have h := refined_source_green_split 0 η hη0 hη1 k x
  rw [pair_power_zero] at h
  rw [h]
  abel

def bulkMap (η : ℝ) (k : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] PhysicalPair :=
  completedSource k-residualMap η k

theorem bulk_map_original (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) (x : ℕ →₀ ℂ) :
    bulkMap η k x=reconstructedBulk 0 η k x := (bulk_eq_source_sub_residual η hη0 hη1 k x).symm

end
end CarryInteriorGreen
