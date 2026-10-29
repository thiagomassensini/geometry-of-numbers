import AlignmentTest
import RefinementCoherence
import GreenPort

namespace CarryFiniteGreen
open CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

def initialInput : ℕ →₀ ℂ := Finsupp.single 0 1

theorem initial_shift : coefficientShift initialInput=Finsupp.single 1 1 := by
  simp [initialInput,coefficientShift,Finsupp.mapDomain_single]

theorem initial_bulk (η : ℝ) : finiteTfvdBulk η initialInput=(η : ℂ) • Finsupp.single 1 1 := by
  ext j
  cases j with
  | zero => simp [finiteTfvdBulk_zero]
  | succ j =>
    rw [finiteTfvdBulk_succ]
    cases j with
    | zero => simp [initialInput]
    | succ j => simp [initialInput,Nat.add_assoc]

theorem completed_residual_smul (k : ℕ) (a : ℂ) (x : ℕ →₀ ℂ) :
    completedResidual k (a • x)=a • completedResidual k x := by
  simp only [completedResidual,map_smul,smul_sub]

theorem residual_numerator_initial (η : ℝ) (k : ℕ) :
    residualNumerator η k initialInput=(2 : ℂ) • completedResidual k initialInput-
      (η : ℂ) • pairAdvance (completedResidual k initialInput) := by
  rw [residualNumerator,initial_bulk,initial_shift,completed_residual_smul]
  module

theorem native_advance_radial (k j : ℕ) :
    nativeAdvance (radialVector k j)=radialVector k (j+1) := by
  rw [radial_vector_feature,map_smul,native_advance_feature,radial_vector_feature]

theorem normalized_positive_response (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z≠0) :
    completedNativeNormalizedPositiveChiralAmplitude z=
      (2*nativeResponse z+Complex.I)/(Real.sqrt 2 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  unfold completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization
    completedNativePositiveHermiteBiehlerCoordinate nativeResponse completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  field_simp [hs,hF]

def responseIncrement (k : ℕ) : ℂ :=
  nativeResponse (canonicalCompletedC3RadialTiltPoint k 1)-
    nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)

def residualScale (k : ℕ) : ℂ :=
  (2/(Real.sqrt 2 : ℂ))*responseIncrement k*(Real.sqrt ((k : ℝ)+1) : ℂ)

theorem initial_regular (k : ℕ)
    (hF0 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP0 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hF1 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1)≠0)
    (hP1 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 1)≠0) :
    sourceRegular k initialInput := by
  intro j hj i hi
  have hj0 : j=0 := by simpa [initialInput] using hj
  subst j
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨hF0,hP0⟩
  · exact ⟨hF1,hP1⟩

theorem residual_initial_first (k : ℕ)
    (hF0 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hF1 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1)≠0) :
    (completedResidual k initialInput).1=residualScale k • physicalCauchyFeature 1 := by
  rw [completedResidual,initial_shift]
  simp only [completedSource,initialInput,Finsupp.linearCombination_single,one_smul,
    Prod.fst_sub,pairAdvance,projectiveLegs]
  change completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 1) • radialVector k 1-
    nativeAdvance (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) • radialVector k 0)=_
  rw [map_smul,native_advance_radial,← sub_smul,radial_vector_feature,smul_smul]
  congr 1
  rw [normalized_positive_response _ hF1,normalized_positive_response _ hF0]
  unfold residualScale responseIncrement
  ring

/-- The entire original zero-input numerator reduces vectorially to one
port. Its higher residual terms CANCEL; they are not omitted. -/
theorem residual_initial_pair (k : ℕ)
    (hF0 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP0 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hF1 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1)≠0)
    (hP1 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 1)≠0) :
    completedResidual k initialInput=
      (residualScale k • physicalCauchyFeature 1,residualScale k • physicalCauchyFeature 1) := by
  have he := completed_residual_equal_legs k initialInput (initial_regular k hF0 hP0 hF1 hP1)
  apply Prod.ext
  · exact residual_initial_first k hF0 hF1
  · exact he.symm.trans (residual_initial_first k hF0 hF1)

theorem pair_power_zero (x : PhysicalPair) : pairPower 0 x=x := by
  apply Prod.ext <;> exact power_identity _

/-- Identification of the ACTUAL reconstructed residual with its two
original equal legs, before a single inner product is taken. -/
theorem reconstructed_residual_initial (η : ℝ) (k : ℕ)
    (hF0 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hP0 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0)≠0)
    (hF1 : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 1)≠0)
    (hP1 : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 1)≠0) :
    reconstructedResidual 0 η k initialInput=
      (residualScale k • greenPort η,residualScale k • greenPort η) := by
  rw [reconstructedResidual,pair_power_zero,residual_numerator_initial,
    residual_initial_pair k hF0 hP0 hF1 hP1]
  apply Prod.ext <;>
    change (η : ℂ) • greenResolvent 1 η (greenResolvent 1 η
      ((2 : ℂ) • (residualScale k • physicalCauchyFeature 1)-
       (η : ℂ) • nativeAdvance (residualScale k • physicalCauchyFeature 1)))=_
  all_goals
    simp only [greenPort,map_smul,smul_sub,smul_smul,map_sub]
    module

end
end CarryFiniteGreen
