import SuccessorPort

namespace CarryFirstOddGreen
open CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Only original nonvanishing at the three nodes needed by the two residuals. -/
def nodeRegular (k : ℕ) : Prop := ∀ i : Fin 3,
  completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
  completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0

def basisPort (η : ℝ) (j : ℕ) : PhysicalCauchySpace :=
  if j=0 then greenPort η else successorPort η

theorem residual_two_ports (η : ℝ) (k : ℕ) (hreg : nodeRegular k) (j : Fin 2) :
    reconstructedResidual 0 η k (basisInput j)=
      ((chiralRadialScale k*increment k j) • basisPort η j,
       (chiralRadialScale k*increment k j) • basisPort η j) := by
  fin_cases j
  · simpa [basisInput,initialInput,basisPort,residual_scale_eq,increment,responseIncrement] using
      reconstructed_residual_initial η k (hreg 0).1 (hreg 0).2 (hreg 1).1 (hreg 1).2
  · simpa [basisPort] using reconstructed_successor η k (by
      intro i hi
      have hi3 : i<3 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega
      exact hreg ⟨i,hi3⟩)

theorem residual_ordered_zero (η : ℝ) (k : ℕ) (hreg : nodeRegular k) (i j : Fin 2) :
    physicalForm (reconstructedResidual 0 η k (basisInput i))
      (reconstructedResidual 0 η k (basisInput j))=0 := by
  rw [residual_two_ports η k hreg i,residual_two_ports η k hreg j]
  simp only [physicalForm,sub_self,mul_zero]

theorem form_add_left (x y z : PhysicalPair) :
    physicalForm (x+y) z=physicalForm x z+physicalForm y z := by
  simp only [physicalForm,Prod.fst_add,Prod.snd_add,inner_add_left]
  ring

theorem form_sub_sub (x y u v : PhysicalPair) :
    physicalForm (x-y) (u-v)=physicalForm x u-physicalForm x v-
      physicalForm y u+physicalForm y v := by
  simp only [physicalForm,Prod.fst_sub,Prod.snd_sub,inner_sub_left,inner_sub_right]
  ring

/-- Both ordered crosses are retained; the residual-residual sector vanishes
only after the original two equal legs have been identified. -/
theorem ordered_mixed_pairing (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (k : ℕ) (hreg : nodeRegular k) (i j : Fin 2) :
    physicalForm (reconstructedBulk 0 η k (basisInput i))
      (reconstructedResidual 0 η k (basisInput j))=
      -Complex.I*((k : ℂ)+1)*increment k j*
        inner ℂ (physicalCauchyFeature i) (basisPort η j) := by
  have hs := refined_source_green_split 0 η hη0 hη1 k (basisInput i)
  rw [pair_power_zero] at hs
  have hf := congrArg (fun x => physicalForm x
    (reconstructedResidual 0 η k (basisInput j))) hs
  rw [form_add_left,residual_ordered_zero η k hreg i j,add_zero] at hf
  rw [← hf,residual_two_ports η k hreg j,physical_form_equal_right,
    basis_contrast k i (hreg ⟨i,by omega⟩).1 (hreg ⟨i,by omega⟩).2,chiral_scaled_inner]
  simp only [Complex.conj_I]
  ring

def oddInput (k : ℕ) : ℕ →₀ ℂ :=
  (canonicalCompletedC3RadialSecondStep k)⁻¹ • (basisInput 1-basisInput 0)

def oddBulk (η : ℝ) (k : ℕ) : PhysicalPair :=
  (canonicalCompletedC3RadialSecondStep k)⁻¹ •
    (reconstructedBulk 0 η k (basisInput 1)-reconstructedBulk 0 η k (basisInput 0))

def oddResidual (η : ℝ) (k : ℕ) : PhysicalPair :=
  (canonicalCompletedC3RadialSecondStep k)⁻¹ •
    (reconstructedResidual 0 η k (basisInput 1)-reconstructedResidual 0 η k (basisInput 0))

theorem bulk_smul_sub (η : ℝ) (a : ℂ) (x y : ℕ →₀ ℂ) :
    finiteTfvdBulk η (a • (x-y))=a • (finiteTfvdBulk η x-finiteTfvdBulk η y) := by
  ext j
  cases j with
  | zero => simp [finiteTfvdBulk_zero]
  | succ j =>
    simp only [finiteTfvdBulk_succ,Finsupp.coe_smul,Pi.smul_apply,
      Finsupp.coe_sub,Pi.sub_apply,smul_eq_mul]
    ring

theorem residual_smul_sub (k : ℕ) (a : ℂ) (x y : ℕ →₀ ℂ) :
    completedResidual k (a • (x-y))=a • (completedResidual k x-completedResidual k y) := by
  simp only [completedResidual,map_smul,map_sub]
  module

theorem numerator_smul_sub (η : ℝ) (k : ℕ) (a : ℂ) (x y : ℕ →₀ ℂ) :
    residualNumerator η k (a • (x-y))=a • (residualNumerator η k x-residualNumerator η k y) := by
  simp only [residualNumerator,bulk_smul_sub,map_smul,map_sub,residual_smul_sub]
  module

theorem odd_residual_original (η : ℝ) (k : ℕ) :
    reconstructedResidual 0 η k (oddInput k)=oddResidual η k := by
  simp only [oddInput,reconstructedResidual,numerator_smul_sub,map_smul,map_sub,oddResidual]
  module

theorem odd_source_original (k : ℕ) : completedSource k (oddInput k)=physicalJet k 1 := by
  simp only [oddInput,map_smul,map_sub,source_basis,physicalJet]
  norm_num [Finset.sum_range_succ,completedGreenForwardWeight]
  module

/-- The actual original factorial and complex step, including its phase. -/
theorem first_odd_jet_difference (k : ℕ) :
    physicalJet k 1=(canonicalCompletedC3RadialSecondStep k)⁻¹ •
      (projectiveLegs k 1-projectiveLegs k 0) := by
  rw [← odd_source_original]
  simp only [oddInput,map_smul,map_sub,source_basis]

theorem odd_vector_split (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) :
    physicalJet k 1=oddBulk η k+oddResidual η k := by
  rw [first_odd_jet_difference]
  have h0 := refined_source_green_split 0 η hη0 hη1 k (basisInput 0)
  have h1 := refined_source_green_split 0 η hη0 hη1 k (basisInput 1)
  rw [pair_power_zero,source_basis] at h0 h1
  rw [h1,h0]
  unfold oddBulk oddResidual
  module

theorem odd_bulk_original (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) :
    reconstructedBulk 0 η k (oddInput k)=oddBulk η k := by
  have h := refined_source_green_split 0 η hη0 hη1 k (oddInput k)
  rw [pair_power_zero,odd_source_original,odd_vector_split η hη0 hη1,
    odd_residual_original] at h
  exact (add_right_cancel h).symm

theorem odd_residual_pair (η : ℝ) (k : ℕ) (hreg : nodeRegular k) :
    oddResidual η k=
      ((canonicalCompletedC3RadialSecondStep k)⁻¹ •
        ((chiralRadialScale k*increment k 1) • successorPort η-
         (chiralRadialScale k*increment k 0) • greenPort η),
       (canonicalCompletedC3RadialSecondStep k)⁻¹ •
        ((chiralRadialScale k*increment k 1) • successorPort η-
         (chiralRadialScale k*increment k 0) • greenPort η)) := by
  rw [oddResidual,residual_two_ports η k hreg ⟨1,by decide⟩,
    residual_two_ports η k hreg ⟨0,by decide⟩]
  rfl

theorem odd_residual_self_zero (η : ℝ) (k : ℕ) (hreg : nodeRegular k) :
    physicalForm (oddResidual η k) (oddResidual η k)=0 := by
  rw [odd_residual_pair η k hreg]
  simp only [physicalForm,sub_self,mul_zero]

theorem inverse_step_product (k : ℕ) :
    conj ((canonicalCompletedC3RadialSecondStep k)⁻¹)*
      (canonicalCompletedC3RadialSecondStep k)⁻¹=((k : ℂ)+1)^2 := by
  unfold canonicalCompletedC3RadialSecondStep canonicalGreenJetStep
  simp only [map_inv₀,map_mul,Complex.conj_I,Complex.conj_natCast,
    map_add,map_one]
  have hk : (k : ℂ)+1≠0 := by exact_mod_cast (show (k : ℝ)+1≠0 by positivity)
  field_simp [hk,Complex.I_ne_zero]
  norm_num [Complex.I_sq]

/-- Exact four ordered crossings, with the conjugated normalization. -/
theorem odd_mixed_four_crossings (η : ℝ) (k : ℕ) :
    physicalForm (oddBulk η k) (oddResidual η k)=((k : ℂ)+1)^2*
      (physicalForm (reconstructedBulk 0 η k (basisInput 1)) (reconstructedResidual 0 η k (basisInput 1))-
       physicalForm (reconstructedBulk 0 η k (basisInput 1)) (reconstructedResidual 0 η k (basisInput 0))-
       physicalForm (reconstructedBulk 0 η k (basisInput 0)) (reconstructedResidual 0 η k (basisInput 1))+
       physicalForm (reconstructedBulk 0 η k (basisInput 0)) (reconstructedResidual 0 η k (basisInput 0))) := by
  rw [oddBulk,oddResidual,physical_form_smul,inverse_step_product,form_sub_sub]

def portOverlap (η : ℝ) (j : ℕ) : ℂ :=
  inner ℂ (physicalCauchyFeature 1-physicalCauchyFeature 0) (basisPort η j)

theorem odd_mixed_exact (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (k : ℕ) (hreg : nodeRegular k) :
    physicalForm (oddBulk η k) (oddResidual η k)=
      -Complex.I*((k : ℂ)+1)^3*
        (increment k 1*portOverlap η 1-increment k 0*portOverlap η 0) := by
  rw [odd_mixed_four_crossings,
    ordered_mixed_pairing η hη0 hη1 k hreg ⟨1,by decide⟩ ⟨1,by decide⟩,
    ordered_mixed_pairing η hη0 hη1 k hreg ⟨1,by decide⟩ ⟨0,by decide⟩,
    ordered_mixed_pairing η hη0 hη1 k hreg ⟨0,by decide⟩ ⟨1,by decide⟩,
    ordered_mixed_pairing η hη0 hη1 k hreg ⟨0,by decide⟩ ⟨0,by decide⟩]
  simp only [portOverlap,inner_sub_left]
  ring

theorem odd_energy_three_sectors (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (k : ℕ) (hreg : nodeRegular k) :
    (physicalForm (physicalJet k 1) (physicalJet k 1)).re=
      (physicalForm (oddBulk η k) (oddBulk η k)).re+
        2*(physicalForm (oddBulk η k) (oddResidual η k)).re := by
  rw [odd_vector_split η hη0 hη1,physical_form_four_sectors,odd_residual_self_zero η k hreg]
  simp only [Complex.add_re,add_zero]
  rw [physical_form_re_symm (oddResidual η k) (oddBulk η k)]
  ring

end
end CarryFirstOddGreen
