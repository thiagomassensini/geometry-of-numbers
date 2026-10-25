import InteriorPorts

namespace CarryInteriorGreen
open CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

def residualFeature (η : ℝ) (k : ℕ) : ℕ → PhysicalCauchySpace
  | 0 => increment k 0 • greenPort η
  | 1 => increment k 1 • successorPort η
  | j+2 => increment k (j+1) • greenColumn η (j+2)-
      ((η : ℂ)^2*increment k (j+2)) • greenColumn η (j+4)

def threeRegular (k : ℕ) : Prop := ∀ i : Fin 4,
  completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
  completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0

theorem three_residual_columns (η : ℝ) (hη : η≠0) (k : ℕ) (hr : threeRegular k) (j : Fin 3) :
    reconstructedResidual 0 η k (basisInput j)=
      (chiralRadialScale k • residualFeature η k j,chiralRadialScale k • residualFeature η k j) := by
  fin_cases j
  · simpa [basisInput,initialInput,residualFeature,residual_scale_eq,increment,responseIncrement,smul_smul] using
      reconstructed_residual_initial η k (hr 0).1 (hr 0).2 (hr 1).1 (hr 1).2
  · have h := reconstructed_successor η k (by
      intro i hi
      have hi4 : i<4 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega
      exact hr ⟨i,hi4⟩)
    simpa only [residualFeature,smul_smul] using h
  · have h := reconstructed_interior η hη k 0 (by
      intro i hi
      have hi4 : i<4 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega
      exact hr ⟨i,hi4⟩)
    change reconstructedResidual 0 η k (basisInput 2)=
      (chiralRadialScale k • residualFeature η k 2,chiralRadialScale k • residualFeature η k 2)
    rw [h]
    apply Prod.ext <;>
      simp only [residualFeature,interiorPort,smul_sub,smul_smul] <;> module

theorem three_residual_cross_zero (η : ℝ) (hη : η≠0) (k : ℕ) (hr : threeRegular k) (i j : Fin 3) :
    physicalForm (reconstructedResidual 0 η k (basisInput i))
      (reconstructedResidual 0 η k (basisInput j))=0 := by
  rw [three_residual_columns η hη k hr i,three_residual_columns η hη k hr j]
  simp only [physicalForm,sub_self,mul_zero]

/-- Every ordered crossing of the three original basis inputs. -/
theorem three_ordered_crossing (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (k : ℕ) (hr : threeRegular k) (i j : Fin 3) :
    physicalForm (reconstructedBulk 0 η k (basisInput i))
      (reconstructedResidual 0 η k (basisInput j))=
      -Complex.I*((k : ℂ)+1)*inner ℂ (physicalCauchyFeature i) (residualFeature η k j) := by
  have hs := refined_source_green_split 0 η hη0 hη1 k (basisInput i)
  rw [pair_power_zero] at hs
  have hf := congrArg (fun x => physicalForm x (reconstructedResidual 0 η k (basisInput j))) hs
  rw [form_add_left,three_residual_cross_zero η hη0.ne' k hr i j,add_zero] at hf
  rw [← hf,three_residual_columns η hη0.ne' k hr j,physical_form_equal_right,
    basis_contrast k i (hr ⟨i,by omega⟩).1 (hr ⟨i,by omega⟩).2]
  have he : chiralRadialScale k • residualFeature η k j=
      (chiralRadialScale k*1) • residualFeature η k j := by simp
  rw [he,chiral_scaled_inner]
  simp only [Complex.conj_I,mul_one]
  ring

def secondScale (k : ℕ) : ℂ := ((2 : ℂ)*canonicalCompletedC3RadialSecondStep k^2)⁻¹

def criticalWeight (k : ℕ) (a : ℝ) (j : ℕ) : ℂ :=
  if j=0 then secondScale k-(a : ℂ) else if j=1 then -2*secondScale k else secondScale k

/-- a is free. The physical jets exist first, independently of moments. -/
def criticalInput (k : ℕ) (a : ℝ) : ℕ →₀ ℂ :=
  ∑ j : Fin 3, criticalWeight k a j • basisInput j

theorem critical_source_original (k : ℕ) (a : ℝ) :
    completedSource k (criticalInput k a)=physicalJet k 2-(a : ℂ) • physicalJet k 0 := by
  simp only [criticalInput,map_sum,map_smul,source_basis]
  norm_num [Fin.sum_univ_succ,criticalWeight,physicalJet,Finset.sum_range_succ,
    completedGreenForwardWeight,secondScale]
  module

def criticalBulk (η : ℝ) (k : ℕ) (a : ℝ) : PhysicalPair := reconstructedBulk 0 η k (criticalInput k a)
def criticalResidual (η : ℝ) (k : ℕ) (a : ℝ) : PhysicalPair := reconstructedResidual 0 η k (criticalInput k a)

theorem critical_residual_expansion (η : ℝ) (k : ℕ) (a : ℝ) :
    criticalResidual η k a=∑ j : Fin 3,
      criticalWeight k a j • reconstructedResidual 0 η k (basisInput j) := by
  change residualMap η k (criticalInput k a)=_
  simp only [criticalInput,map_sum,map_smul,residual_map_apply]

theorem critical_bulk_expansion (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) (a : ℝ) :
    criticalBulk η k a=∑ j : Fin 3,
      criticalWeight k a j • reconstructedBulk 0 η k (basisInput j) := by
  change reconstructedBulk 0 η k (criticalInput k a)=_
  rw [← bulk_map_original η hη0 hη1]
  rw [criticalInput,map_sum]
  simp only [map_smul]
  simp only [bulk_map_original η hη0 hη1]

theorem critical_residual_pair (η : ℝ) (hη : η≠0) (k : ℕ) (hr : threeRegular k) (a : ℝ) :
    criticalResidual η k a=
      (∑ j : Fin 3, (criticalWeight k a j*chiralRadialScale k) • residualFeature η k j,
       ∑ j : Fin 3, (criticalWeight k a j*chiralRadialScale k) • residualFeature η k j) := by
  rw [critical_residual_expansion]
  simp only [three_residual_columns η hη k hr]
  apply Prod.ext <;> simp [Fin.sum_univ_succ,smul_smul]

theorem critical_residual_self_zero (η : ℝ) (hη : η≠0) (k : ℕ) (hr : threeRegular k) (a : ℝ) :
    physicalForm (criticalResidual η k a) (criticalResidual η k a)=0 := by
  rw [critical_residual_pair η hη k hr a]
  simp only [physicalForm,sub_self,mul_zero]

/-- Nine ORDERED crossings, including conjugation of every coefficient.
No real projection has been taken. -/
theorem critical_mixed_nine_crossings (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) (a b : ℝ) :
    physicalForm (criticalBulk η k a) (criticalResidual η k b)=
      ∑ i : Fin 3, ∑ j : Fin 3,
        conj (criticalWeight k a i)*criticalWeight k b j*
          physicalForm (reconstructedBulk 0 η k (basisInput i))
            (reconstructedResidual 0 η k (basisInput j)) := by
  rw [critical_bulk_expansion η hη0 hη1,critical_residual_expansion]
  rw [physical_form_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact physical_form_smul _ _ _ _

theorem critical_vector_split (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (k : ℕ) (a : ℝ) :
    physicalJet k 2-(a : ℂ) • physicalJet k 0=criticalBulk η k a+criticalResidual η k a := by
  have h := refined_source_green_split 0 η hη0 hη1 k (criticalInput k a)
  rwa [pair_power_zero,critical_source_original] at h

theorem critical_energy_three_sectors (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (k : ℕ) (hr : threeRegular k) (a : ℝ) :
    (physicalForm (physicalJet k 2-(a : ℂ) • physicalJet k 0)
      (physicalJet k 2-(a : ℂ) • physicalJet k 0)).re=
      (physicalForm (criticalBulk η k a) (criticalBulk η k a)).re+
        2*(physicalForm (criticalBulk η k a) (criticalResidual η k a)).re := by
  rw [critical_vector_split η hη0 hη1,physical_form_four_sectors,
    critical_residual_self_zero η hη0.ne' k hr a]
  simp only [Complex.add_re,add_zero]
  rw [physical_form_re_symm (criticalResidual η k a) (criticalBulk η k a)]
  ring

end
end CarryInteriorGreen
