import NativeRemainder

namespace CarryGreenFinitePart
open CarryInteriorGreen CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- The WHOLE original Green balance, after its proved vector reconstruction. -/
def greenBalance (η a : ℝ) (k : ℕ) : ℝ :=
  (physicalForm (criticalBulk η k a) (criticalBulk η k a)).re+
    2*(physicalForm (criticalBulk η k a) (criticalResidual η k a)).re

theorem green_balance_source (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (k : ℕ) (hr : threeRegular k) (a : ℝ) : greenBalance η a k=
    (physicalForm (completedSource k (criticalInput k a))
      (completedSource k (criticalInput k a))).re := by
  rw [greenBalance,critical_source_original]
  exact (critical_energy_three_sectors η hη0 hη1 k hr a).symm

theorem basis_mean (k j : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0) :
    meanPort (completedSource k (basisInput j))=
      (chiralRadialScale k*nativeResponse (canonicalCompletedC3RadialTiltPoint k j)) • physicalCauchyFeature j := by
  rw [source_basis,projective_mean_response k j hF hP,radial_vector_feature,smul_smul]
  congr 1
  unfold chiralRadialScale
  ring

/-- Original polarized source pairing before choosing the critical weights. -/
theorem source_basis_real (k i j : ℕ)
    (hiF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hiP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hjF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hjP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0) :
    (physicalForm (completedSource k (basisInput i)) (completedSource k (basisInput j))).re=
      ((k : ℝ)+1)*((nativeResponse (canonicalCompletedC3RadialTiltPoint k i)).im+
        (nativeResponse (canonicalCompletedC3RadialTiltPoint k j)).im)/((i : ℝ)+(j : ℝ)+2) := by
  rw [signed_form_mean_contrast,basis_mean k i hiF hiP,basis_mean k j hjF hjP,
    basis_contrast k i hiF hiP,basis_contrast k j hjF hjP,
    chiral_scaled_inner,chiral_scaled_inner,physical_column_inner]
  rw [show (2 : ℂ)⁻¹=((1/2 : ℝ) : ℂ) by norm_num]
  simp only [← Complex.ofReal_inv,Complex.add_re,Complex.mul_re,Complex.mul_im,
    Complex.conj_im,Complex.conj_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,
    Nat.cast_add,Nat.cast_ofNat]
  norm_num only [Complex.natCast_re,Complex.natCast_im,Complex.one_re,Complex.one_im,Complex.add_im]
  norm_num only [Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem second_scale_real (k : ℕ) :
    secondScale k=((-((k : ℝ)+1)^2/2 : ℝ) : ℂ) := by
  unfold secondScale canonicalCompletedC3RadialSecondStep canonicalGreenJetStep
  push_cast
  have hk : (k : ℂ)+1≠0 := by exact_mod_cast (show (k : ℝ)+1≠0 by positivity)
  field_simp [hk,Complex.I_ne_zero]
  norm_num [Complex.I_sq]

def realWeight (k : ℕ) (a : ℝ) (j : ℕ) : ℝ :=
  if j=0 then -((k : ℝ)+1)^2/2-a else if j=1 then ((k : ℝ)+1)^2 else -((k : ℝ)+1)^2/2

theorem critical_weight_real (k : ℕ) (a : ℝ) (j : ℕ) :
    criticalWeight k a j=(realWeight k a j : ℂ) := by
  unfold criticalWeight realWeight
  rw [second_scale_real]
  split_ifs <;> push_cast <;> ring

theorem real_weighted_form (a b : ℝ) (x y : PhysicalPair) :
    (physicalForm ((a : ℂ) • x) ((b : ℂ) • y)).re=a*b*(physicalForm x y).re := by
  rw [physical_form_smul]
  simp [Complex.mul_re]

theorem source_energy_three_samples (a : ℝ) (k : ℕ) (hr : threeRegular k) :
    (physicalForm (completedSource k (criticalInput k a))
      (completedSource k (criticalInput k a))).re=
      ((k : ℝ)+1)*(
        (a^2+7*a*((k : ℝ)+1)^2/12+((k : ℝ)+1)^4/24)*
          (nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)).im+
        (-2*a*((k : ℝ)+1)^2/3-((k : ℝ)+1)^4/30)*
          (nativeResponse (canonicalCompletedC3RadialTiltPoint k 1)).im+
        (a*((k : ℝ)+1)^2/4+((k : ℝ)+1)^4/120)*
          (nativeResponse (canonicalCompletedC3RadialTiltPoint k 2)).im) := by
  have hs : completedSource k (criticalInput k a)=
      ∑ j : Fin 3, (realWeight k a j : ℂ) • completedSource k (basisInput j) := by
    simp only [criticalInput,map_sum,map_smul,critical_weight_real]
  rw [hs,physical_form_sum]
  simp only [Complex.re_sum]
  simp_rw [real_weighted_form]
  have hp (i j : Fin 3) := source_basis_real k i j
    (hr ⟨i,by omega⟩).1 (hr ⟨i,by omega⟩).2
    (hr ⟨j,by omega⟩).1 (hr ⟨j,by omega⟩).2
  simp_rw [hp]
  norm_num [Fin.sum_univ_succ,realWeight]
  ring

/-- All nine source crosses and the two Green mixed sectors have already
been synthesized when this scalar formula is extracted. -/
theorem green_balance_three_samples (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (a : ℝ) (k : ℕ) (hr : threeRegular k) :
    greenBalance η a k=((k : ℝ)+1)*(
        (a^2+7*a*((k : ℝ)+1)^2/12+((k : ℝ)+1)^4/24)*
          (nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)).im+
        (-2*a*((k : ℝ)+1)^2/3-((k : ℝ)+1)^4/30)*
          (nativeResponse (canonicalCompletedC3RadialTiltPoint k 1)).im+
        (a*((k : ℝ)+1)^2/4+((k : ℝ)+1)^4/120)*
          (nativeResponse (canonicalCompletedC3RadialTiltPoint k 2)).im) := by
  rw [green_balance_source η hη0 hη1 k hr a]
  exact source_energy_three_samples a k hr

end
end CarryGreenFinitePart
