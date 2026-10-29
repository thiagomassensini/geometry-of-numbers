import RawGreenRay

namespace CarryAllOrderCorrection
open CarrySelfAdjointOperator CarrySourceLaw Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

theorem native_sample_eq_atom (k r s : ℕ) :
    canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k + r • canonicalCompletedC3RadialSecondStep k)
      (canonicalCompletedC3RadialSecondStep k + s • canonicalCompletedC3RadialSecondStep k) =
      rawAtom r s (canonicalGreenJetStep k) /
        (Complex.I*(r+s+2:ℂ)*canonicalGreenJetStep k) := by
  have ht := canonicalGreenJetStep_ne_zero k
  have hc : conj (canonicalGreenJetStep k) = canonicalGreenJetStep k := by
    simp [canonicalGreenJetStep]
  have hp (a : ℕ) : canonicalCompletedC3RadialSecondStep k +
      a • canonicalCompletedC3RadialSecondStep k =
      (Complex.I*(a+1:ℂ))*canonicalGreenJetStep k := by
    simp only [canonicalCompletedC3RadialSecondStep, nsmul_eq_mul]
    ring
  unfold canonicalCompletedNativePolarizedDslopeKernel
  rw [hp,hp]
  simp only [map_mul,map_add,map_natCast,map_one,Complex.conj_I,hc]
  have hd : (Complex.I*(s+1:ℂ))*canonicalGreenJetStep k -
      (-Complex.I*(r+1:ℂ))*canonicalGreenJetStep k =
      Complex.I*(r+s+2:ℂ)*canonicalGreenJetStep k := by ring
  have hsum : (r+s+2:ℂ) ≠ 0 := by
    exact_mod_cast (show (r+s+2:ℝ) ≠ 0 by positivity)
  have hsep : (Complex.I*(s+1:ℂ))*canonicalGreenJetStep k ≠
      (-Complex.I*(r+1:ℂ))*canonicalGreenJetStep k := by
    apply sub_ne_zero.mp
    rw [hd]
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero hsum) ht
  rw [dslope_of_ne _ hsep,slope_def_field,hd]
  rfl

/-- Exact numerator before the singular factorial/step normalization. Every
sample of the completed physical kernel is still present. -/
theorem raw_kernel_difference_eq_ray (k p q : ℕ) :
    completedGreenKernelTwoStepShiftedRawDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k) (canonicalCompletedC3RadialSecondStep k) p q =
      rawGreenRay p q (canonicalGreenJetStep k) / canonicalGreenJetStep k := by
  unfold completedGreenKernelTwoStepShiftedRawDifference rawGreenRay
  rw [completedGreenForwardDifference_iter_eq_sum_shift,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  rw [completedGreenForwardDifference_iter_eq_sum_shift,Finset.sum_div]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [native_sample_eq_atom]
  simp only [completedGreenForwardWeight,zsmul_eq_mul,div_eq_mul_inv,mul_inv_rev]
  ring

def phaseFactor (i j s : ℕ) : ℂ :=
  (-1:ℂ)^(i+j)/(((2*i+s).factorial:ℂ)*((2*j+s).factorial:ℂ))

theorem parity_phase (i j s : ℕ) :
    (-Complex.I)^(2*i+s)*Complex.I^(2*j+s) = (-1:ℂ)^(i+j) := by
  rw [pow_add,pow_add,pow_mul,pow_mul]
  norm_num [Complex.I_sq]
  have he : (-Complex.I)^s*Complex.I^s = 1 := by
    rw [← mul_pow]
    norm_num [Complex.I_sq]
  rw [pow_add]
  linear_combination (norm := ring_nf) ((-1:ℂ)^i*(-1:ℂ)^j)*he

theorem normalization_eq_phase (k i j s : ℕ) :
    conj ((((2*i+s).factorial:ℂ)*canonicalCompletedC3RadialSecondStep k^(2*i+s))⁻¹) *
      ((((2*j+s).factorial:ℂ)*canonicalCompletedC3RadialSecondStep k^(2*j+s))⁻¹) =
    phaseFactor i j s / canonicalGreenJetStep k^(2*i+s+(2*j+s)) := by
  have ht := canonicalGreenJetStep_ne_zero k
  have hc : conj (canonicalGreenJetStep k) = canonicalGreenJetStep k := by
    simp [canonicalGreenJetStep]
  have hf : ((2*i+s).factorial:ℂ) ≠ 0 := by exact_mod_cast (2*i+s).factorial_ne_zero
  have hg : ((2*j+s).factorial:ℂ) ≠ 0 := by exact_mod_cast (2*j+s).factorial_ne_zero
  simp only [map_inv₀,map_mul,map_pow,map_natCast,canonicalCompletedC3RadialSecondStep,
    Complex.conj_I,hc]
  rw [← mul_inv]
  have he : (((2*i+s).factorial:ℂ)*(-Complex.I*canonicalGreenJetStep k)^(2*i+s)) *
      (((2*j+s).factorial:ℂ)*(Complex.I*canonicalGreenJetStep k)^(2*j+s)) =
      (-1:ℂ)^(i+j)*((2*i+s).factorial:ℂ)*((2*j+s).factorial:ℂ)*
        canonicalGreenJetStep k^(2*i+s+(2*j+s)) := by
    rw [mul_pow,mul_pow,pow_add]
    linear_combination (norm := ring_nf)
      (((2*i+s).factorial:ℂ)*((2*j+s).factorial:ℂ)*
        canonicalGreenJetStep k^(2*i+s)*canonicalGreenJetStep k^(2*j+s))*parity_phase i j s
  rw [he]
  unfold phaseFactor
  have hs : (-1:ℂ)^(i+j) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsq : ((-1:ℂ)^(i+j))^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm (i+j) 2,pow_mul]
    norm_num
  field_simp
  exact hsq.symm

/-- The exact original projective source pairing, with every phase and
factorial accounted for, is the analytic raw numerator divided by its known
vanishing order. No positivity or state replacement is involved. -/
theorem projective_pairing_eventually_ray (i j s : ℕ) :
    (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k (2*i+s)) (projectiveChiralDifferenceJet k (2*j+s)))
      =ᶠ[atTop] (fun k => phaseFactor i j s *
        (rawGreenRay (2*i+s) (2*j+s) (canonicalGreenJetStep k) /
          canonicalGreenJetStep k^(2*i+s+(2*j+s)+1))) := by
  filter_upwards [projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope (2*i+s) (2*j+s)]
    with k hk
  rw [hk,completedGreenKernelTwoStepShiftedForwardDifference,
    raw_kernel_difference_eq_ray,normalization_eq_phase]
  rw [pow_succ]
  ring

end
end CarryAllOrderCorrection
