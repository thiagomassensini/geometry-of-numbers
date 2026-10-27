import RegressionEnergy
import BinomialCoefficient

namespace CarryOddEnergy
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The ORIGINAL static odd input, including its imaginary-step phase. -/
def nativeOddProfile (r : ℕ) : ℕ →₀ ℂ :=
  (-Complex.I) • ((-1:ℂ)^r • staticStencil (2*r+1))

abbrev oddPairKernel (w : ℕ → ℂ) (r s : ℕ) : ℂ :=
  kernel w (nativeOddProfile r) (nativeOddProfile s)+
    kernel w (nativeOddProfile s) (nativeOddProfile r)

/-- Exact bridge to the existing real native binomial extraction. -/
theorem shifted_power_complex (m p : ℕ) :
    (CarryBinomialGreen.shiftedPower m p : ℂ)=
      (m.factorial:ℂ)*differencePower m p := by
  rw [CarryBinomialGreen.shifted_power_sum, difference_power_sum]
  have hf : (m.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  rw [← mul_assoc, mul_inv_cancel₀ hf, one_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  norm_cast

theorem divided_coefficient_native (m n p : ℕ) :
    dividedCoefficient m n (p+1)=
      (CarryBinomialGreen.mixedCoefficient m n p : ℂ)/(m.factorial:ℂ)/(n.factorial:ℂ) := by
  unfold dividedCoefficient CarryBinomialGreen.mixedCoefficient
  push_cast
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  rw [shifted_power_complex, shifted_power_complex]
  have hm : (m.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- Reuse of the preexisting arbitrary-index leading binomial coefficient. -/
theorem divided_leading_native (m n : ℕ) :
    dividedCoefficient m n (m+n+1)=(-1:ℂ)^n := by
  rw [divided_coefficient_native, CarryBinomialGreen.mixed_coefficient_leading]
  push_cast
  have hm : (m.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- Reuse of same_parity_first_correction at parity ONE, not a new binomial law. -/
theorem divided_first_odd (r s : ℕ) :
    dividedCoefficient (2*r+1) (2*s+1) (2*(r+s+2)+1)=
      -spatialCorrection (2*r+1) (2*s+1) := by
  rw [show 2*(r+s+2)+1=((2*r+1)+(2*s+1)+2)+1 by omega,
    divided_coefficient_native]
  have hc := congrArg (fun x : ℝ => (x:ℂ))
    (CarryBinomialGreen.same_parity_first_correction 1 r s)
  have ha : (CarryBinomialGreen.parityRadialCoefficient 1 r s : ℂ)=
      spatialCorrection (2*r+1) (2*s+1) := by
    unfold CarryBinomialGreen.parityRadialCoefficient CarryBinomialGreen.secondOffset
      CarryBinomialGreen.triangular spatialCorrection curvature CarrySpatialCorrection.slope
    push_cast
    ring
  push_cast at hc
  rw [ha] at hc
  linear_combination -hc

/-- Literal calibration of the odd radial jet, with its -i phase intact. -/
theorem radial_odd_calibration (k r : ℕ) :
    radialJetCoefficients k (2*r+1)=((k:ℂ)+1)^(2*r+1) • nativeOddProfile r := by
  have hi : (-Complex.I)^(2*r+1)=(-1:ℂ)^r*(-Complex.I) := by
    rw [pow_succ, pow_mul]
    have hI : (-Complex.I)^2=(-1:ℂ) := by norm_num [neg_pow, Complex.I_sq]
    rw [hI]
  unfold radialJetCoefficients canonicalCompletedC3RadialSecondStep canonicalGreenJetStep
    nativeOddProfile staticStencil
  simp only [mul_inv_rev, ← inv_pow, inv_inv, Complex.inv_I, mul_pow, hi, smul_smul]
  congr 1
  ring

theorem odd_profile_support (r : ℕ) :
    (nativeOddProfile r).support ⊆ Finset.range (2*r+2) := by
  intro j hj
  apply Finset.mem_range.mpr
  by_contra hn
  have hz : nativeOddProfile r j=0 := by
    simp only [nativeOddProfile, staticStencil, Finsupp.smul_apply, smul_eq_mul,
      raw_stencil_apply, completedGreenForwardWeight]
    rw [Nat.choose_eq_zero_of_lt (by omega : 2*r+1 < j)]
    simp
  exact (Finsupp.mem_support_iff.mp hj) hz

/-- Both conjugated phases are evaluated before reducing the paired kernel. -/
theorem odd_pair_static (w : ℕ → ℂ) (r s : ℕ) :
    oddPairKernel w r s=(-1:ℂ)^(r+s)*
      (kernel w (staticStencil (2*r+1)) (staticStencil (2*s+1))+
        kernel w (staticStencil (2*s+1)) (staticStencil (2*r+1))) := by
  unfold oddPairKernel nativeOddProfile
  simp only [kernel_scale_inputs, map_neg, map_pow, map_one, Complex.conj_I]
  rw [pow_add]
  ring_nf
  norm_num [Complex.I_sq]

theorem odd_pair_divided (r s p : ℕ) (hp : Odd p) :
    oddPairKernel (monomialWeight p) r s=
      (-1:ℂ)^(r+s)*dividedCoefficient (2*r+1) (2*s+1) p := by
  rw [odd_pair_static]
  have he := static_odd_divided (1/2) (by norm_num) (by norm_num) (2*r+1) (2*s+1) p hp
  exact congrArg (fun z : ℂ => (-1:ℂ)^(r+s)*z) he

theorem odd_pair_below (r s l : ℕ) (hl : l < r+s+1) :
    oddPairKernel (monomialWeight (2*l+1)) r s=0 := by
  rw [odd_pair_divided r s (2*l+1) ⟨l,rfl⟩,
    divided_below (show 2*l+1 < (2*r+1)+(2*s+1)+1 by omega), mul_zero]

theorem odd_pair_leading (r s : ℕ) :
    oddPairKernel (monomialWeight (2*(r+s+1)+1)) r s=(-1:ℂ)^(r+s+1) := by
  rw [odd_pair_divided r s _ ⟨r+s+1,rfl⟩,
    show 2*(r+s+1)+1=(2*r+1)+(2*s+1)+1 by omega, divided_leading_native]
  simp only [pow_add, pow_mul]
  norm_num

theorem odd_pair_correction (r s : ℕ) :
    oddPairKernel (monomialWeight (2*(r+s+2)+1)) r s=
      (-1:ℂ)^(r+s+1)*spatialCorrection (2*r+1) (2*s+1) := by
  rw [odd_pair_divided r s _ ⟨r+s+2,rfl⟩, divided_first_odd, pow_succ]
  ring

end
end CarryOddEnergy
