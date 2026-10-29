import AddressGreen

namespace CarryAddressSplit
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000

/-- One-step lowering of the EXISTING factorial-normalized binomial stencil. -/
theorem static_address_step (m : ℕ) :
    addressPower 1 (staticStencil (m+1))=((m:ℂ)+2) • staticStencil (m+1)+staticStencil m := by
  ext j
  simp only [address_power_apply,pow_one,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,
    staticStencil,raw_stencil_apply,completedGreenForwardWeight]
  push_cast
  by_cases hj : j ≤ m
  · have hc := congrArg (fun n : ℕ => (n:ℂ)) (Nat.choose_mul_succ_eq m j)
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub (by omega : j ≤ m+1)] at hc
    push_cast at hc
    rw [show m+1-j=(m-j)+1 by omega,pow_succ,Nat.factorial_succ]
    push_cast
    have hf : (m.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hm : (m:ℂ)+1≠0 := by exact_mod_cast (by omega : m+1≠0)
    field_simp
    linear_combination -hc
  · by_cases he : j=m+1
    · subst j
      simp only [Nat.sub_self,pow_zero,Nat.choose_self,Nat.choose_eq_zero_of_lt (by omega : m < m+1),
        Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,add_zero]
      push_cast
      ring
    · have h1 := Nat.choose_eq_zero_of_lt (by omega : m+1 < j)
      have h0 := Nat.choose_eq_zero_of_lt (by omega : m < j)
      simp [h1,h0]

/-- Exact two-step law, retaining the asymmetric 2m+5 first-address term. -/
theorem static_address_two_step (m : ℕ) :
    addressPower 2 (staticStencil (m+2))-
      ((2*m+5:ℕ):ℂ) • addressPower 1 (staticStencil (m+2))+
      (((m+2:ℕ):ℂ)*((m+3:ℕ):ℂ)) • staticStencil (m+2)=staticStencil m := by
  have h1 := static_address_step (m+1)
  have h2 := congrArg (addressPower 1) h1
  rw [address_power_add,address_power_scale,address_power_comp,static_address_step m] at h2
  have h3 : staticStencil (m+1)=addressPower 1 (staticStencil (m+2))-((m:ℂ)+3) • staticStencil (m+2) := by
    rw [h1]
    norm_num only [Nat.cast_add,Nat.cast_one]
    module
  rw [h3] at h2
  simp only [show m+1+1=m+2 by omega] at h2
  push_cast at h2 ⊢
  ext j
  have h := DFunLike.congr_fun h2 j
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul] at h ⊢
  linear_combination h

/-- All odd orders: lower the ORIGINAL phase-preserving profile by TWO degrees. -/
theorem odd_address_lowering (r : ℕ) :
    addressPower 2 (nativeOddProfile (r+1))-
      ((4*r+7:ℕ):ℂ) • addressPower 1 (nativeOddProfile (r+1))+
      (((2*r+3:ℕ):ℂ)*((2*r+4:ℕ):ℂ)) • nativeOddProfile (r+1)= -nativeOddProfile r := by
  have he := congrArg (fun c : ℕ →₀ ℂ => (-Complex.I*(-1:ℂ)^(r+1)) • c)
    (static_address_two_step (2*r+1))
  simp only [nativeOddProfile,address_power_scale,smul_smul]
  rw [show 2*(r+1)+1=2*r+1+2 by omega]
  simp only [smul_add,smul_sub,smul_smul] at he
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at he ⊢
  rw [pow_succ] at he ⊢
  convert he using 1 <;> module

/-- Endpoint moments are the original finite differences, with the same factorial. -/
theorem endpoint_static_power (m p : ℕ) :
    sourceEndpoint (addressPower p (staticStencil m))=differencePower m p := by
  rw [staticStencil,address_power_scale,rawStencil,address_power_sum]
  simp only [map_smul,map_sum,address_power_scale,address_power_single,source_endpoint_single,smul_eq_mul,mul_one]
  rw [difference_power_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold completedGreenForwardWeight
  push_cast
  ring

theorem endpoint_odd_power (r p : ℕ) :
    sourceEndpoint (addressPower p (nativeOddProfile r))=
      (-Complex.I*(-1:ℂ)^r)*differencePower (2*r+1) p := by
  rw [nativeOddProfile,address_power_scale,address_power_scale,map_smul,map_smul,endpoint_static_power]
  simp only [smul_eq_mul]
  ring

/-- Native boundary cancellations in EVERY odd order, without a sign assumption. -/
theorem endpoint_odd_power_zero (r p : ℕ) (hp : p<2*r+1) :
    sourceEndpoint (addressPower p (nativeOddProfile r))=0 := by
  rw [endpoint_odd_power,difference_power_below hp,mul_zero]

/-- The first surviving trace is NONZERO: no invariant boundary-free domain is assumed. -/
theorem endpoint_odd_first_survives (r : ℕ) :
    sourceEndpoint (addressPower (2*r+1) (nativeOddProfile r))= -Complex.I*(-1:ℂ)^r := by
  rw [endpoint_odd_power,difference_power_diagonal,mul_one]

theorem endpoint_odd_first_nonzero (r : ℕ) :
    sourceEndpoint (addressPower (2*r+1) (nativeOddProfile r))≠0 := by
  rw [endpoint_odd_first_survives]
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (pow_ne_zero r (by norm_num))

end
end CarryAddressSplit
