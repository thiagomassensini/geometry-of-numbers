import PhysicalPrincipalSplit
namespace CarryPrincipalFlow
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000


/-- The existing Cauchy inner product, with unit readout weight. -/
abbrev bareKernel (c d : ℕ →₀ ℂ) : ℂ := kernel (fun _ => 1) c d

theorem bare_kernel_inner (c d : ℕ →₀ ℂ) :
    bareKernel c d=inner ℂ (physicalCauchySynthesis c) (physicalCauchySynthesis d) := by
  have he : coefficientWeight (fun _ => (1:ℂ)) d=d := by
    ext j
    simp only [coefficient_weight_apply,one_mul]
  change inner ℂ _ (physicalCauchySynthesis (coefficientWeight (fun _ => (1:ℂ)) d))=_
  rw [he]

theorem bare_kernel_conj (c d : ℕ →₀ ℂ) : conj (bareKernel c d)=bareKernel d c := by
  rw [bare_kernel_inner,bare_kernel_inner]
  exact inner_conj_symm _ _

/-- All endpoint crossings from the original Euler/Green mechanism. -/
def boundaryFlux (m : ℕ) (c d : ℕ →₀ ℂ) : ℂ :=
  ∑ p ∈ Finset.range m, (-1:ℂ)^p*conj (sourceEndpoint (addressPower p c))*
    sourceEndpoint (addressPower (m-1-p) d)

theorem boundary_flux_succ (m : ℕ) (c d : ℕ →₀ ℂ) :
    boundaryFlux (m+1) c d=conj (sourceEndpoint c)*sourceEndpoint (addressPower m d)-
      boundaryFlux m (addressPower 1 c) d := by
  unfold boundaryFlux
  rw [Finset.sum_range_succ']
  simp only [pow_zero,one_mul,address_power_zero,Nat.add_sub_cancel]
  have he : (∑ p ∈ Finset.range m, (-1:ℂ)^(p+1)*conj (sourceEndpoint (addressPower (p+1) c))*
      sourceEndpoint (addressPower (m-(p+1)) d))=
      -(∑ p ∈ Finset.range m, (-1:ℂ)^p*conj (sourceEndpoint (addressPower p (addressPower 1 c)))*
        sourceEndpoint (addressPower (m-1-p) d)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [address_power_comp,show m-(p+1)=m-1-p by omega,pow_succ]
    ring
  rw [he]
  simp only [Nat.sub_zero]
  ring

/-- Arbitrary order, with ALL boundary terms. No invariant trace-zero domain. -/
theorem source_green_all_order (m : ℕ) (c d : ℕ →₀ ℂ) :
    bareKernel c (addressPower m d)-(-1:ℂ)^m*bareKernel (addressPower m c) d=
      boundaryFlux m c d := by
  induction m generalizing c with
  | zero => simp [boundaryFlux,address_power_zero]
  | succ m ih =>
    have hs := kernel_address_green (fun _ => 1) c (addressPower m d)
    simp only [one_mul,← source_endpoint_sum,address_power_comp] at hs
    rw [show 1+m=m+1 by omega] at hs
    have hi := ih (addressPower 1 c)
    rw [address_power_comp] at hi
    rw [boundary_flux_succ,pow_succ]
    linear_combination hs-hi

theorem monomial_kernel_right (m : ℕ) (c d : ℕ →₀ ℂ) :
    kernel (monomialWeight m) c d=bareKernel c (addressPower m d) := by
  have he := kernel_address_right m (fun _ => 1) c d
  have hw : (fun j : ℕ => ((j:ℂ)+1)^m*(1:ℂ))=monomialWeight m := by
    funext j
    simp [monomialWeight]
  rw [hw] at he
  exact he.symm

/-- Both imaginary quadratures are retained before invoking Hermitian symmetry. -/
theorem monomial_kernel_reverse (m : ℕ) (c d : ℕ →₀ ℂ)
    (hc : ∀ j, conj (c j)= -c j) (hd : ∀ j, conj (d j)= -d j) :
    kernel (monomialWeight m) d c=bareKernel (addressPower m c) d := by
  have hw (j : ℕ) : conj (monomialWeight m j)=monomialWeight m j := by
    simp [monomialWeight]
  have hr := kernel_imaginary_imaginary (monomialWeight m) d c hw hd hc
  calc
    kernel (monomialWeight m) d c=conj (kernel (monomialWeight m) d c) := hr.symm
    _ = conj (bareKernel d (addressPower m c)) := congrArg conj (monomial_kernel_right m d c)
    _ = bareKernel (addressPower m c) d := bare_kernel_conj d (addressPower m c)


/-- Complete TWO-argument odd-power response layer equals its endpoint flux. -/
theorem odd_monomial_flux (n : ℕ) (c d : ℕ →₀ ℂ)
    (hc : ∀ j, conj (c j)= -c j) (hd : ∀ j, conj (d j)= -d j) :
    symKernel (monomialWeight (2*n+1)) c d=boundaryFlux (2*n+1) c d := by
  have he := source_green_all_order (2*n+1) c d
  have hs : (-1:ℂ)^(2*n+1)= -1 := by rw [pow_succ,pow_mul]; norm_num
  rw [hs] at he
  unfold symKernel
  rw [monomial_kernel_right,monomial_kernel_reverse _ _ _ hc hd]
  linear_combination he

end
end CarryPrincipalFlow
