import EndpointFlux
namespace CarryPrincipalFlow
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000


/-- Boundary jets of the LITERAL principal input, not coefficients chosen from moments. -/
theorem principal_boundary_trace (p : ℕ) (a : ℝ) (k : ℕ) :
    sourceEndpoint (addressPower p (principalInput a k))=
      Complex.I*(((k:ℂ)+1)^3*differencePower 3 p+
        (a:ℂ)*((k:ℂ)+1)*(12*differencePower 3 p+differencePower 3 (p+2))) := by
  rw [principalInput,address_power_add,address_power_scale,address_power_scale,
    address_power_comp,map_add,map_smul,map_smul,endpoint_odd_power,endpoint_odd_power]
  simp only [smul_eq_mul,pow_one]
  push_cast
  ring

theorem principal_trace_zero (a : ℝ) (k : ℕ) : sourceEndpoint (principalInput a k)=0 := by
  have he := principal_boundary_trace 0 a k
  norm_num [difference_power_stirling,Nat.stirlingSecond,address_power_zero] at he
  exact he

theorem principal_trace_one (a : ℝ) (k : ℕ) :
    sourceEndpoint (addressPower 1 (principalInput a k))=Complex.I*(a:ℂ)*((k:ℂ)+1) := by
  rw [principal_boundary_trace]
  norm_num [difference_power_stirling,Nat.stirlingSecond]
  ring

theorem principal_trace_two (a : ℝ) (k : ℕ) :
    sourceEndpoint (addressPower 2 (principalInput a k))=10*Complex.I*(a:ℂ)*((k:ℂ)+1) := by
  rw [principal_boundary_trace]
  norm_num [difference_power_stirling,Nat.stirlingSecond]
  ring

theorem principal_trace_three (a : ℝ) (k : ℕ) :
    sourceEndpoint (addressPower 3 (principalInput a k))=
      Complex.I*(((k:ℂ)+1)^3+77*(a:ℂ)*((k:ℂ)+1)) := by
  rw [principal_boundary_trace]
  norm_num [difference_power_stirling,Nat.stirlingSecond]
  ring

/-- Euler response cancels because the SAME complete input has zero endpoint. -/
theorem principal_flux_first (a b : ℝ) (k : ℕ) :
    boundaryFlux 1 (principalInput a k) (principalInput b k)=0 := by
  simp [boundaryFlux,address_power_zero,principal_trace_zero]

/-- The cubic layer gives a slope product, with its ORIGINAL Green orientation. -/
theorem principal_flux_cubic (a b : ℝ) (k : ℕ) :
    boundaryFlux 3 (principalInput a k) (principalInput b k)=
      -(a:ℂ)*(b:ℂ)*((k:ℂ)+1)^2 := by
  norm_num [boundaryFlux,Finset.sum_range_succ,address_power_zero,
    principal_trace_zero,principal_trace_one,principal_trace_two]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The next layer retains BOTH value/slope crossings; it is NOT a square. -/
theorem principal_flux_quintic (a b : ℝ) (k : ℕ) :
    boundaryFlux 5 (principalInput a k) (principalInput b k)=
      -((a:ℂ)+(b:ℂ))*((k:ℂ)+1)^4-54*(a:ℂ)*(b:ℂ)*((k:ℂ)+1)^2 := by
  norm_num [boundaryFlux,Finset.sum_range_succ,address_power_zero,
    principal_trace_zero,principal_trace_one,principal_trace_two,principal_trace_three]
  simp only [map_ofNat]
  ring_nf
  norm_num [Complex.I_sq]
  ring

theorem principal_monomial_one (a b : ℝ) (k : ℕ) :
    symKernel (monomialWeight 1) (principalInput a k) (principalInput b k)=0 := by
  rw [show 1=2*0+1 by decide,odd_monomial_flux 0 _ _ (principal_imaginary a k) (principal_imaginary b k)]
  exact principal_flux_first a b k

theorem principal_monomial_three (a b : ℝ) (k : ℕ) :
    symKernel (monomialWeight 3) (principalInput a k) (principalInput b k)=
      -(a:ℂ)*(b:ℂ)*((k:ℂ)+1)^2 := by
  rw [show 3=2*1+1 by decide,odd_monomial_flux 1 _ _ (principal_imaginary a k) (principal_imaginary b k)]
  exact principal_flux_cubic a b k

theorem principal_monomial_five (a b : ℝ) (k : ℕ) :
    symKernel (monomialWeight 5) (principalInput a k) (principalInput b k)=
      -((a:ℂ)+(b:ℂ))*((k:ℂ)+1)^4-54*(a:ℂ)*(b:ℂ)*((k:ℂ)+1)^2 := by
  rw [show 5=2*2+1 by decide,odd_monomial_flux 2 _ _ (principal_imaginary a k) (principal_imaginary b k)]
  exact principal_flux_quintic a b k

end
end CarryPrincipalFlow
