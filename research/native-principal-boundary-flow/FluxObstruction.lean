import NativePrincipalFlux
namespace CarryPrincipalFlow
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000


/-- Source-independent sign of the ORIENTED cubic response layer. -/
theorem oriented_cubic_value (v a : ℝ) (k : ℕ) :
    (((k:ℂ)+1)*symKernel (responseHead 0 (-v) 0 k) (principalInput a k) (principalInput a k)).re=v*a^2 := by
  have he : ((k:ℂ)+1)*symKernel (responseHead 0 (-v) 0 k) (principalInput a k) (principalInput a k)=
      ((v*a^2:ℝ):ℂ) := by
    rw [principal_head_flux]
    push_cast
    ring
  exact congrArg Complex.re he

theorem oriented_cubic_nonnegative (v a : ℝ) (hv : 0 ≤ v) (k : ℕ) :
    0 ≤ (((k:ℂ)+1)*symKernel (responseHead 0 (-v) 0 k) (principalInput a k) (principalInput a k)).re := by
  rw [oriented_cubic_value]
  exact mul_nonneg hv (sq_nonneg a)

/-- The NEXT layer has the opposite orientation. This is an actual response
basis layer of the SAME original principal input, not the full native response. -/
theorem oriented_quintic_value (q a : ℝ) (k : ℕ) :
    (((k:ℂ)+1)*symKernel (responseHead 0 0 q k) (principalInput a k) (principalInput a k)).re=
      -2*q*a-54*q*a^2/((k:ℝ)+1)^2 := by
  have he : ((k:ℂ)+1)*symKernel (responseHead 0 0 q k) (principalInput a k) (principalInput a k)=
      ((-2*q*a-54*q*a^2/((k:ℝ)+1)^2:ℝ):ℂ) := by
    rw [principal_head_flux]
    push_cast
    ring
  exact congrArg Complex.re he

theorem oriented_quintic_negative (q a : ℝ) (hq : 0<q) (ha : 0<a) (k : ℕ) :
    (((k:ℂ)+1)*symKernel (responseHead 0 0 q k) (principalInput a k) (principalInput a k)).re<0 := by
  rw [oriented_quintic_value]
  have hpos : 0<2*q*a := by positivity
  have hnon : 0 ≤ 54*q*a^2/((k:ℝ)+1)^2 := by positivity
  linarith

/-- A concrete check in the ORIGINAL X coefficients and metric: -56 exactly. -/
theorem raw_quintic_counterexample :
    (symKernel (monomialWeight 5) (principalInput 1 0) (principalInput 1 0)).re= -56 := by
  rw [principal_monomial_five]
  norm_num

/-- Positive weights do not force positive native Cauchy/Green readout.
This refutes only that general inference; it is NOT a counterexample to the
full completed response, whose remaining layers are retained above. -/
theorem positive_weight_not_sufficient :
    ∃ w : ℕ → ℂ, (∀ j, 0<(w j).re ∧ (w j).im=0) ∧
      (symKernel w (principalInput 1 0) (principalInput 1 0)).re<0 := by
  refine ⟨monomialWeight 5,?_,?_⟩
  · intro j
    have he : monomialWeight 5 j=((((1+j:ℕ):ℝ)^5:ℝ):ℂ) := by
      simp [monomialWeight,add_comm]
    rw [he]
    constructor
    · change 0<((1+j:ℕ):ℝ)^5
      positivity
    · rfl
  · rw [raw_quintic_counterexample]
    norm_num

end
end CarryPrincipalFlow
