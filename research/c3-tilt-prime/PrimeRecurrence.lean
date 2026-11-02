import NativeTiltJets

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem prime_depth_coefficient_recurrence (n : ℕ) :
    (nativeC 0 : ℂ)*primeDepthCompletedNativeResponseTaylorCoefficient (2*n+1) +
      ∑ k ∈ Finset.range n,
        primeDepthCompletedNativeResponseTaylorCoefficient (2*k+1) * (nativeC (n-k) : ℂ) =
      -((n+1:ℕ):ℂ)*(nativeC (n+1):ℂ) := by
  have he := congrArg Complex.ofReal (canonicalCompletedNativeLogDerivativeMoment_real_recurrence n)
  push_cast at he
  simpa only [canonicalCompletedNativeLogDerivativeMoment_eq_primeDepthResponse, Nat.cast_add, Nat.cast_one] using he

#print axioms prime_depth_coefficient_recurrence
end
end CarryTiltSlice
