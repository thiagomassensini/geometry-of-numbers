import PrimeRecurrence
import TiltSourceGate

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem prime_depth_carrier_recurrence (M n : ℕ) :
    (carrierCoefficient M 0 : ℂ)*primeDepthCompletedNativeResponseTaylorCoefficient (2*n+1) +
      ∑ k ∈ Finset.range n,
        primeDepthCompletedNativeResponseTaylorCoefficient (2*k+1) * (carrierCoefficient M (n-k) : ℂ) =
      -((n+1:ℕ):ℂ)*(carrierCoefficient M (n+1):ℂ) := by
  simpa only [carrierCoefficient_eq_native] using prime_depth_coefficient_recurrence n

#print axioms prime_depth_carrier_recurrence
end
end CarryTiltSlice
