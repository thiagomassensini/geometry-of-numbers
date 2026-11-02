import CriticalTiltBridge

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator CarrySourceBezout
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem native_even_coefficient_carrier_boundary_tail (M n : ℕ) :
    (nativeC n : ℂ) =
      (iteratedDeriv (2*n) (fun u : ℝ => CarryTwoEvenJets.valueMultiplier (u:ℂ) *
        (1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter u) +
          CarryC3Tail.c3Boundary (fun j => CarryC3Tail.c3Sample j (u:ℂ)) (3*M+2) +
            CarryC3Tail.acceleratedC3Tail M (u:ℂ))) 0) / ((2*n).factorial:ℂ) := by
  rw [← completedNativeEvenCharacteristicCoefficient_eq_real,
    ← completedNativeFullCharacteristicTaylorCoefficient_even]
  change NativeTrace.sourceJet (2*n) completedNativeOperatorCharacteristic = _
  unfold NativeTrace.sourceJet
  have he := iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal (2*n) 0
  norm_num only [Complex.ofReal_zero] at he
  rw [← he]
  rw [completed_characteristic_vertical_jets]

#print axioms native_even_coefficient_carrier_boundary_tail
end
end CarryTiltSlice
