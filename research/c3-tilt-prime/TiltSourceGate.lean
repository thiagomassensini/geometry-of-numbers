import NativeTiltJets
import SourceGate

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator CarrySourceBezout CarrySourceDimensionThree
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def carrierCoefficient (M n : ℕ) : ℝ :=
  ((iteratedDeriv (2*n) (fun u : ℝ => CarryTwoEvenJets.valueMultiplier (u:ℂ) *
    (1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter u) +
      CarryC3Tail.c3Boundary (fun j => CarryC3Tail.c3Sample j (u:ℂ)) (3*M+2) +
        CarryC3Tail.acceleratedC3Tail M (u:ℂ))) 0) / ((2*n).factorial:ℂ)).re

theorem carrierCoefficient_eq_native (M n : ℕ) : carrierCoefficient M n = nativeC n := by
  unfold carrierCoefficient
  rw [← native_even_coefficient_carrier_boundary_tail M n]
  simp

theorem carrierCoefficient_eq (M : ℕ) : carrierCoefficient M = nativeC := by
  funext n
  exact carrierCoefficient_eq_native M n

theorem even_pivot_gate_carrier (M : ℕ) (hA : IsUnit (sourceMomentMatrix nativeH 0 2)) :
    0 < sourceMomentSchur nativeH 0 2 ↔
      carrierCoefficient M 5 < evenSourceCeiling (carrierCoefficient M)/(5*carrierCoefficient M 0) := by
  rw [carrierCoefficient_eq]
  exact native_even_gate hA

theorem odd_pivot_gate_carrier (M : ℕ) (hA : IsUnit (sourceMomentMatrix nativeH 1 2)) :
    0 < sourceMomentSchur nativeH 1 2 ↔
      carrierCoefficient M 6 < oddSourceCeiling (carrierCoefficient M)/(6*carrierCoefficient M 0) := by
  rw [carrierCoefficient_eq]
  exact native_odd_gate hA

theorem carrier_coefficient_zero_pos (M : ℕ) : 0 < carrierCoefficient M 0 := by
  rw [carrierCoefficient_eq_native]
  exact native_source_c0_positive_from_boxes

theorem carrier_coefficient_one_negative (M : ℕ) : carrierCoefficient M 1 < -(1/100:ℝ) := by
  rw [carrierCoefficient_eq_native]
  exact native_source_c1_negative

#print axioms carrier_coefficient_zero_pos
#print axioms carrier_coefficient_one_negative
#print axioms carrierCoefficient_eq_native
#print axioms even_pivot_gate_carrier
#print axioms odd_pivot_gate_carrier
end
end CarryTiltSlice
