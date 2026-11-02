import CriticalTiltSlice
import NativeRepartition64
import FiniteEvaluationError

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator CarrySourceBezout Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem height_parameter_real (t : ℝ) : operatorHeightParameter (t:ℂ) = criticalParameter t := by
  simp [operatorHeightParameter,criticalParameter]

theorem chart_line_eq_seed_carrier (M : ℕ) (t : ℝ) :
    finiteBracketedDirichletChart 3 M (operatorHeightParameter (t:ℂ)) =
      1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter t) := by
  rw [height_parameter_real,finiteBracketedDirichletChart_three_eq_one_add_trace,finite_bracket_line]

theorem physical_head_line (M : ℕ) (t : ℝ) :
    (NativeTrace.headTrace M (t:ℂ)).1 = NativeTrace.valueMultiplier (t:ℂ) *
      (1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter t)) := by
  rw [NativeTrace.head_value_formula,chart_line_eq_seed_carrier]

theorem accelerated_head_line (M : ℕ) (t : ℝ) :
    CarryC3Tail.acceleratedC3Head M (t:ℂ) =
      1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter t) +
        CarryC3Tail.c3Boundary (fun n => CarryC3Tail.c3Sample n (t:ℂ)) (3*M+2) := by
  rw [CarryC3Tail.acceleratedC3Head,chart_line_eq_seed_carrier]

theorem complete_c3_line (M : ℕ) (t : ℝ) (ht : |t| < 1) :
    CarryC3Tail.fullC3Signal (t:ℂ) =
      1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter t) +
        CarryC3Tail.c3Boundary (fun n => CarryC3Tail.c3Sample n (t:ℂ)) (3*M+2) +
          CarryC3Tail.acceleratedC3Tail M (t:ℂ) := by
  have hn : ‖(t:ℂ)‖ < 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using ht
  rw [CarryC3Tail.native_c3_head_tail M (t:ℂ) hn,accelerated_head_line]

theorem physical_head_vertical_jets (M n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => (NativeTrace.headTrace M (u:ℂ)).1) t =
      iteratedDeriv n (fun u : ℝ => NativeTrace.valueMultiplier (u:ℂ) *
        (1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter u))) t := by
  have h : (fun u : ℝ => (NativeTrace.headTrace M (u:ℂ)).1) =
      (fun u : ℝ => NativeTrace.valueMultiplier (u:ℂ) *
        (1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter u))) := by
    funext u
    exact physical_head_line M u
  rw [h]

#print axioms chart_line_eq_seed_carrier
#print axioms physical_head_line
#print axioms complete_c3_line
#print axioms physical_head_vertical_jets
theorem completed_characteristic_line (M : ℕ) (t : ℝ) (ht : |t| < 1) :
    completedNativeOperatorCharacteristic (t:ℂ) =
      CarryTwoEvenJets.valueMultiplier (t:ℂ) *
        (1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter t) +
          CarryC3Tail.c3Boundary (fun n => CarryC3Tail.c3Sample n (t:ℂ)) (3*M+2) +
            CarryC3Tail.acceleratedC3Tail M (t:ℂ)) := by
  rw [CarryC3Tail.characteristic_c3_formula,complete_c3_line M t ht]

theorem completed_characteristic_vertical_jets (M n : ℕ) :
    iteratedDeriv n (fun u : ℝ => completedNativeOperatorCharacteristic (u:ℂ)) 0 =
      iteratedDeriv n (fun u : ℝ => CarryTwoEvenJets.valueMultiplier (u:ℂ) *
        (1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter u) +
          CarryC3Tail.c3Boundary (fun j => CarryC3Tail.c3Sample j (u:ℂ)) (3*M+2) +
            CarryC3Tail.acceleratedC3Tail M (u:ℂ))) 0 := by
  have hdom : {u : ℝ | |u| < 1} ∈ nhds (0:ℝ) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with u hu
    simpa [Metric.mem_ball,Real.dist_eq] using hu
  have h : (fun u : ℝ => completedNativeOperatorCharacteristic (u:ℂ)) =ᶠ[nhds 0]
      (fun u : ℝ => CarryTwoEvenJets.valueMultiplier (u:ℂ) *
        (1 + finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter u) +
          CarryC3Tail.c3Boundary (fun j => CarryC3Tail.c3Sample j (u:ℂ)) (3*M+2) +
            CarryC3Tail.acceleratedC3Tail M (u:ℂ))) := by
    filter_upwards [hdom] with u hu
    exact completed_characteristic_line M u hu
  exact Filter.EventuallyEq.iteratedDeriv_eq n h

#print axioms completed_characteristic_line
#print axioms completed_characteristic_vertical_jets

end
end CarryTiltSlice
