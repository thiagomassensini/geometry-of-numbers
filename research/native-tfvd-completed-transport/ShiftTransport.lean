import NativeSynthesis
import GeometryOfNumbers.Analysis.RealCarryTfvd
import CarrySelfAdjointOperator.NativePhysicalGreenResolvent

namespace CarryNativeTfvd
open CarrySelfAdjointOperator CarryVerticalSynthesis
open CPFormal.Analytic.Cp (NativeGpreTowerHilbert)
open GeometryOfNumbers.Analysis.RealCarry
open scoped BigOperators InnerProductSpace lp ENNReal
open Filter Topology
noncomputable section
set_option autoImplicit false

theorem vertical_shift_basis (j : ℕ) :
    carryVerticalL2UnilateralShift 1 (lp.single 2 j (1 : ℝ)) =
      lp.single 2 (j + 1) (1 : ℝ) := by
  apply lp.ext; funext n
  by_cases hn : 1 ≤ n
  · have he : n - 1 = j ↔ n = j + 1 := by omega
    simp [carryVerticalL2UnilateralShift_apply, lp.single_apply, Pi.single_apply, hn, he]
  · have he : n ≠ j + 1 := by omega
    simp [carryVerticalL2UnilateralShift_apply, lp.single_apply, hn, he]

/-- Forward transport of the native vertical shift, on the whole original tower. -/
theorem native_synthesis_shift (X : NativeGpreTowerHilbert) :
    nativeSynthesis (carryVerticalL2UnilateralShift 1 X) =
      NativeLaguerre.physicalRadialAdvance (nativeSynthesis X) := by
  have hc : IsClosed {Y : NativeGpreTowerHilbert |
      nativeSynthesis (carryVerticalL2UnilateralShift 1 Y) =
        NativeLaguerre.physicalRadialAdvance (nativeSynthesis Y)} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  refine finite_tower_dense.induction_on X hc ?_
  intro c
  classical
  simp only [finiteTower, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, ContinuousLinearMap.map_smul_of_tower, vertical_shift_basis, native_synthesis_column,
    NativeLaguerre.physicalRadialAdvance_feature]

/-- The inverse-direction shift retains its center trace; no inverse multiplier
or bounded coefficient recovery is assumed. -/
theorem vertical_shift_backward_trace (X : NativeGpreTowerHilbert) :
    carryVerticalL2UnilateralShift 1 (carryVerticalL2BackwardShift 1 X) =
      X - (X 0) • lp.single 2 0 (1 : ℝ) := by
  apply lp.ext; funext n
  cases n with
  | zero => simp [carryVerticalL2UnilateralShift_apply, lp.single_apply]
  | succ n =>
    simp [carryVerticalL2UnilateralShift_apply, carryVerticalL2BackwardShift_apply,
      lp.single_apply]

theorem native_backward_numerator (X : NativeGpreTowerHilbert) :
    NativeLaguerre.physicalRadialAdvance
      (nativeSynthesis (carryVerticalL2BackwardShift 1 X)) =
      nativeSynthesis X - (X 0) • completedNativeChiralCauchyFeature 0 := by
  rw [← native_synthesis_shift, vertical_shift_backward_trace, map_sub,
    map_smul, native_synthesis_column]

/-- Exact source coefficient valve, including BOTH initial traces. -/
theorem vertical_numerator_two_traces (eta : ℝ) (heta : eta ≠ 0)
    (X : NativeGpreTowerHilbert) :
    X - (2 * eta) • carryVerticalL2UnilateralShift 1 X +
      eta ^ 2 • carryVerticalL2UnilateralShift 1 (carryVerticalL2UnilateralShift 1 X) =
    eta • carryVerticalL2UnilateralShift 1 (carryWeightedVerticalCenteredBracket eta X) +
      (X 0) • lp.single 2 0 (1 : ℝ) +
      (X 1 - 2 * eta * X 0) • lp.single 2 1 (1 : ℝ) := by
  apply lp.ext; funext n
  rcases n with _ | _ | n
  · simp [carryVerticalL2UnilateralShift_apply, lp.single_apply]
  · simp [carryVerticalL2UnilateralShift_apply, lp.single_apply,
      carryWeightedVerticalCenteredBracket_zero]
  · simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, carryVerticalL2UnilateralShift_apply]
    simp [carryWeightedVerticalCenteredBracket_succ, lp.single_apply,
      Nat.add_assoc]
    field_simp [heta]

end
end CarryNativeTfvd
