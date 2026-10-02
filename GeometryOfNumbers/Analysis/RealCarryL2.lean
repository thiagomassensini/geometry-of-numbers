import GeometryOfNumbers.Analysis.RealCarryGreenKernel
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Real vertical Hilbert space and causal shifts

Real rewrite of the historical vertical construction; no prime specialization.
The parameter eta is vertical and independent of center-leg deformation.
-/

open scoped BigOperators lp ENNReal NNReal

namespace GeometryOfNumbers.Analysis.RealCarry

noncomputable section

abbrev CarryVerticalL2 := ℓ²(ℕ, ℝ)

def carryVerticalL2BackwardShiftLinear (r : ℕ) :
    CarryVerticalL2 →ₗ[ℝ] CarryVerticalL2 where
  toFun x :=
    ⟨fun n => x (n + r), by
      change Memℓp (fun n : ℕ => x (n + r)) 2
      rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      exact (summable_nat_add_iff r).2
        ((lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
  map_add' x y := by
    ext n
    rfl
  map_smul' c x := by
    ext n
    rfl

@[simp] theorem carryVerticalL2BackwardShiftLinear_apply
    (r : ℕ) (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2BackwardShiftLinear r x n = x (n + r) := rfl

theorem carryVerticalL2BackwardShiftLinear_norm_le
    (r : ℕ) (x : CarryVerticalL2) :
    ‖carryVerticalL2BackwardShiftLinear r x‖ ≤ ‖x‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp]
  rw [lp.norm_rpow_eq_tsum hp, lp.norm_rpow_eq_tsum hp]
  simp only [carryVerticalL2BackwardShiftLinear_apply]
  have hx : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp x).summable hp
  have hsplit := hx.sum_add_tsum_nat_add r
  rw [← hsplit]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun n hn => by positivity)

def carryVerticalL2BackwardShift (r : ℕ) :
    CarryVerticalL2 →L[ℝ] CarryVerticalL2 :=
  LinearMap.mkContinuous (carryVerticalL2BackwardShiftLinear r) 1
    (fun x => by
      change ‖carryVerticalL2BackwardShiftLinear r x‖ ≤ 1 * ‖x‖
      simpa using carryVerticalL2BackwardShiftLinear_norm_le r x)

@[simp] theorem carryVerticalL2BackwardShift_apply
    (r : ℕ) (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2BackwardShift r x n = x (n + r) := rfl

theorem carryVerticalL2BackwardShift_norm_le_one (r : ℕ) :
    ‖carryVerticalL2BackwardShift r‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  change ‖carryVerticalL2BackwardShiftLinear r x‖ ≤ 1 * ‖x‖
  simpa using carryVerticalL2BackwardShiftLinear_norm_le r x

theorem carryVerticalL2BackwardShift_single (r k : ℕ) :
    carryVerticalL2BackwardShift r (lp.single 2 k (1 : ℝ)) =
      if r ≤ k then lp.single 2 (k - r) (1 : ℝ) else 0 := by
  ext n
  by_cases hrk : r ≤ k
  · have hiff : n + r = k ↔ n = k - r := by omega
    simp [carryVerticalL2BackwardShift_apply, lp.single_apply,
      Pi.single_apply, hrk, hiff]
  · have hne : n + r ≠ k := by omega
    simp [carryVerticalL2BackwardShift_apply, lp.single_apply, hrk, hne]

def carryVerticalL2UnilateralShift (r : ℕ) :
    CarryVerticalL2 →L[ℝ] CarryVerticalL2 :=
  ContinuousLinearMap.adjoint (carryVerticalL2BackwardShift r)

@[simp] theorem carryVerticalL2UnilateralShift_apply
    (r : ℕ) (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2UnilateralShift r x n =
      if r ≤ n then x (n - r) else 0 := by
  have hinner :
      inner ℝ (lp.single 2 n (1 : ℝ))
          (carryVerticalL2UnilateralShift r x) =
        inner ℝ
          (carryVerticalL2BackwardShift r (lp.single 2 n (1 : ℝ))) x := by
    exact ContinuousLinearMap.adjoint_inner_right
      (carryVerticalL2BackwardShift r) (lp.single 2 n (1 : ℝ)) x
  by_cases hrn : r ≤ n
  · simpa [carryVerticalL2UnilateralShift,
      carryVerticalL2BackwardShift_single, hrn, lp.inner_single_left] using hinner
  · simpa [carryVerticalL2UnilateralShift,
      carryVerticalL2BackwardShift_single, hrn, lp.inner_single_left] using hinner

theorem carryVerticalL2UnilateralShift_norm_le_one (r : ℕ) :
    ‖carryVerticalL2UnilateralShift r‖ ≤ 1 := by
  calc
    ‖carryVerticalL2UnilateralShift r‖ =
        ‖carryVerticalL2BackwardShift r‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    _ ≤ 1 := carryVerticalL2BackwardShift_norm_le_one r

def carryVerticalL2ShiftFamily : CarryVerticalShiftFamily CarryVerticalL2 where
  shift := carryVerticalL2UnilateralShift
  norm_shift_le_one := carryVerticalL2UnilateralShift_norm_le_one

def carryVerticalL2WeightedGreen (eta : ℝ) :
    CarryVerticalL2 →L[ℝ] CarryVerticalL2 :=
  carryWeightedVerticalGreen carryVerticalL2ShiftFamily eta

end
end GeometryOfNumbers.Analysis.RealCarry
