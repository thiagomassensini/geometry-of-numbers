import GeometryOfNumbers.Analysis.RealDiscreteValve
import Mathlib.RingTheory.PowerSeries.Derivative

/-! # Formal discrete Green kernel and three-channel reconstruction

Local rewrite of the historical finite algebra; see SOURCE_PROVENANCE.md.
-/

namespace GeometryOfNumbers.Analysis.DiscreteValve

open PowerSeries

variable {R : Type*} [CommRing R]

theorem X_mul_mk_fdiff (f : ℕ → R) :
    X * mk (fdiff f) = (1 - X) * mk f - C (f 0) := by
  ext n
  cases n with
  | zero => simp
  | succ m =>
    simp only [sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_mk, coeff_C,
      Nat.succ_ne_zero, ↓reduceIte, fdiff, sub_zero]

theorem X_sq_mul_mk_bracket (f : ℕ → R) :
    X ^ 2 * mk (bracket f)
      = (1 - X) ^ 2 * mk f - (1 - X) * C (f 0) - X * C (fdiff f 0) := by
  have hb : bracket f = fdiff (fdiff f) := by
    funext j; rw [bracket_eq_fdiff_sub]; rfl
  rw [hb]
  linear_combination (X : R⟦X⟧) * X_mul_mk_fdiff (fdiff f) + (1 - X) * X_mul_mk_fdiff f

/-- Formal inverse of 1-X. -/
def geometricSeries : PowerSeries R := mk fun _ => 1

/-- Formal inverse of (1-X)^2, with coefficient n+1. -/
def greenKernelSeries : PowerSeries R := mk fun n => (n : R) + 1

theorem one_sub_X_mul_geometricSeries : (1 - X) * geometricSeries = (1 : R⟦X⟧) := by
  ext n
  cases n with
  | zero => simp [geometricSeries]
  | succ m =>
    simp only [geometricSeries, sub_mul, one_mul, map_sub, coeff_succ_X_mul,
      coeff_mk, coeff_one, Nat.succ_ne_zero, ↓reduceIte, sub_self]

theorem one_sub_X_mul_greenKernelSeries :
    (1 - X) * greenKernelSeries = (geometricSeries : R⟦X⟧) := by
  ext n
  cases n with
  | zero => simp [greenKernelSeries, geometricSeries]
  | succ m =>
    simp only [greenKernelSeries, geometricSeries, sub_mul, one_mul, map_sub,
      coeff_succ_X_mul, coeff_mk]
    push_cast; ring

theorem one_sub_X_sq_mul_greenKernelSeries :
    (1 - X) ^ 2 * greenKernelSeries = (1 : R⟦X⟧) := by
  rw [sq, mul_assoc, one_sub_X_mul_greenKernelSeries, one_sub_X_mul_geometricSeries]

theorem X_mul_greenKernelSeries :
    X * greenKernelSeries = mk (fun m => (m : R)) := by
  ext n
  cases n with
  | zero => simp [greenKernelSeries]
  | succ m =>
    simp only [greenKernelSeries, coeff_succ_X_mul, coeff_mk]
    push_cast; ring

theorem mk_greenSum (f : ℕ → R) :
    mk (fun n => greenSum f n) = X * greenKernelSeries * mk (bracket f) := by
  rw [X_mul_greenKernelSeries]
  ext n
  rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk, greenSum]
  rw [← Finset.sum_range_reflect (fun i => (i : R) * bracket f (n - i)) (n + 1),
    Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  rw [nsmul_eq_mul, Nat.sub_sub_self (le_of_lt hi')]

theorem mk_discrete_valve (f : ℕ → R) :
    mk f = C (f 0) * geometricSeries + X * C (fdiff f 0) * greenKernelSeries
      + X ^ 2 * greenKernelSeries * mk (bracket f) := by
  rw [← one_sub_X_mul_greenKernelSeries]
  linear_combination (-greenKernelSeries) * X_sq_mul_mk_bracket f
    - mk f * one_sub_X_sq_mul_greenKernelSeries (R := R)

end GeometryOfNumbers.Analysis.DiscreteValve
