import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic

/-! Exact forward differences at the ORIGINAL positive nodes r+1.
No moments or physical states are used to define these coefficients. -/
namespace CarryBinomialGreen
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators

/-- Original forward stencil, evaluated before choosing a moment sequence. -/
def difference (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (fwdDiff (1 : ℝ))^[n] f x

theorem difference_succ (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    difference (n+1) f x = difference n f (x+1)-difference n f x := by
  simp only [difference, Function.iterate_succ_apply', fwdDiff]

/-- Discrete multiplication commutator; proved without a sign assumption. -/
theorem difference_mul_coordinate (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    difference (n+1) (fun z => z*f z) x =
      (x+(n+1))*difference (n+1) f x+(n+1)*difference n f x := by
  induction n generalizing x with
  | zero =>
    rw [difference_succ 0, difference_succ 0]
    simp only [difference, Function.iterate_zero, id_eq, Nat.cast_zero, zero_add]
    ring
  | succ n ih =>
    rw [difference_succ (n+1) (fun z => z*f z), ih, ih,
      difference_succ (n+1) f, difference_succ n f, difference_succ n f]
    push_cast
    ring

/-- Shifted power moments of the original binomial stencil. -/
def shiftedPower (n d : ℕ) : ℝ := difference n (fun z => z^d) 1

def triangular (n : ℕ) : ℝ := ((n:ℝ)+1)*((n:ℝ)+2)/2

def secondOffset (n : ℕ) : ℝ :=
  ((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)*(3*(n:ℝ)+4)/24

theorem shifted_power_sum (n d : ℕ) : shiftedPower n d =
    ∑ r ∈ Finset.range (n+1), (((-1:ℤ)^(n-r)*n.choose r : ℤ):ℝ)*(r+1)^d := by
  rw [shiftedPower, difference, fwdDiff_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro r _
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one]
  ring

theorem shifted_power_zero {n d : ℕ} (hd : d<n) : shiftedPower n d=0 := by
  exact congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R:=ℝ) hd) 1

theorem shifted_power_self (n : ℕ) : shiftedPower n n=(n.factorial:ℝ) := by
  exact congrFun (fwdDiff_iter_eq_factorial (R:=ℝ) (n:=n)) 1

theorem shifted_power_recurrence (n d : ℕ) :
    shiftedPower (n+1) (d+1)=(n+2)*shiftedPower (n+1) d+(n+1)*shiftedPower n d := by
  unfold shiftedPower
  have he : (1:ℝ)+((n:ℝ)+1)=(n:ℝ)+2 := by ring
  simpa only [pow_succ, mul_comm, he] using difference_mul_coordinate n (fun z => z^d) 1

theorem shifted_power_first (n : ℕ) :
    shiftedPower n (n+1)=(n.factorial:ℝ)*triangular n := by
  induction n with
  | zero => norm_num [shiftedPower,difference,triangular]
  | succ n ih =>
    rw [show n+1+1=(n+1)+1 by omega, shifted_power_recurrence,
      shifted_power_self, ih]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, triangular]
    ring

theorem shifted_power_second (n : ℕ) :
    shiftedPower n (n+2)=(n.factorial:ℝ)*secondOffset n := by
  induction n with
  | zero => norm_num [shiftedPower,difference,secondOffset]
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega, shifted_power_recurrence,
      show n+2=(n+1)+1 by omega, shifted_power_first, ih]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      triangular, secondOffset]
    ring

end
end CarryBinomialGreen
