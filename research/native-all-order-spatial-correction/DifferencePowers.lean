import CarrySelfAdjointOperator.NewtonStirlingTransport
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Choose.Cast

namespace CarrySpatialCorrection
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- An auxiliary finite difference at sample 1, with the ORIGINAL factorial. -/
def differencePower (m p : ℕ) : ℂ :=
  (m.factorial : ℂ)⁻¹ * (fwdDiff (1 : ℕ))^[m] (fun k => (k : ℂ)^p) 1

/-- The complex-valued version of the existing Newton-basis delta identity. -/
theorem choose_difference_zero (j m : ℕ) :
    (fwdDiff (1 : ℕ))^[m] (fun k => (k.choose j : ℂ)) 0 =
      if m=j then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (fwdDiff_iter_choose_zero j m)
  simpa only [fwdDiff_iter_eq_sum_shift, zsmul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_ite, Int.cast_zero, Int.cast_natCast] using h

/-- Evaluation at 1 keeps precisely the two adjacent Newton coefficients. -/
theorem choose_difference_one (j m : ℕ) :
    (fwdDiff (1 : ℕ))^[m] (fun k => (k.choose j : ℂ)) 1 =
      (if m=j then 1 else 0) + (if m+1=j then 1 else 0) := by
  cases j with
  | zero =>
    cases m with
    | zero => simp
    | succ m =>
      simp only [Nat.choose_zero_right, Nat.cast_one]
      rw [Function.iterate_succ_apply]
      simp only [fwdDiff_const]
      simp [fwdDiff_iter_eq_sum_shift]
  | succ j =>
    have hs : (fun k : ℕ => ((k+1).choose (j+1) : ℂ)) =
        (fun k : ℕ => (k.choose (j+1) : ℂ)) + (fun k : ℕ => (k.choose j : ℂ)) := by
      funext k
      simp only [Pi.add_apply, Nat.choose_succ_succ', Nat.cast_add]
      ring
    have hc := fwdDiff_iter_comp_add (1 : ℕ)
      (fun k : ℕ => (k.choose (j+1) : ℂ)) 1 m 0
    rw [hs, fwdDiff_iter_add] at hc
    simpa only [Pi.add_apply, choose_difference_zero, Nat.succ.injEq, zero_add] using hc.symm

/-- Reuses the native Newton/Stirling combinatorial identity, without reading
any characteristic or canonical moment. -/
theorem power_newton_expansion (p : ℕ) :
    (fun k : ℕ => (k : ℂ)^p) =
      ∑ j ∈ Finset.range (p+1),
        ((Nat.stirlingSecond p j : ℂ)*(j.factorial : ℂ)) •
          (fun k : ℕ => (k.choose j : ℂ)) := by
  funext k
  have h := CarrySelfAdjointOperator.ProjectiveDepth.pow_eq_sum_stirlingSecond_descFactorial p k
  simp only [Nat.descFactorial_eq_factorial_mul_choose] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_pow,
    Nat.cast_sum, Nat.cast_mul, mul_assoc] using congrArg (fun z : ℕ => (z : ℂ)) h

/-- Closed evaluation of the finite difference; these are auxiliary Stirling
coefficients, not a replacement sequence of canonical moments. -/
theorem difference_power_stirling (m p : ℕ) :
    differencePower m p = (Nat.stirlingSecond (p+1) (m+1) : ℂ) := by
  unfold differencePower
  rw [power_newton_expansion]
  simp only [fwdDiff_iter_finsetSum, fwdDiff_iter_const_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, choose_difference_one, mul_add, Finset.sum_add_distrib]
  have hd (j : ℕ) :
      (∑ k ∈ Finset.range (p+1),
        (Nat.stirlingSecond p k : ℂ)*(k.factorial : ℂ)*(if j=k then 1 else 0)) =
        (Nat.stirlingSecond p j : ℂ)*(j.factorial : ℂ) := by
    by_cases hj : j < p+1
    · simp [mul_ite, Finset.mem_range, hj]
    · have hz : Nat.stirlingSecond p j=0 := Nat.stirlingSecond_eq_zero_of_lt (by omega)
      simp [mul_ite, Finset.mem_range, hj, hz]
  rw [hd, hd, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
  push_cast
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp
  ring

theorem difference_power_below {m p : ℕ} (hp : p < m) : differencePower m p=0 := by
  rw [difference_power_stirling, Nat.stirlingSecond_eq_zero_of_lt (by omega), Nat.cast_zero]

theorem difference_power_diagonal (m : ℕ) : differencePower m m=1 := by
  simp only [difference_power_stirling, Nat.stirlingSecond_self, Nat.cast_one]

/-- Exact binomial formula with the same factorial as the native stencil. -/
theorem difference_power_sum (m p : ℕ) :
    differencePower m p = (m.factorial : ℂ)⁻¹ *
      ∑ j ∈ Finset.range (m+1),
        (((-1 : ℤ)^(m-j)*(m.choose j : ℤ) : ℤ) : ℂ) * ((j+1 : ℕ) : ℂ)^p := by
  unfold differencePower
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Nat.cast_id, add_comm 1]

/-- First excess degree after the exact stencil cancellations. -/
def slope (m : ℕ) : ℂ := ((m:ℂ)+1)*((m:ℂ)+2)/2
/-- Second excess degree after the exact stencil cancellations. -/
def curvature (m : ℕ) : ℂ := ((m:ℂ)+1)*((m:ℂ)+2)*((m:ℂ)+3)*(3*(m:ℂ)+4)/24

theorem difference_power_one_above (m : ℕ) : differencePower m (m+1)=slope m := by
  rw [difference_power_stirling, Nat.stirlingSecond_succ_self_left, Nat.cast_choose_two]
  push_cast
  unfold slope
  ring

theorem stirling_two_above (m : ℕ) :
    (Nat.stirlingSecond (m+3) (m+1) : ℂ)=curvature m := by
  induction m with
  | zero => norm_num [curvature, Nat.stirlingSecond]
  | succ m ih =>
    rw [show m+1+3=(m+3)+1 by omega, Nat.stirlingSecond_succ_succ]
    rw [show m+1+1=m+2 by omega, Nat.stirlingSecond_succ_self_left]
    push_cast
    rw [Nat.cast_choose_two, ih]
    unfold curvature
    push_cast
    ring

theorem difference_power_two_above (m : ℕ) : differencePower m (m+2)=curvature m := by
  rw [difference_power_stirling]
  exact stirling_two_above m

end
end CarrySpatialCorrection
