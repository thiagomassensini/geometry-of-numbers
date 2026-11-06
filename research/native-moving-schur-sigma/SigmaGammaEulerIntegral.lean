import Mathlib

/-!
# Uniform Euler-integral approximation for the original Gamma factor in C5

The finite evaluator below comes directly from the Euler integral for
`Complex.Gamma`. The compact-interval Taylor remainder and the infinite tail
are both retained. The C5 Cauchy domain has `Re (w / 2) ≥ 1495 / 20000`; at
`N = 512`, `T = 81` this gives a uniform error below `10⁻³²`.

This is the analytic bridge from `Complex.Gamma` to a finite expression. It
does not yet enclose that finite expression in rational boxes.
-/

namespace SigmaC5Gamma

open MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2048

/-- Truncated Taylor polynomial for `exp (-x)`, with complex coefficients. -/
def expHead (N : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, (-(x : ℂ)) ^ k / (k.factorial : ℂ)

/-- The integral of the Taylor polynomial against the original Gamma kernel. -/
def gammaHeadIntegral (N : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in 0..T, expHead N x * (x : ℂ) ^ (z - 1)

/-- Finite closed form obtained by integrating each Taylor term. -/
def gammaFinite (N : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (T : ℂ) ^ z * ∑ k ∈ Finset.range N,
    (-(T : ℂ)) ^ k / ((k.factorial : ℂ) * (z + k))

theorem exp_head_error (N : ℕ) (T x : ℝ) (hx : 0 ≤ x) (hxT : x ≤ T)
    (hN : T / (N + 1 : ℕ) ≤ 1 / 2) :
    ‖(Real.exp (-x) : ℂ) - expHead N x‖ ≤ 2 * T ^ N / (N.factorial : ℝ) := by
  have hn : ‖(-(x : ℂ))‖ = x := by simp [abs_of_nonneg hx]
  have h := Complex.exp_bound' (x := -(x : ℂ)) (n := N) (by
    rw [hn]
    exact (div_le_div_of_nonneg_right hxT (by positivity)).trans hN)
  rw [hn] at h
  have he : (Real.exp (-x) : ℂ) = Complex.exp (-(x : ℂ)) := by simp
  rw [he, expHead]
  apply h.trans
  calc
    x ^ N / (N.factorial : ℝ) * 2 ≤ T ^ N / (N.factorial : ℝ) * 2 := by gcongr
    _ = 2 * T ^ N / (N.factorial : ℝ) := by ring

theorem gamma_tail_bound (T : ℝ) (hT : 1 ≤ T) (z : ℂ)
    (hz1 : z.re ≤ 1) :
    ‖∫ x : ℝ in Ioi T, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ ≤ Real.exp (-T) := by
  rw [← integral_exp_neg_Ioi T]
  apply MeasureTheory.norm_integral_le_of_norm_le (integrableOn_exp_neg_Ioi T)
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with x hx
  have hx1 : 1 ≤ x := hT.trans hx.le
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x)]
  have hp : x ^ ((z - 1).re) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hx1
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  simpa using mul_le_mul_of_nonneg_left hp (Real.exp_pos (-x)).le

theorem gamma_compact_error (N : ℕ) (T : ℝ) (hT : 1 ≤ T)
    (hN : T / (N + 1 : ℕ) ≤ 1 / 2) (z : ℂ) (hz : 0 < z.re) (hz1 : z.re ≤ 1) :
    ‖(∫ x : ℝ in 0..T, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)) -
      gammaHeadIntegral N T z‖ ≤ 2 * T ^ (N + 1) / ((N.factorial : ℝ) * z.re) := by
  have hT0 : 0 ≤ T := by linarith
  have hi : IntervalIntegrable (fun x : ℝ => (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0]
    exact (Complex.GammaIntegral_convergent hz).mono_set Ioc_subset_Ioi_self
  have hp : IntervalIntegrable (fun x : ℝ => expHead N x * (x : ℂ) ^ (z - 1)) volume 0 T := by
    apply IntervalIntegrable.continuousOn_mul
      (intervalIntegral.intervalIntegrable_cpow' (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith))
    unfold expHead
    fun_prop
  rw [gammaHeadIntegral, ← intervalIntegral.integral_sub hi hp]
  let C : ℝ := 2 * T ^ N / (N.factorial : ℝ)
  have hb : ‖∫ x : ℝ in 0..T,
      (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1) - expHead N x * (x : ℂ) ^ (z - 1)‖ ≤
      ∫ x : ℝ in 0..T, C * x ^ (z.re - 1) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT0
    · filter_upwards with x hx
      rw [← sub_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      simpa only [Complex.sub_re, Complex.one_re] using
        mul_le_mul_of_nonneg_right (exp_head_error N T x hx.1.le hx.2 hN)
          (Real.rpow_nonneg hx.1.le _)
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C
  apply hb.trans
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  have hz0 : z.re ≠ 0 := hz.ne'
  rw [sub_add_cancel, Real.zero_rpow hz0, sub_zero]
  have he : T ^ z.re ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT hz1
  have hc : 0 ≤ C := by dsimp [C]; positivity
  calc
    C * (T ^ z.re / z.re) ≤ C * (T / z.re) := by gcongr
    _ = 2 * T ^ (N + 1) / ((N.factorial : ℝ) * z.re) := by
      dsimp [C]
      rw [pow_succ]
      ring

theorem gamma_integral_approx_error (N : ℕ) (T : ℝ) (hT : 1 ≤ T)
    (hN : T / (N + 1 : ℕ) ≤ 1 / 2) (z : ℂ) (hz : 0 < z.re) (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma z - gammaHeadIntegral N T z‖ ≤
      2 * T ^ (N + 1) / ((N.factorial : ℝ) * z.re) + Real.exp (-T) := by
  have hT0 : 0 ≤ T := by linarith
  have hf := Complex.GammaIntegral_convergent hz
  have he : Complex.Gamma z =
      (∫ x : ℝ in 0..T, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)) +
      ∫ x : ℝ in Ioi T, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1) := by
    rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral,
      intervalIntegral.integral_of_le hT0]
    rw [← setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hT0))]
    rw [Ioc_union_Ioi_eq_Ioi hT0]
  let A : ℂ := ∫ x : ℝ in 0..T, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)
  let B : ℂ := ∫ x : ℝ in Ioi T, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)
  have he' : Complex.Gamma z = A + B := by simpa [A, B] using he
  rw [he']
  have hA : ‖A - gammaHeadIntegral N T z‖ ≤
      2 * T ^ (N + 1) / ((N.factorial : ℝ) * z.re) := by
    simpa [A] using gamma_compact_error N T hT hN z hz hz1
  have hB : ‖B‖ ≤ Real.exp (-T) := by
    simpa [B] using gamma_tail_bound T hT z hz1
  calc
    ‖(A + B) - gammaHeadIntegral N T z‖ = ‖(A - gammaHeadIntegral N T z) + B‖ := by
      congr 1
      abel_nf
    _ ≤ ‖A - gammaHeadIntegral N T z‖ + ‖B‖ := norm_add_le _ _
    _ ≤ 2 * T ^ (N + 1) / ((N.factorial : ℝ) * z.re) + Real.exp (-T) :=
      add_le_add hA hB

theorem euler_term (k : ℕ) (z : ℂ) (x : ℝ) (hx : 0 < x) :
    (-(x : ℂ)) ^ k / (k.factorial : ℂ) * (x : ℂ) ^ (z - 1) =
      (-1 : ℂ) ^ k / (k.factorial : ℂ) * (x : ℂ) ^ (z + k - 1) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [show z + (k : ℂ) - 1 = (k : ℂ) + (z - 1) by ring,
    Complex.cpow_add _ _ hx0, Complex.cpow_natCast, neg_pow]
  ring

theorem gamma_head_integral_formula (N : ℕ) (T : ℝ) (hT : 0 < T)
    (z : ℂ) (hz : 0 < z.re) : gammaHeadIntegral N T z = gammaFinite N T z := by
  have he : gammaHeadIntegral N T z = ∫ x : ℝ in 0..T,
      ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k / (k.factorial : ℂ) * (x : ℂ) ^ (z + k - 1) := by
    unfold gammaHeadIntegral expHead
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    have hx' : 0 < x := by simpa [min_eq_left hT.le] using hx.1
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => euler_term k z x hx')
  rw [he, intervalIntegral.integral_finsetSum]
  · unfold gammaFinite
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hzk : z + (k : ℂ) ≠ 0 := by
      intro hh
      have hr := congrArg Complex.re hh
      simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hr
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    rw [intervalIntegral.integral_const_mul,
      integral_cpow (Or.inl (by
        simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
        linarith [Nat.cast_nonneg (α := ℝ) k])),
      sub_add_cancel, Complex.ofReal_zero, Complex.zero_cpow hzk, sub_zero,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hT.ne'),
      Complex.cpow_natCast, neg_pow]
    field_simp
    ring
  · intro k hk
    exact (intervalIntegral.intervalIntegrable_cpow' (by
      simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
      linarith [Nat.cast_nonneg (α := ℝ) k])).const_mul _

theorem gamma_finite_error (N : ℕ) (T : ℝ) (hT : 1 ≤ T)
    (hN : T / (N + 1 : ℕ) ≤ 1 / 2) (z : ℂ) (hz : 0 < z.re) (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma z - gammaFinite N T z‖ ≤
      2 * T ^ (N + 1) / ((N.factorial : ℝ) * z.re) + Real.exp (-T) := by
  rw [← gamma_head_integral_formula N T (by linarith) z hz]
  exact gamma_integral_approx_error N T hT hN z hz hz1

theorem exp_neg_eighty_one_bound : Real.exp (-81) ≤ 1 / 10 ^ 33 := by
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : (8 / 3 : ℝ) ^ 81 ≤ (Real.exp 1) ^ 81 := pow_le_pow_left₀ (by norm_num) he 81
  rw [show (-81 : ℝ) = -((81 : ℕ) * (1 : ℝ)) by norm_num,
    Real.exp_neg, Real.exp_nat_mul]
  calc
    ((Real.exp 1) ^ 81)⁻¹ ≤ ((8 / 3 : ℝ) ^ 81)⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (8 / 3) ^ 81) hp
    _ ≤ 1 / 10 ^ 33 := by norm_num

theorem exp_neg_two_hundred_forty_bound : Real.exp (-240) ≤ 1 / 10 ^ 100 := by
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : (8 / 3 : ℝ) ^ 240 ≤ (Real.exp 1) ^ 240 := pow_le_pow_left₀ (by norm_num) he 240
  have hlarge : (10 : ℝ) ^ 100 ≤ (8 / 3 : ℝ) ^ 240 := by
    have h20 : (3 * 10 ^ 8 : ℝ) ≤ (8 / 3 : ℝ) ^ 20 := by norm_num
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 8) h20 12
    calc
      (10 : ℝ) ^ 100 ≤ (3 * 10 ^ 8 : ℝ) ^ 12 := by norm_num
      _ ≤ ((8 / 3 : ℝ) ^ 20) ^ 12 := hpow
      _ = (8 / 3 : ℝ) ^ 240 := by rw [← pow_mul]
  rw [show (-240 : ℝ) = -((240 : ℕ) * (1 : ℝ)) by norm_num,
    Real.exp_neg, Real.exp_nat_mul]
  calc
    ((Real.exp 1) ^ 240)⁻¹ ≤ ((8 / 3 : ℝ) ^ 240)⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (8 / 3) ^ 240) hp
    _ ≤ 1 / 10 ^ 100 := by
      rw [one_div, inv_le_inv₀ (by positivity : (0 : ℝ) < (8 / 3) ^ 240)
        (by positivity : (0 : ℝ) < (10 : ℝ) ^ 100)]
      exact hlarge

/-- Uniform error for the C5 Gamma argument on the complete Cauchy rectangle. -/
theorem gamma_finite_512_error (z : ℂ) (hz : (1495 / 20000 : ℝ) ≤ z.re)
    (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma z - gammaFinite 512 81 z‖ ≤ 1 / 10 ^ 32 := by
  have hmain := gamma_finite_error 512 81 (by norm_num) (by norm_num) z
    (by linarith [hz]) hz1
  have hcoef : 2 / z.re ≤ 27 := by
    have hzpos : 0 < z.re := by positivity
    apply (div_le_iff₀ hzpos).2
    have hlower : (2 : ℝ) ≤ 27 * z.re := by nlinarith [hz]
    linarith
  have hfirst : 2 * (81 : ℝ) ^ 513 / ((Nat.factorial 512 : ℝ) * z.re) ≤
      27 * (81 : ℝ) ^ 513 / (Nat.factorial 512 : ℝ) := by
    have hrewrite :
        2 * (81 : ℝ) ^ 513 / ((Nat.factorial 512 : ℝ) * z.re) =
          (2 / z.re) * ((81 : ℝ) ^ 513 / (Nat.factorial 512 : ℝ)) := by ring
    calc
      _ = (2 / z.re) * ((81 : ℝ) ^ 513 / (Nat.factorial 512 : ℝ)) := hrewrite
      _ ≤ 27 * ((81 : ℝ) ^ 513 / (Nat.factorial 512 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  have hsmall : 27 * (81 : ℝ) ^ 513 / (Nat.factorial 512 : ℝ) ≤ 1 / 10 ^ 98 := by
    norm_num1
  have hsum := add_le_add (hfirst.trans hsmall) exp_neg_eighty_one_bound
  exact hmain.trans (hsum.trans (by norm_num))

/-- Higher precision version for C5 coefficient extraction. -/
theorem gamma_finite_1024_240_error (z : ℂ) (hz : (1495 / 20000 : ℝ) ≤ z.re)
    (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma z - gammaFinite 1024 240 z‖ ≤ 1 / 10 ^ 99 := by
  have hmain := gamma_finite_error 1024 240 (by norm_num) (by norm_num) z
    (by linarith [hz]) hz1
  have hcoef : 2 / z.re ≤ 27 := by
    have hzpos : 0 < z.re := by positivity
    apply (div_le_iff₀ hzpos).2
    have hlower : (2 : ℝ) ≤ 27 * z.re := by nlinarith [hz]
    linarith
  have hfirst : 2 * (240 : ℝ) ^ 1025 / ((Nat.factorial 1024 : ℝ) * z.re) ≤
      27 * (240 : ℝ) ^ 1025 / (Nat.factorial 1024 : ℝ) := by
    have hrewrite :
        2 * (240 : ℝ) ^ 1025 / ((Nat.factorial 1024 : ℝ) * z.re) =
          (2 / z.re) * ((240 : ℝ) ^ 1025 / (Nat.factorial 1024 : ℝ)) := by ring
    calc
      _ = (2 / z.re) * ((240 : ℝ) ^ 1025 / (Nat.factorial 1024 : ℝ)) := hrewrite
      _ ≤ 27 * ((240 : ℝ) ^ 1025 / (Nat.factorial 1024 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  have hsmall : 27 * (240 : ℝ) ^ 1025 / (Nat.factorial 1024 : ℝ) ≤
      1 / 10 ^ 120 := by norm_num1
  have hsum := add_le_add (hfirst.trans hsmall) exp_neg_two_hundred_forty_bound
  exact hmain.trans (hsum.trans (by norm_num))

end
end SigmaC5Gamma
