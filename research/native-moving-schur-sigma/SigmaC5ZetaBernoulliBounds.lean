import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic

/-!
# Explicit rational bounds for the Bernoulli kernels in high-order Euler–Maclaurin

The periodic Bernoulli kernels are bounded through their Fourier series.  The
coarse constant `4 / 6^k` is enough for a high-order remainder at the C5 node
scale and uses only `π > 3` and the elementary `p`-series bound.
-/

namespace SigmaC5Zeta

open Complex

theorem natPowSeries_le_two (k : ℕ) (hk : 2 ≤ k) :
    ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ k) ≤ 2 := by
  have hk1 : 1 < k := by omega
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) :=
    Real.summable_one_div_nat_pow.mpr hk1
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℝ) ^ k)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) 1).mpr hbase
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-(k : ℝ))) (Set.Ici (1 : ℝ)) := by
    intro x hx y hy hxy
    have hx' : 0 < x := by linarith [Set.mem_Ici.mp hx]
    exact Real.rpow_le_rpow_of_nonpos hx' hxy (neg_nonpos.mpr (by positivity))
  have hintg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-(k : ℝ))) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by
      have hkR : 1 < (k : ℝ) := by exact_mod_cast hk1
      linarith) (by norm_num)
  have hnonneg : ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ t ^ (-(k : ℝ)) := by
    intro t ht
    have ht' : 0 < t := by linarith [Set.mem_Ioi.mp ht]
    exact Real.rpow_nonneg ht'.le _
  have hanti' : AntitoneOn (fun t : ℝ => t ^ (-(k : ℝ))) (Set.Ici ((1 : ℕ) : ℝ)) := by
    simpa using hanti
  have hintg' : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-(k : ℝ)))
      (Set.Ioi ((1 : ℕ) : ℝ)) := by simpa using hintg
  have hnonneg' : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ t ^ (-(k : ℝ)) := by
    simpa using hnonneg
  have htail := AntitoneOn.tsum_comp_add_le_integral (N := 1) hanti' hintg' hnonneg'
  have hint : ∫ t : ℝ in Set.Ioi (1 : ℝ), t ^ (-(k : ℝ)) = 1 / ((k : ℝ) - 1) := by
    rw [integral_Ioi_rpow_of_lt (by
      have hkR : 1 < (k : ℝ) := by exact_mod_cast hk1
      linarith) (by norm_num)]
    have he : -(k : ℝ) + 1 = -((k : ℝ) - 1) := by ring
    rw [he]
    have hkR : 1 < (k : ℝ) := by exact_mod_cast hk1
    field_simp [ne_of_gt (sub_pos.mpr hkR)]; simp
  have htail' : (∑' n : ℕ, 1 / ((n + 2 : ℝ) ^ k)) ≤ 1 := by
    calc
      _ = ∑' n : ℕ, ((n + 2 : ℝ) ^ (-(k : ℝ))) := by
        congr 1
        funext n
        rw [Real.rpow_neg, Real.rpow_natCast, one_div]
        positivity
      _ ≤ ∫ t : ℝ in Set.Ioi (1 : ℝ), t ^ (-(k : ℝ)) := by
        have hsumEq : (∑' n : ℕ, ((n + 2 : ℝ) ^ (-(k : ℝ)))) =
            ∑' n : ℕ, (((n + 1 + 1 : ℕ) : ℝ) ^ (-(k : ℝ))) := by
          apply tsum_congr
          intro n
          congr 1
          norm_cast
        rw [hsumEq]
        simpa only [Nat.cast_one] using htail
      _ = 1 / ((k : ℝ) - 1) := hint
      _ ≤ 1 := by
        have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
        have hk' : 1 ≤ (k : ℝ) - 1 := by linarith
        exact (div_le_iff₀ (by linarith : 0 < (k : ℝ) - 1)).2 (by linarith)
  calc
    _ = 1 + ∑' n : ℕ, 1 / ((n + 2 : ℝ) ^ k) := by
      rw [← hsum.sum_add_tsum_nat_add 1]
      simp [Nat.cast_add, Nat.cast_one]
      apply tsum_congr
      intro n
      congr 1; ring
    _ ≤ 1 + 1 := add_le_add le_rfl htail'
    _ = 2 := by norm_num

set_option maxHeartbeats 1000000 in
theorem bernoulliFun_abs_le_four_factorial_div_six_pow
    {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun k x| ≤ 4 * (k.factorial : ℝ) / 6 ^ k := by
  let a : ℕ → ℂ := fun n =>
    1 / (n : ℂ) ^ k * (fourier n (x : UnitAddCircle) + (-1 : ℂ) ^ k * fourier (-n) (x : UnitAddCircle))
  have hfourier (n : ℤ) : ‖fourier n (x : UnitAddCircle)‖ = 1 := by
    rw [fourier_coe_apply]
    simp [Complex.norm_exp]
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) :=
    Real.summable_one_div_nat_pow.mpr (by omega : 1 < k)
  have hseries : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℝ) ^ k)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) 1).mpr hbase
  have hdom : Summable (fun n : ℕ => (2 : ℝ) / ((n + 1 : ℝ) ^ k)) := by
    have hfun : (fun n : ℕ => (2 : ℝ) / ((n + 1 : ℝ) ^ k)) =
        fun n : ℕ => 2 * (1 / ((n + 1 : ℝ) ^ k)) := by
      funext n
      ring
    rw [hfun]
    exact hseries.mul_left 2
  have hshift_bound (n : ℕ) : ‖a (n + 1)‖ ≤ 2 / ((n + 1 : ℝ) ^ k) := by
    dsimp [a]
    rw [norm_mul]
    have hden : ‖(1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ k‖ = 1 / ((n + 1 : ℝ) ^ k) := by
      norm_num; norm_cast
    rw [hden]
    calc
      1 / ((n + 1 : ℝ) ^ k) * ‖fourier (n + 1) (x : UnitAddCircle) + (-1 : ℂ) ^ k * fourier (-(n + 1)) (x : UnitAddCircle)‖
          ≤ 1 / ((n + 1 : ℝ) ^ k) *
            (‖fourier (n + 1) (x : UnitAddCircle)‖ + ‖(-1 : ℂ) ^ k * fourier (-(n + 1)) (x : UnitAddCircle)‖) :=
              mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = 2 / ((n + 1 : ℝ) ^ k) := by
        rw [hfourier (n + 1), norm_mul, norm_pow, norm_neg, norm_one,
          hfourier (-(n + 1))]
        ring
  have htailNorm : Summable (fun n : ℕ => ‖a (n + 1)‖) :=
    hdom.of_nonneg_of_le (fun n => norm_nonneg _) hshift_bound
  have hnorm : Summable (fun n : ℕ => ‖a n‖) :=
    (summable_nat_add_iff (f := fun n : ℕ => ‖a n‖) 1).mp htailNorm
  have hnormsum : ‖∑' n : ℕ, a n‖ ≤ 4 := by
    have hzero : ‖a 0‖ = 0 := by
      have hk0 : k ≠ 0 := by omega
      dsimp only [a]
      rw [Nat.cast_zero, zero_pow hk0]
      simp
    have hmajor := Summable.tsum_le_tsum hshift_bound htailNorm hdom
    have hp := natPowSeries_le_two k hk
    have hmajor' : (∑' n : ℕ, 2 / ((n + 1 : ℝ) ^ k)) ≤ 4 := by
      have heq : (fun n : ℕ => (2 : ℝ) / ((n + 1 : ℝ) ^ k)) =
          fun n : ℕ => 2 * (1 / ((n + 1 : ℝ) ^ k)) := by funext n; ring
      rw [show ∑' n : ℕ, 2 / ((n + 1 : ℝ) ^ k) =
        ∑' n : ℕ, 2 * (1 / ((n + 1 : ℝ) ^ k)) by rw [heq]]
      rw [tsum_mul_left]
      nlinarith
    calc
      ‖∑' n : ℕ, a n‖ ≤ ∑' n : ℕ, ‖a n‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' n : ℕ, ‖a (n + 1)‖ := by
        rw [← hnorm.sum_add_tsum_nat_add 1]
        simp [hzero]
      _ ≤ ∑' n : ℕ, 2 / ((n + 1 : ℝ) ^ k) := hmajor
      _ ≤ 4 := hmajor'
  have hfourierSum := hasSum_one_div_nat_pow_mul_fourier hk hx
  have hcoef : ‖-(2 * Real.pi * Complex.I) ^ k / (k.factorial : ℂ)‖ =
      (2 * Real.pi) ^ k / (k.factorial : ℝ) := by
    simp only [norm_div, norm_neg, norm_pow, norm_mul, Complex.norm_I,
      Complex.norm_two, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hfourierEq : ‖-(2 * Real.pi * Complex.I) ^ k / (k.factorial : ℂ) *
      (bernoulliFun k x : ℂ)‖ ≤ 4 := by
    calc
      _ = ‖∑' n : ℕ, a n‖ := by
        rw [← hfourierSum.tsum_eq]
      _ ≤ 4 := hnormsum
  have hfourierEq' : (2 * Real.pi) ^ k / (k.factorial : ℝ) *
      |bernoulliFun k x| ≤ 4 := by
    simpa only [norm_mul, hcoef, Complex.norm_real, Real.norm_eq_abs] using hfourierEq
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hden : 0 < (2 * Real.pi) ^ k := by positivity
  have hbound : |bernoulliFun k x| ≤ 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
    apply (le_div_iff₀ hden).2
    calc
      |bernoulliFun k x| * (2 * Real.pi) ^ k =
          ((2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x|) *
            (k.factorial : ℝ) := by
        field_simp [ne_of_gt hfac]
      _ ≤ 4 * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_right hfourierEq' hfac.le
  have hpi : 6 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc
    |bernoulliFun k x| ≤ 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k := hbound
    _ ≤ 4 * (k.factorial : ℝ) / 6 ^ k := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by norm_num) hpi k

end SigmaC5Zeta

#print axioms SigmaC5Zeta.natPowSeries_le_two
#print axioms SigmaC5Zeta.bernoulliFun_abs_le_four_factorial_div_six_pow
