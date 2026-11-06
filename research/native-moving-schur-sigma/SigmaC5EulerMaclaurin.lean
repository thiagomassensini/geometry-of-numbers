import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
import SigmaC5ZetaBernoulliBounds

open intervalIntegral MeasureTheory Complex Filter
open scoped Topology

namespace SigmaC5Zeta

noncomputable section
set_option autoImplicit false

/-- A normalized Bernoulli kernel on a unit interval. -/
def emBernoulliKernel (a : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (bernoulliFun k (t - a) : ℂ) / (Nat.factorial k : ℂ)

/-- The Bernoulli-weighted integral of the `k`th derivative in a derivative sequence. -/
def emBernoulliIntegral (a : ℝ) (D : ℕ → ℝ → ℂ) (k : ℕ) : ℂ :=
  ∫ t in a..a + 1, emBernoulliKernel a k t * D k t

/-- The endpoint term produced by one Bernoulli integration by parts. -/
def emBernoulliBoundary (a : ℝ) (D : ℕ → ℝ → ℂ) (k : ℕ) : ℂ :=
  emBernoulliKernel a (k + 1) (a + 1) * D k (a + 1) -
    emBernoulliKernel a (k + 1) a * D k a

lemma hasDerivAt_emBernoulliKernel (a t : ℝ) (k : ℕ) :
    HasDerivAt (fun x => emBernoulliKernel a (k + 1) x) (emBernoulliKernel a k t) t := by
  have hshift : HasDerivAt (fun x : ℝ => x - a) 1 t := (hasDerivAt_id' t).sub_const a
  have hpoly := (hasDerivAt_bernoulliFun (k + 1) (t - a)).comp t hshift
  have hcast := hpoly.ofReal_comp
  have hdiv := hcast.div_const (Nat.factorial (k + 1) : ℂ)
  apply hdiv.congr_deriv
  simp only [emBernoulliKernel]
  rw [Nat.factorial_succ]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]

lemma emBernoulliKernel_continuous (a : ℝ) (k : ℕ) :
    Continuous (emBernoulliKernel a k) := by
  unfold emBernoulliKernel
  exact (Complex.continuous_ofReal.comp
    ((continuous_bernoulliFun k).comp (continuous_id.sub continuous_const))).div_const _

set_option maxHeartbeats 1000000 in
lemma emBernoulliStep {a : ℝ} {D : ℕ → ℝ → ℂ}
    (hD : ∀ k t, t ∈ Set.uIcc a (a + 1) →
      HasDerivAt (D k) (D (k + 1) t) t) (k : ℕ) :
    emBernoulliIntegral a D k =
      emBernoulliBoundary a D k - emBernoulliIntegral a D (k + 1) := by
  have hDcont (j : ℕ) : ContinuousOn (D j) (Set.uIcc a (a + 1)) := by
    intro t ht
    exact (hD j t ht).continuousAt.continuousWithinAt
  have hkercont (j : ℕ) : ContinuousOn (emBernoulliKernel a j) (Set.uIcc a (a + 1)) :=
    (emBernoulliKernel_continuous a j).continuousOn
  have hkerint (j : ℕ) : IntervalIntegrable (emBernoulliKernel a j) volume a (a + 1) :=
    (hkercont j).intervalIntegrable
  have hDint (j : ℕ) : IntervalIntegrable (D j) volume a (a + 1) :=
    (hDcont j).intervalIntegrable
  have hparts :
      (∫ t in a..a + 1, emBernoulliKernel a (k + 1) t * D (k + 1) t) =
        emBernoulliKernel a (k + 1) (a + 1) * D k (a + 1) -
          emBernoulliKernel a (k + 1) a * D k a -
            (∫ t in a..a + 1, emBernoulliKernel a k t * D k t) := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := a) (b := a + 1)
      (u := emBernoulliKernel a (k + 1)) (v := D k)
      (u' := emBernoulliKernel a k) (v' := D (k + 1))
      (fun t _ => hasDerivAt_emBernoulliKernel a t k)
      (fun t ht => hD k t ht)
      (hkerint k) (hDint (k + 1))
  have hparts' : emBernoulliIntegral a D (k + 1) =
      emBernoulliBoundary a D k - emBernoulliIntegral a D k := by
    simpa only [emBernoulliIntegral, emBernoulliBoundary] using hparts
  calc
    emBernoulliIntegral a D k =
        emBernoulliBoundary a D k -
          (emBernoulliBoundary a D k - emBernoulliIntegral a D k) := by
      simp only [sub_sub_cancel]
    _ = emBernoulliBoundary a D k - emBernoulliIntegral a D (k + 1) := by
      rw [← hparts']

lemma emBernoulliIntegral_zero (a : ℝ) (D : ℕ → ℝ → ℂ) :
    emBernoulliIntegral a D 0 = ∫ t in a..a + 1, D 0 t := by
  simp [emBernoulliIntegral, emBernoulliKernel]

lemma emBernoulliBoundary_zero (a : ℝ) (D : ℕ → ℝ → ℂ) :
    emBernoulliBoundary a D 0 = (D 0 (a + 1) + D 0 a) / 2 := by
  have h1 : a + 1 - a = 1 := by ring
  simp [emBernoulliBoundary, emBernoulliKernel, h1, bernoulliFun_one]
  ring

lemma emBernoulliBoundary_even_zero {a : ℝ} {D : ℕ → ℝ → ℂ} {p : ℕ}
    (hp : 1 ≤ p) : emBernoulliBoundary a D (2 * p) = 0 := by
  have hodd : Odd (2 * p + 1) := ⟨p, by omega⟩
  have hlt : 1 < 2 * p + 1 := by omega
  have hber : bernoulli (2 * p + 1) = 0 := bernoulli_eq_zero_of_odd hodd hlt
  have hzero : bernoulliFun (2 * p + 1) 0 = 0 := by
    simpa [bernoulliFun_eval_zero] using hber
  have hone : bernoulliFun (2 * p + 1) 1 = 0 := by
    rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), hzero]
  have h1 : a + 1 - a = 1 := by ring
  simp [emBernoulliBoundary, emBernoulliKernel, h1, hzero, hone]

lemma emBernoulliKernel_norm_le_four_div_six_pow {a t : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (ht : t ∈ Set.uIcc a (a + 1)) :
    ‖emBernoulliKernel a k t‖ ≤ 4 / 6 ^ k := by
  have hab : a ≤ a + 1 := by linarith
  have ht' : t - a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hab] at ht
    rw [Set.mem_Icc]
    constructor <;> linarith [ht.1, ht.2]
  have hB := bernoulliFun_abs_le_four_factorial_div_six_pow hk ht'
  have hfac : 0 < (Nat.factorial k : ℝ) := by positivity
  unfold emBernoulliKernel
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  calc
    |bernoulliFun k (t - a)| / (Nat.factorial k : ℝ) ≤
        (4 * (Nat.factorial k : ℝ) / 6 ^ k) / (Nat.factorial k : ℝ) :=
      div_le_div_of_nonneg_right hB hfac.le
    _ = 4 / 6 ^ k := by field_simp

lemma emBernoulliIntegral_norm_le {a : ℝ} {D : ℕ → ℝ → ℂ} {k : ℕ} {M : ℝ}
    (hk : 2 ≤ k)
    (hDcont : ContinuousOn (D k) (Set.uIcc a (a + 1)))
    (hDbound : ∀ t ∈ Set.Icc a (a + 1), ‖D k t‖ ≤ M) :
    ‖emBernoulliIntegral a D k‖ ≤ (4 / 6 ^ k) * M := by
  have hab : a ≤ a + 1 := by linarith
  have hkernel : ContinuousOn (emBernoulliKernel a k) (Set.uIcc a (a + 1)) :=
    (emBernoulliKernel_continuous a k).continuousOn
  have hprod : IntervalIntegrable
      (fun t => emBernoulliKernel a k t * D k t) volume a (a + 1) :=
    (hkernel.mul hDcont).intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ => (4 / 6 ^ k) * M) volume a (a + 1) :=
    intervalIntegrable_const
  calc
    ‖emBernoulliIntegral a D k‖ ≤
        ∫ t in a..a + 1, ‖emBernoulliKernel a k t * D k t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..a + 1, (4 / 6 ^ k) * M := by
      apply intervalIntegral.integral_mono_on hab hprod.norm hconst
      intro t ht
      have htI : t ∈ Set.Icc a (a + 1) := by
        simpa [Set.uIcc_of_le hab] using ht
      have htU : t ∈ Set.uIcc a (a + 1) := by
        simpa [Set.uIcc_of_le hab] using htI
      rw [norm_mul]
      exact mul_le_mul
        (emBernoulliKernel_norm_le_four_div_six_pow hk htU)
        (hDbound t htI) (norm_nonneg _) (by positivity)
    _ = (4 / 6 ^ k) * M := by
      rw [intervalIntegral.integral_const]
      simp [show a + 1 - a = 1 by ring]

/-- The rising factorial `(s)_k`, kept as a finite product. -/
noncomputable def emPochhammer (s : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (s + (j : ℂ))

/-- The `k`th derivative of `x ↦ x^{-s}` on the positive real axis. -/
noncomputable def emZetaDerivative (s : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  (-1 : ℂ) ^ k * emPochhammer s k * (x : ℂ) ^ (-s - (k : ℂ))

/-- The `j`th even Bernoulli coefficient, with the factorial normalization. -/
noncomputable def emBernoulliCoefficient (j : ℕ) : ℂ :=
  (bernoulli (2 * j + 2) : ℂ) / (Nat.factorial (2 * j + 2) : ℂ)

lemma hasDerivAt_emZetaDerivative {s : ℂ} {x : ℝ} (hs : 0 < s.re) (hx : 0 < x)
    (k : ℕ) :
    HasDerivAt (emZetaDerivative s k) (emZetaDerivative s (k + 1) x) x := by
  let r : ℂ := -s - (k : ℂ)
  have hr : r ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [r] at hre
    linarith
  have hpow := hasDerivAt_ofReal_cpow_const (x := x) (r := r)
    hx.ne' hr
  have hconst := hpow.const_mul ((-1 : ℂ) ^ k * emPochhammer s k)
  have hexp : r - 1 = -s - ((k + 1 : ℕ) : ℂ) := by
    simp only [r]
    push_cast
    ring
  have hcoeff : (-1 : ℂ) ^ k * emPochhammer s k * r =
      (-1 : ℂ) ^ (k + 1) * emPochhammer s (k + 1) := by
    simp only [emPochhammer, Finset.prod_range_succ]
    ring
  apply hconst.congr_deriv
  calc
    (-1 : ℂ) ^ k * emPochhammer s k * (r * (x : ℂ) ^ (r - 1)) =
        ((-1 : ℂ) ^ k * emPochhammer s k * r) * (x : ℂ) ^ (r - 1) := by ring
    _ = ((-1 : ℂ) ^ (k + 1) * emPochhammer s (k + 1)) *
        (x : ℂ) ^ (-s - ((k + 1 : ℕ) : ℂ)) := by rw [hcoeff, hexp]
    _ = emZetaDerivative s (k + 1) x := by rfl

lemma emBernoulliBoundary_eq_coefficient {a : ℝ} {D : ℕ → ℝ → ℂ} (j : ℕ) :
    emBernoulliBoundary a D (2 * j + 1) =
      emBernoulliCoefficient j * (D (2 * j + 1) (a + 1) - D (2 * j + 1) a) := by
  have hshift : a + 1 - a = 1 := by ring
  have h0 : emBernoulliKernel a (2 * j + 2) a = emBernoulliCoefficient j := by
    simp [emBernoulliKernel, emBernoulliCoefficient, bernoulliFun_eval_zero]
  have h1 : emBernoulliKernel a (2 * j + 2) (a + 1) = emBernoulliCoefficient j := by
    simp [emBernoulliKernel, emBernoulliCoefficient, hshift,
      bernoulliFun_endpoints_eq_of_ne_one (by omega : 2 * j + 2 ≠ 1),
      bernoulliFun_eval_zero]
  simp only [emBernoulliBoundary, h0, h1]
  ring

lemma emZetaDerivative_norm_eq {s : ℂ} {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ‖emZetaDerivative s k x‖ =
      ‖(-1 : ℂ) ^ k * emPochhammer s k‖ * x ^ (-s.re - (k : ℝ)) := by
  rw [emZetaDerivative, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1

noncomputable def emZetaRemainder (s : ℂ) (P n : ℕ) : ℂ :=
  emBernoulliIntegral (n : ℝ) (emZetaDerivative s) (2 * P)

/-- A closed-form Euler–Maclaurin block: one integral cell minus its trapezoid,
plus the first `P` Bernoulli boundary corrections. -/
noncomputable def emZetaHighBlock (s : ℂ) (P : ℕ) (x : ℝ) : ℂ :=
  ((((x + 1 : ℝ) : ℂ) ^ (1 - s) - (x : ℂ) ^ (1 - s)) / (1 - s))
    - ((x : ℂ) ^ (-s) + ((x + 1 : ℝ) : ℂ) ^ (-s)) / 2
    + ∑ j ∈ Finset.range P, emBernoulliBoundary x (emZetaDerivative s) (2 * j + 1)

theorem emZetaRemainder_norm_le {s : ℂ} (hs : 0 < s.re) {P n : ℕ}
    (hP : 1 ≤ P) (hn : 1 ≤ n) :
    ‖emZetaRemainder s P n‖ ≤
      (4 / 6 ^ (2 * P)) * ‖emPochhammer s (2 * P)‖ *
        (n : ℝ) ^ (-s.re - ((2 * P : ℕ) : ℝ)) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hab : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hDcont : ContinuousOn (emZetaDerivative s (2 * P))
      (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by
    intro t ht
    have htI : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
      simpa [Set.uIcc_of_le hab] using ht
    have htpos : 0 < t := lt_of_lt_of_le hnreal htI.1
    exact (hasDerivAt_emZetaDerivative hs htpos (2 * P)).continuousAt.continuousWithinAt
  have hcoeff : ‖(-1 : ℂ) ^ (2 * P) * emPochhammer s (2 * P)‖ =
      ‖emPochhammer s (2 * P)‖ := by
    rw [norm_mul, norm_pow, norm_neg, norm_one]
    simp
  have hDbound : ∀ t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1),
      ‖emZetaDerivative s (2 * P) t‖ ≤
        ‖emPochhammer s (2 * P)‖ *
          (n : ℝ) ^ (-s.re - ((2 * P : ℕ) : ℝ)) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hnreal ht.1
    have hexp : -s.re - ((2 * P : ℕ) : ℝ) ≤ 0 := by
      have hPpos : 0 ≤ ((2 * P : ℕ) : ℝ) := by positivity
      linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hnreal ht.1 hexp
    rw [emZetaDerivative_norm_eq htpos (2 * P), hcoeff]
    exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  have hbound := emBernoulliIntegral_norm_le (a := (n : ℝ))
    (D := emZetaDerivative s) (k := 2 * P)
    (M := ‖emPochhammer s (2 * P)‖ *
      (n : ℝ) ^ (-s.re - ((2 * P : ℕ) : ℝ))) (by omega) hDcont hDbound
  simpa [emZetaRemainder, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- Repeated integration by parts on a unit interval, in a form whose final term is the
normalized `2p`th Bernoulli integral. -/
theorem emBernoulliCell {a : ℝ} {D : ℕ → ℝ → ℂ}
    (hD : ∀ k t, t ∈ Set.uIcc a (a + 1) →
      HasDerivAt (D k) (D (k + 1) t) t) (p : ℕ) :
    emBernoulliIntegral a D 0 =
      (D 0 (a + 1) + D 0 a) / 2 -
        ∑ j ∈ Finset.range (p + 1), emBernoulliBoundary a D (2 * j + 1) +
        emBernoulliIntegral a D (2 * (p + 1)) := by
  induction p with
  | zero =>
      rw [Finset.sum_range_one]
      have h0 := emBernoulliStep (a := a) hD 0
      have h1 := emBernoulliStep (a := a) hD 1
      rw [emBernoulliBoundary_zero] at h0
      rw [h0, h1]
      ring
  | succ p ih =>
      have hp : 1 ≤ p + 1 := by omega
      have hEven := emBernoulliStep (a := a) hD (2 * (p + 1))
      rw [emBernoulliBoundary_even_zero hp] at hEven
      have hOdd := emBernoulliStep (a := a) hD (2 * (p + 1) + 1)
      have hEven' : emBernoulliIntegral a D (2 * (p + 1)) =
          0 - emBernoulliIntegral a D (2 * (p + 1) + 1) := hEven
      have hOdd' : emBernoulliIntegral a D (2 * (p + 1) + 1) =
          emBernoulliBoundary a D (2 * (p + 1) + 1) -
            emBernoulliIntegral a D (2 * (p + 2)) := by
        have hidx : 2 * (p + 2) = 2 * (p + 1) + 1 + 1 := by omega
        simpa only [hidx] using hOdd
      have hsum :
          (∑ j ∈ Finset.range (p + 2), emBernoulliBoundary a D (2 * j + 1)) =
            (∑ j ∈ Finset.range (p + 1), emBernoulliBoundary a D (2 * j + 1)) +
              emBernoulliBoundary a D (2 * (p + 1) + 1) := by
        simp only [show p + 2 = (p + 1) + 1 by omega, Finset.sum_range_succ]
      calc
        emBernoulliIntegral a D 0 =
            (D 0 (a + 1) + D 0 a) / 2 -
              ∑ j ∈ Finset.range (p + 1), emBernoulliBoundary a D (2 * j + 1) +
              emBernoulliIntegral a D (2 * (p + 1)) := ih
        _ = (D 0 (a + 1) + D 0 a) / 2 -
              ∑ j ∈ Finset.range (p + 2), emBernoulliBoundary a D (2 * j + 1) +
              emBernoulliIntegral a D (2 * (p + 2)) := by
          rw [hsum, hEven', hOdd']
          ring

theorem emZetaHighBlock_eq_remainder {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {P : ℕ} (hP : 1 ≤ P) {x : ℝ} (hx : 0 < x) :
    emZetaHighBlock s P x = emBernoulliIntegral x (emZetaDerivative s) (2 * P) := by
  have hab : x ≤ x + 1 := by linarith
  have hD : ∀ k t, t ∈ Set.uIcc x (x + 1) →
      HasDerivAt (emZetaDerivative s k) (emZetaDerivative s (k + 1) t) t := by
    intro k t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hasDerivAt_emZetaDerivative hs (lt_of_lt_of_le hx ht.1) k
  have hcell := emBernoulliCell (a := x) hD (P - 1)
  have hcell' : emBernoulliIntegral x (emZetaDerivative s) (2 * P) =
      (∫ t in x..x + 1, emZetaDerivative s 0 t) -
        (emZetaDerivative s 0 (x + 1) + emZetaDerivative s 0 x) / 2 +
        ∑ j ∈ Finset.range P,
          emBernoulliBoundary x (emZetaDerivative s) (2 * j + 1) := by
    simp only [Nat.sub_add_cancel hP] at hcell
    rw [emBernoulliIntegral_zero] at hcell
    linear_combination -hcell
  have hD0 (y : ℝ) : emZetaDerivative s 0 y = (y : ℂ) ^ (-s) := by
    simp [emZetaDerivative, emPochhammer]
  have hzero : (0 : ℝ) ∉ Set.uIcc x (x + 1) := by
    rw [Set.uIcc_of_le hab]
    simp only [Set.mem_Icc, not_and]
    intro h
    linarith
  have hI : (∫ t in x..x + 1, (t : ℂ) ^ (-s)) =
      (((x + 1 : ℝ) : ℂ) ^ (1 - s) - (x : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [integral_cpow (Or.inr ⟨fun h => hs1 (by linear_combination -h), hzero⟩)]
    rw [show -s + 1 = 1 - s by ring]
  calc
    emZetaHighBlock s P x =
        (∫ t in x..x + 1, emZetaDerivative s 0 t) -
          (emZetaDerivative s 0 (x + 1) + emZetaDerivative s 0 x) / 2 +
          ∑ j ∈ Finset.range P,
            emBernoulliBoundary x (emZetaDerivative s) (2 * j + 1) := by
      simp only [emZetaHighBlock, hI, hD0]
      ring
    _ = emBernoulliIntegral x (emZetaDerivative s) (2 * P) := hcell'.symm

private lemma summable_shift_rpow_c5 {q : ℝ} (hq : 1 < q) (N : ℕ) :
    Summable (fun k : ℕ => ((k + N : ℕ) : ℝ) ^ (-q)) := by
  have hbase : Summable (fun k : ℕ => (k : ℝ) ^ (-q)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ (-q)) N).mpr hbase |>.congr
    fun k => by push_cast; ring_nf

lemma tsum_shift_rpow_le {q : ℝ} (hq : 1 < q) {N : ℕ} (hN : 1 ≤ N) :
    (∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ (-q)) ≤
      (N : ℝ) ^ (-q) + (N : ℝ) ^ (1 - q) / (q - 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-q)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hanti₀ : AntitoneOn f (Set.Ioi 0) := by
    simpa [f] using Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -q ≤ 0)
  have hanti : AntitoneOn f (Set.Ici (N : ℝ)) := hanti₀.mono fun x hx =>
    lt_of_lt_of_le hNpos hx
  have hint : IntegrableOn f (Set.Ioi (N : ℝ)) := by
    simpa [f] using integrableOn_Ioi_rpow_of_lt (by linarith : -q < -1) hNpos
  have hnonneg : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ f t := by
    intro t ht
    have hNt : (N : ℝ) < t := ht
    exact Real.rpow_nonneg (by linarith [hNpos, hNt]) _
  have htail := hanti.tsum_comp_add_le_integral N hint hnonneg
  have hsum : Summable (fun k : ℕ => ((k + N : ℕ) : ℝ) ^ (-q)) :=
    summable_shift_rpow_c5 hq N
  have hsplit : (∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ (-q)) =
      (N : ℝ) ^ (-q) + ∑' k : ℕ, ((k + N + 1 : ℕ) : ℝ) ^ (-q) := by
    rw [hsum.tsum_eq_zero_add]
    congr 1
    · simp
    · apply tsum_congr
      intro k
      have hidx : k + 1 + N = k + N + 1 := by omega
      rw [hidx]
  have hinter : (∫ x in Set.Ioi (N : ℝ), f x) =
      (N : ℝ) ^ (1 - q) / (q - 1) := by
    rw [show f = fun x : ℝ => x ^ (-q) by rfl]
    rw [integral_Ioi_rpow_of_lt (by linarith : -q < -1) hNpos]
    rw [show -q + 1 = 1 - q by ring]
    rw [show q - 1 = -(1 - q) by ring, div_neg, neg_div]
  have htail' : (∑' k : ℕ, ((k + N + 1 : ℕ) : ℝ) ^ (-q)) ≤
      ∫ x in Set.Ioi (N : ℝ), f x := by
    simpa [f, Nat.cast_add] using htail
  calc
    (∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ (-q)) =
        (N : ℝ) ^ (-q) + ∑' k : ℕ, ((k + N + 1 : ℕ) : ℝ) ^ (-q) := hsplit
    _ ≤ (N : ℝ) ^ (-q) + ∫ x in Set.Ioi (N : ℝ), f x := by
      gcongr
    _ = (N : ℝ) ^ (-q) + (N : ℝ) ^ (1 - q) / (q - 1) := by rw [hinter]

theorem emZetaHighBlock_summable_norm {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {P N : ℕ} (hP : 1 ≤ P) (hN : 1 ≤ N) :
    Summable (fun k : ℕ => ‖emZetaHighBlock s P ((k + N : ℕ) : ℝ)‖) := by
  let q : ℝ := ((2 * P : ℕ) : ℝ) + s.re
  let C : ℝ := (4 / 6 ^ (2 * P)) * ‖emPochhammer s (2 * P)‖
  have hq : 1 < q := by
    have hP2 : 2 ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * P)
    dsimp [q]
    linarith
  have hsumm : Summable (fun k : ℕ => ((k + N : ℕ) : ℝ) ^ (-q)) :=
    summable_shift_rpow_c5 hq N
  have hmajor : Summable (fun k : ℕ => C * ((k + N : ℕ) : ℝ) ^ (-q)) :=
    hsumm.mul_left C
  have hbound : ∀ k : ℕ,
      ‖emZetaHighBlock s P ((k + N : ℕ) : ℝ)‖ ≤
        C * ((k + N : ℕ) : ℝ) ^ (-q) := by
    intro k
    have hn : 1 ≤ k + N := by omega
    have hb := emZetaHighBlock_eq_remainder hs hs1 hP
      (x := ((k + N : ℕ) : ℝ)) (by exact_mod_cast (show 0 < k + N by omega))
    rw [hb]
    have hr := emZetaRemainder_norm_le hs hP hn
    have hexp : -s.re - ((2 * P : ℕ) : ℝ) = -((2 * P : ℕ) : ℝ) - s.re := by ring
    rw [hexp] at hr
    have hexp' : -((2 * P : ℕ) : ℝ) - s.re =
        -s.re + -((2 * P : ℕ) : ℝ) := by ring
    rw [hexp'] at hr
    simpa [emZetaRemainder, C, q, mul_assoc] using hr
  exact hmajor.of_nonneg_of_le (fun k => norm_nonneg _) hbound

theorem emZetaHighTail_norm_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {P N : ℕ} (hP : 1 ≤ P) (hN : 1 ≤ N) :
    ‖∑' k : ℕ, emZetaHighBlock s P ((k + N : ℕ) : ℝ)‖ ≤
      (4 / 6 ^ (2 * P)) * ‖emPochhammer s (2 * P)‖ *
        ((N : ℝ) ^ (-(s.re + (2 * P : ℕ))) +
          (N : ℝ) ^ (1 - (s.re + (2 * P : ℕ))) /
            (s.re + (2 * P : ℕ) - 1)) := by
  let m : ℕ := 2 * P
  let q : ℝ := s.re + (m : ℝ)
  let C : ℝ := (4 / 6 ^ m) * ‖emPochhammer s m‖
  have hq : 1 < q := by
    have hm : 2 ≤ (m : ℝ) := by dsimp [m]; exact_mod_cast (show 2 ≤ 2 * P by omega)
    dsimp [q]
    linarith
  have hsum : Summable (fun k : ℕ => ((k + N : ℕ) : ℝ) ^ (-q)) :=
    summable_shift_rpow_c5 hq N
  have hblocksum := emZetaHighBlock_summable_norm hs hs1 hP hN
  have hpoint : ∀ k : ℕ,
      ‖emZetaHighBlock s P ((k + N : ℕ) : ℝ)‖ ≤
        C * ((k + N : ℕ) : ℝ) ^ (-q) := by
    intro k
    have hn : 1 ≤ k + N := by omega
    have hx : 0 < ((k + N : ℕ) : ℝ) := by exact_mod_cast (show 0 < k + N by omega)
    have hb := emZetaHighBlock_eq_remainder hs hs1 hP
      (x := ((k + N : ℕ) : ℝ)) hx
    have hr := emZetaRemainder_norm_le hs hP hn
    rw [hb]
    have hexp : -s.re - ((m : ℝ)) = -q := by dsimp [q, m]; ring
    have hconst : ((2 * P : ℕ) : ℝ) = (m : ℝ) := by rfl
    simpa [emZetaRemainder, C, q, m, hconst, hexp, mul_assoc] using hr
  have hC : 0 ≤ C := by positivity
  have htail := tsum_shift_rpow_le hq hN
  calc
    ‖∑' k : ℕ, emZetaHighBlock s P ((k + N : ℕ) : ℝ)‖ ≤
        ∑' k : ℕ, ‖emZetaHighBlock s P ((k + N : ℕ) : ℝ)‖ :=
      norm_tsum_le_tsum_norm hblocksum
    _ ≤ ∑' k : ℕ, C * ((k + N : ℕ) : ℝ) ^ (-q) :=
      hblocksum.tsum_le_tsum hpoint (hsum.mul_left C)
    _ = C * ∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ (-q) := by rw [← tsum_mul_left]
    _ ≤ C * ((N : ℝ) ^ (-q) + (N : ℝ) ^ (1 - q) / (q - 1)) :=
      mul_le_mul_of_nonneg_left htail hC
    _ = (4 / 6 ^ (2 * P)) * ‖emPochhammer s (2 * P)‖ *
        ((N : ℝ) ^ (-(s.re + (2 * P : ℕ))) +
          (N : ℝ) ^ (1 - (s.re + (2 * P : ℕ))) /
            (s.re + (2 * P : ℕ) - 1)) := by
      dsimp [C, q, m]

lemma emZetaDerivative_nat_eq (s : ℂ) (k n : ℕ) :
    emZetaDerivative s k (n : ℝ) =
      (-1 : ℂ) ^ k * emPochhammer s k * (n : ℂ) ^ (-(s + (k : ℂ))) := by
  rw [emZetaDerivative, show -s - (k : ℂ) = -(s + (k : ℂ)) by ring]
  norm_cast

lemma hasSum_shift_c5 {w : ℂ} (hw : 1 < w.re) (N : ℕ) :
    HasSum (fun k : ℕ => ((k + N : ℕ) : ℂ) ^ (-w))
      (riemannZeta w - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w)) := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ w) :=
    Complex.summable_one_div_nat_cpow.mpr hw
  have h : HasSum (fun n : ℕ => (n : ℂ) ^ (-w)) (riemannZeta w) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hw]
    convert hsum.hasSum using 1
    funext n
    rw [Complex.cpow_neg, one_div]
  exact (hasSum_nat_add_iff' N).mpr h

lemma hasSum_shift_succ_c5 {w : ℂ} (hw : 1 < w.re) (N : ℕ) :
    HasSum (fun k : ℕ => ((k + 1 + N : ℕ) : ℂ) ^ (-w))
      (riemannZeta w - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w) - (N : ℂ) ^ (-w)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_shift_c5 hw N)
  simpa [Finset.sum_range_one, add_comm, add_left_comm, add_assoc] using h

lemma emZetaBoundary_shift_hasSum {s : ℂ} (hs : 2 < s.re) (j N : ℕ) :
    HasSum (fun k : ℕ =>
      emBernoulliBoundary ((k + N : ℕ) : ℝ) (emZetaDerivative s) (2 * j + 1))
      (-emBernoulliCoefficient j * emZetaDerivative s (2 * j + 1) (N : ℝ)) := by
  let m : ℕ := 2 * j + 1
  let w : ℂ := s + (m : ℂ)
  let A : ℂ := (-1 : ℂ) ^ m * emPochhammer s m
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmw : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hw : 1 < w.re := by
    change 1 < s.re + (m : ℝ)
    linarith [hmw]
  have hdiff := (hasSum_shift_succ_c5 hw N).sub (hasSum_shift_c5 hw N)
  have hsum : HasSum (fun k : ℕ =>
      ((k + 1 + N : ℕ) : ℂ) ^ (-w) - ((k + N : ℕ) : ℂ) ^ (-w))
      (-((N : ℂ) ^ (-w))) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiff
  have hscaled := hsum.mul_left (emBernoulliCoefficient j * A)
  have hfun : (fun k : ℕ =>
      emBernoulliBoundary ((k + N : ℕ) : ℝ) (emZetaDerivative s) (2 * j + 1)) =
      fun k : ℕ => (emBernoulliCoefficient j * A) *
        (((k + 1 + N : ℕ) : ℂ) ^ (-w) - ((k + N : ℕ) : ℂ) ^ (-w)) := by
    funext k
    rw [emBernoulliBoundary_eq_coefficient]
    have hplus : ((k + N : ℕ) : ℝ) + 1 = ((k + N + 1 : ℕ) : ℝ) := by
      norm_cast
    rw [hplus, emZetaDerivative_nat_eq, emZetaDerivative_nat_eq]
    have hidx : k + N + 1 = k + 1 + N := by omega
    rw [hidx]
    simp only [m, w, A]
    ring
  have hval : (emBernoulliCoefficient j * A) * (-((N : ℂ) ^ (-w))) =
      -emBernoulliCoefficient j * emZetaDerivative s m (N : ℝ) := by
    simp only [A, w]
    rw [emZetaDerivative_nat_eq]
    ring
  rw [hfun, ← hval]
  exact hscaled

noncomputable def emZetaHighCorrection (s : ℂ) (P N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range P,
    -emBernoulliCoefficient j * emZetaDerivative s (2 * j + 1) (N : ℝ)

noncomputable def emZetaHighRHS (N P : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, (i : ℂ) ^ (-s) +
    (N : ℂ) ^ (1 - s) / (s - 1) +
    (N : ℂ) ^ (-s) / 2 + emZetaHighCorrection s P N -
    ∑' k : ℕ, emZetaHighBlock s P ((k + N : ℕ) : ℝ)

theorem zeta_em_high_of_two_lt {s : ℂ} (hs : 2 < s.re) {N P : ℕ} :
    riemannZeta s = emZetaHighRHS N P s := by
  let head : ℂ := ∑ i ∈ Finset.range N, (i : ℂ) ^ (-s)
  let gseq : ℕ → ℂ := fun k =>
    ((((k + 1 + N : ℕ) : ℂ) ^ (-(s - 1)) - ((k + N : ℕ) : ℂ) ^ (-(s - 1))) /
      (1 - s))
  let tseq : ℕ → ℂ := fun k =>
    (((k + N : ℕ) : ℂ) ^ (-s) + ((k + 1 + N : ℕ) : ℂ) ^ (-s)) / 2
  let bseq : ℕ → ℂ := fun k =>
    ∑ j ∈ Finset.range P,
      emBernoulliBoundary ((k + N : ℕ) : ℝ) (emZetaDerivative s) (2 * j + 1)
  have hA := hasSum_shift_c5 (w := s) (by linarith) N
  have hA1 := hasSum_shift_succ_c5 (w := s) (by linarith) N
  have hC := hasSum_shift_c5 (w := s - 1) (by simp; linarith) N
  have hC1 := hasSum_shift_succ_c5 (w := s - 1) (by simp; linarith) N
  have hG : HasSum gseq ((N : ℂ) ^ (1 - s) / (s - 1)) := by
    have hraw := (hC1.sub hC).div_const (1 - s)
    have hexp : -(s - 1) = 1 - s := by ring
    have hval :
        (riemannZeta (s - 1) - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-(s - 1)) -
          (N : ℂ) ^ (-(s - 1)) -
          (riemannZeta (s - 1) - ∑ i ∈ Finset.range N, (i : ℂ) ^ (-(s - 1)))) /
            (1 - s) = (N : ℂ) ^ (1 - s) / (s - 1) := by
      rw [hexp]
      have hs1 : (s - 1 : ℂ) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      have h1s : (1 - s : ℂ) ≠ 0 := by
        intro h
        apply hs1
        linear_combination -h
      field_simp [hs1, h1s]; ring
    rw [hval] at hraw
    change HasSum gseq ((N : ℂ) ^ (1 - s) / (s - 1))
    exact hraw
  have hT : HasSum tseq (riemannZeta s - head - (N : ℂ) ^ (-s) / 2) := by
    have hraw := (hA.add hA1).div_const (2 : ℂ)
    have hval :
        (riemannZeta s - head +
          (riemannZeta s - head - (N : ℂ) ^ (-s))) / 2 =
            riemannZeta s - head - (N : ℂ) ^ (-s) / 2 := by ring
    rw [hval] at hraw
    change HasSum tseq (riemannZeta s - head - (N : ℂ) ^ (-s) / 2)
    exact hraw
  have hBj : ∀ j ∈ Finset.range P,
      HasSum (fun k : ℕ =>
        emBernoulliBoundary ((k + N : ℕ) : ℝ) (emZetaDerivative s) (2 * j + 1))
        (-emBernoulliCoefficient j * emZetaDerivative s (2 * j + 1) (N : ℝ)) := by
    intro j hj
    exact emZetaBoundary_shift_hasSum hs j N
  have hBsum : Summable bseq := by
    apply summable_sum
    intro j hj
    exact (hBj j hj).summable
  have hBval : (∑' k : ℕ, bseq k) = emZetaHighCorrection s P N := by
    rw [Summable.tsum_finsetSum (fun j hj => (hBj j hj).summable)]
    change (∑ j ∈ Finset.range P, ∑' k : ℕ,
        emBernoulliBoundary ((k + N : ℕ) : ℝ) (emZetaDerivative s) (2 * j + 1)) =
      ∑ j ∈ Finset.range P,
        -emBernoulliCoefficient j * emZetaDerivative s (2 * j + 1) (N : ℝ)
    apply Finset.sum_congr rfl
    intro j hj
    exact (hBj j hj).tsum_eq
  have hB : HasSum bseq (emZetaHighCorrection s P N) := by
    rw [← hBval]
    exact hBsum.hasSum
  have hE := (hG.sub hT).add hB
  have hblock : (fun k : ℕ => emZetaHighBlock s P ((k + N : ℕ) : ℝ)) =
      fun k => gseq k - tseq k + bseq k := by
    funext k
    have hplus : ((((k + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) =
        ((k + 1 + N : ℕ) : ℂ) := by norm_cast; omega
    simp only [emZetaHighBlock, gseq, tseq, bseq]
    rw [hplus, show 1 - s = -(s - 1) by ring]
    push_cast
    ring
  rw [← hblock] at hE
  have hEtsum := hE.tsum_eq
  unfold emZetaHighRHS
  dsimp only [head] at hEtsum ⊢
  rw [hEtsum]
  ring

lemma differentiableAt_emPochhammer (k : ℕ) (s : ℂ) :
    DifferentiableAt ℂ (fun w => emPochhammer w k) s := by
  unfold emPochhammer
  fun_prop

lemma differentiableAt_emZetaDerivative {x : ℝ} (hx : 0 < x) (k : ℕ) (s : ℂ) :
    DifferentiableAt ℂ (fun w => emZetaDerivative w k x) s := by
  have hlin : DifferentiableAt ℂ (fun w : ℂ => -w - (k : ℂ)) s :=
    differentiableAt_id.neg.sub (differentiableAt_const _)
  have hpow := hlin.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  unfold emZetaDerivative
  exact ((differentiableAt_const _).mul (differentiableAt_emPochhammer k s)).mul hpow

lemma differentiableAt_emBernoulliBoundary {x : ℝ} (hx : 0 < x) (j : ℕ) (s : ℂ) :
    DifferentiableAt ℂ
      (fun w => emBernoulliBoundary x (emZetaDerivative w) (2 * j + 1)) s := by
  have hfun : (fun w => emBernoulliBoundary x (emZetaDerivative w) (2 * j + 1)) =
      fun w => emBernoulliCoefficient j *
        (emZetaDerivative w (2 * j + 1) (x + 1) -
          emZetaDerivative w (2 * j + 1) x) := by
    funext w
    exact emBernoulliBoundary_eq_coefficient (a := x) (D := emZetaDerivative w) j
  rw [hfun]
  have hplus : 0 < x + 1 := by linarith
  exact (differentiableAt_const _).mul
    ((differentiableAt_emZetaDerivative hplus (2 * j + 1) s).sub
      (differentiableAt_emZetaDerivative hx (2 * j + 1) s))

lemma differentiableAt_emZetaHighBlock {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs1 : s ≠ 1) (P : ℕ) :
    DifferentiableAt ℂ (fun w => emZetaHighBlock w P x) s := by
  have hx1 : 0 < x + 1 := by linarith
  have hcx : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hcx1 : (((x + 1 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hx1.ne'
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 1 - w) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have hneg : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
  have hleft := hlin.const_cpow (Or.inl hcx1)
  have hright := hlin.const_cpow (Or.inl hcx)
  have hmain : DifferentiableAt ℂ
      (fun w => ((((x + 1 : ℝ) : ℂ) ^ (1 - w) - (x : ℂ) ^ (1 - w)) / (1 - w))) s :=
    (hleft.sub hright).div hlin (sub_ne_zero.mpr (Ne.symm hs1))
  have hpowx := hneg.const_cpow (Or.inl hcx)
  have hpowx1 := hneg.const_cpow (Or.inl hcx1)
  have htrap : DifferentiableAt ℂ
      (fun w => ((x : ℂ) ^ (-w) + ((x + 1 : ℝ) : ℂ) ^ (-w)) / 2) s :=
    (hpowx.add hpowx1).div_const 2
  have hcorr : DifferentiableAt ℂ
      (fun w => ∑ j ∈ Finset.range P,
        emBernoulliBoundary x (emZetaDerivative w) (2 * j + 1)) s :=
    DifferentiableAt.fun_sum fun j _ => differentiableAt_emBernoulliBoundary hx j s
  unfold emZetaHighBlock
  exact (hmain.sub htrap).add hcorr

def emQP : Set ℂ := {z | 0 < z.re ∧ 0 < z.im}

def emHP : Set ℂ := {z | 0 < z.re ∧ z ≠ 1}

lemma isOpen_emHP : IsOpen emHP :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton

lemma ne_one_of_emHP {z : ℂ} (hz : z ∈ emHP) : z ≠ 1 := hz.2

lemma isOpen_emQP : IsOpen emQP :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma convex_emQP : Convex ℝ emQP := by
  have hre : IsLinearMap ℝ (fun z : ℂ => z.re) :=
    ⟨fun x y => Complex.add_re x y, fun c x => by simp [Complex.real_smul, Complex.mul_re]⟩
  have him : IsLinearMap ℝ (fun z : ℂ => z.im) :=
    ⟨fun x y => Complex.add_im x y, fun c x => by simp [Complex.real_smul, Complex.mul_im]⟩
  exact (convex_halfSpace_gt hre 0).inter (convex_halfSpace_gt him 0)

lemma ne_one_of_emQP {z : ℂ} (hz : z ∈ emQP) : z ≠ 1 := by
  rintro rfl
  simp [emQP] at hz

lemma emPochhammer_norm_le {w : ℂ} {m : ℕ} {R : ℝ}
    (hw : ‖w‖ ≤ R) :
    ‖emPochhammer w m‖ ≤ (R + (m : ℝ)) ^ m := by
  have hterm : ∀ j ∈ Finset.range m,
      ‖w + (j : ℂ)‖ ≤ R + (m : ℝ) := by
    intro j hj
    have hjr : (j : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
    calc
      ‖w + (j : ℂ)‖ ≤ ‖w‖ + ‖(j : ℂ)‖ := norm_add_le _ _
      _ = ‖w‖ + (j : ℝ) := by simp
      _ ≤ R + (m : ℝ) := add_le_add hw hjr
  calc
    ‖emPochhammer w m‖ = ∏ j ∈ Finset.range m, ‖w + (j : ℂ)‖ := by
      simp [emPochhammer, norm_prod]
    _ ≤ ∏ _j ∈ Finset.range m, (R + (m : ℝ)) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        exact hterm j hj
    _ = (R + (m : ℝ)) ^ m := by simp

lemma emPochhammer_norm_le_factorial {s : ℂ} (hs : ‖s‖ ≤ 1) (m : ℕ) :
    ‖emPochhammer s m‖ ≤ (Nat.factorial m : ℝ) := by
  have hterm : ∀ j ∈ Finset.range m, ‖s + (j : ℂ)‖ ≤ ((j + 1 : ℕ) : ℝ) := by
    intro j hj
    calc
      ‖s + (j : ℂ)‖ ≤ ‖s‖ + ‖(j : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + (j : ℝ) := add_le_add hs (by simp)
      _ = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  calc
    ‖emPochhammer s m‖ = ∏ j ∈ Finset.range m, ‖s + (j : ℂ)‖ := by
      simp [emPochhammer, norm_prod]
    _ ≤ ∏ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        exact hterm j hj
    _ = (Nat.factorial m : ℝ) := by
      norm_cast
      simp

lemma differentiableOn_emZetaHighTail {N P : ℕ} (hN : 1 ≤ N) (hP : 1 ≤ P) :
    DifferentiableOn ℂ (fun s => ∑' k : ℕ,
      emZetaHighBlock s P ((k + N : ℕ) : ℝ)) emHP := by
  intro s₀ hs₀
  obtain ⟨hre₀, hs₀1⟩ := hs₀
  set δ : ℝ := min (s₀.re / 2) (‖s₀ - 1‖ / 2) with hδ
  have hdist0 : 0 < ‖s₀ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs₀1)
  have hδ0 : 0 < δ := by positivity
  have hδre : δ ≤ s₀.re / 2 := by rw [hδ]; exact min_le_left _ _
  have hδone : δ ≤ ‖s₀ - 1‖ / 2 := by rw [hδ]; exact min_le_right _ _
  have hball : ∀ w ∈ Metric.ball s₀ δ,
      s₀.re / 2 ≤ w.re ∧ w ≠ 1 ∧ ‖w‖ ≤ ‖s₀‖ + δ := by
    intro w hw
    have hd : ‖w - s₀‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := Complex.abs_re_le_norm (w - s₀)
    rw [Complex.sub_re] at h1
    have hwne : w ≠ 1 := by
      intro heq
      subst w
      have hdist : ‖s₀ - 1‖ < δ := by simpa [norm_sub_rev] using hd
      linarith
    refine ⟨by linarith [(abs_le.mp h1).1], hwne, ?_⟩
    calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + δ := by linarith
  have hsub : Metric.ball s₀ δ ⊆ emHP := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hball w hw
    exact ⟨by linarith, h2⟩
  let m : ℕ := 2 * P
  let R : ℝ := ‖s₀‖ + δ + (m : ℝ)
  let q : ℝ := s₀.re / 2 + (m : ℝ)
  let C : ℝ := (4 / 6 ^ m) * R ^ m
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hq : 1 < q := by
    have hm : 2 ≤ (m : ℝ) := by dsimp [m]; exact_mod_cast (show 2 ≤ 2 * P by omega)
    dsimp [q]
    linarith
  have hmajor : Summable (fun k : ℕ => C * (((k + N : ℕ) : ℝ) ^ (-q))) := by
    have hsumm : Summable (fun k : ℕ => ((k + N : ℕ) : ℝ) ^ (-q)) :=
      summable_shift_rpow_c5 hq N
    exact hsumm.mul_left C
  have hF_le : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball s₀ δ →
      ‖emZetaHighBlock w P ((k + N : ℕ) : ℝ)‖ ≤
        C * (((k + N : ℕ) : ℝ) ^ (-q)) := by
    intro k w hw
    obtain ⟨hσ, -, hwN⟩ := hball w hw
    have hn : 1 ≤ k + N := by omega
    have hx1 : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) := by exact_mod_cast hn
    have hxpos : 0 < ((k + N : ℕ) : ℝ) := by linarith
    have hwpos : 0 < w.re := by linarith
    have hwhp : w ∈ emHP := hsub hw
    have hblock := emZetaHighBlock_eq_remainder hwpos (ne_one_of_emHP hwhp) hP
      (x := ((k + N : ℕ) : ℝ)) hxpos
    have hrem := emZetaRemainder_norm_le hwpos hP hn
    rw [hblock]
    simp only [emZetaRemainder] at hrem
    have hpoch : ‖emPochhammer w m‖ ≤ R ^ m := by
      have hbase : ‖w‖ ≤ ‖s₀‖ + δ := hwN
      simpa [R] using (emPochhammer_norm_le hbase (m := m))
    have hexp : -w.re - (m : ℝ) ≤ -q := by
      dsimp [q]
      linarith
    have hpow : ((k + N : ℕ) : ℝ) ^ (-w.re - (m : ℝ)) ≤
        ((k + N : ℕ) : ℝ) ^ (-q) := Real.rpow_le_rpow_of_exponent_le hx1 hexp
    have hcoeff : 0 ≤ 4 / (6 : ℝ) ^ m := by positivity
    have hcoef : (4 / (6 : ℝ) ^ m) * ‖emPochhammer w m‖ ≤
        (4 / (6 : ℝ) ^ m) * R ^ m :=
      mul_le_mul_of_nonneg_left hpoch hcoeff
    have hpow_nonneg : 0 ≤ ((k + N : ℕ) : ℝ) ^ (-w.re - (m : ℝ)) :=
      Real.rpow_nonneg (by linarith) _
    have hmul := mul_le_mul hcoef hpow hpow_nonneg (by positivity)
    have hbound : ‖emBernoulliIntegral ((k + N : ℕ) : ℝ)
        (emZetaDerivative w) (m)‖ ≤
        (4 / (6 : ℝ) ^ m) * ‖emPochhammer w m‖ *
          ((k + N : ℕ) : ℝ) ^ (-w.re - (m : ℝ)) := by
      simpa [emZetaRemainder, m] using hrem
    calc
      ‖emBernoulliIntegral ((k + N : ℕ) : ℝ) (emZetaDerivative w) m‖ ≤
          (4 / (6 : ℝ) ^ m) * ‖emPochhammer w m‖ *
            ((k + N : ℕ) : ℝ) ^ (-w.re - (m : ℝ)) := hbound
      _ ≤ (4 / (6 : ℝ) ^ m) * R ^ m * ((k + N : ℕ) : ℝ) ^ (-q) := hmul
      _ = C * ((k + N : ℕ) : ℝ) ^ (-q) := by rfl
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ
      (fun w => emZetaHighBlock w P ((k + N : ℕ) : ℝ)) (Metric.ball s₀ δ) := by
    intro k w hw
    have hx : 0 < ((k + N : ℕ) : ℝ) := by
      have : 0 < k + N := by omega
      exact_mod_cast this
    exact (differentiableAt_emZetaHighBlock hx (ne_one_of_emHP (hsub hw)) P).differentiableWithinAt
  have hD := differentiableOn_tsum_of_summable_norm
    hmajor hdiff Metric.isOpen_ball hF_le
  exact (hD.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ0))).differentiableWithinAt

lemma differentiableOn_emZetaHighRHS {N P : ℕ} (hN : 1 ≤ N) (hP : 1 ≤ P) :
    DifferentiableOn ℂ (emZetaHighRHS N P) emHP := by
  intro s hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [emHP] at hs
  have hs1 := ne_one_of_emHP hs
  have hn : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
  have hsum : DifferentiableAt ℂ
      (fun w => ∑ i ∈ Finset.range N, (i : ℂ) ^ (-w)) s :=
    DifferentiableAt.fun_sum fun i _ => hn.const_cpow (Or.inr (neg_ne_zero.mpr hs0))
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmain : DifferentiableAt ℂ
      (fun w => (N : ℂ) ^ (1 - w) / (w - 1)) s :=
    (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hNne)).div
      (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hs1)
  have hhalf : DifferentiableAt ℂ (fun w => (N : ℂ) ^ (-w) / 2) s :=
    (hn.const_cpow (Or.inl hNne)).div_const 2
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hcorr : DifferentiableAt ℂ (fun w => emZetaHighCorrection w P N) s := by
    unfold emZetaHighCorrection
    apply DifferentiableAt.fun_sum
    intro j hj
    exact (differentiableAt_const _).mul
      (differentiableAt_emZetaDerivative hNpos (2 * j + 1) s)
  have htail : DifferentiableAt ℂ (fun w => ∑' k : ℕ,
      emZetaHighBlock w P ((k + N : ℕ) : ℝ)) s :=
    (differentiableOn_emZetaHighTail hN hP).differentiableAt
      (isOpen_emHP.mem_nhds hs)
  unfold emZetaHighRHS
  exact ((((hsum.add hmain).add hhalf).add hcorr).sub htail).differentiableWithinAt

lemma differentiableOn_emZetaHighRHS_emQP {N P : ℕ} (hN : 1 ≤ N) (hP : 1 ≤ P) :
    DifferentiableOn ℂ (emZetaHighRHS N P) emQP := by
  intro s hs
  have hhp : s ∈ emHP := ⟨hs.1, ne_one_of_emQP hs⟩
  exact (differentiableOn_emZetaHighRHS hN hP).differentiableAt
    (isOpen_emHP.mem_nhds hhp) |>.differentiableWithinAt

theorem zeta_em_high {s : ℂ} (hs : s ∈ emQP) {N P : ℕ}
    (hN : 1 ≤ N) (hP : 1 ≤ P) : riemannZeta s = emZetaHighRHS N P s := by
  have hzd : DifferentiableOn ℂ riemannZeta emQP := fun z hz =>
    (differentiableAt_riemannZeta (ne_one_of_emQP hz)).differentiableWithinAt
  have hz : AnalyticOnNhd ℂ riemannZeta emQP := hzd.analyticOnNhd isOpen_emQP
  have he : AnalyticOnNhd ℂ (emZetaHighRHS N P) emQP :=
    (differentiableOn_emZetaHighRHS_emQP hN hP).analyticOnNhd isOpen_emQP
  have hmem : (3 + I : ℂ) ∈ emQP := by simp [emQP]
  have hev : riemannZeta =ᶠ[nhds (3 + I : ℂ)] emZetaHighRHS N P := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simp; norm_num)) fun z hz => ?_
    exact zeta_em_high_of_two_lt hz
  exact hz.eqOn_of_preconnected_of_eventuallyEq he convex_emQP.isPreconnected hmem hev hs

theorem zeta_em_high_real {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) {N P : ℕ}
    (hN : 1 ≤ N) (hP : 1 ≤ P) :
    riemannZeta (x : ℂ) = emZetaHighRHS N P (x : ℂ) := by
  have hx1C : (x : ℂ) ≠ 1 := by exact_mod_cast hx1
  let seq : ℕ → ℂ := fun n => (x : ℂ) + Complex.I *
    (((((n + 1 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ)
  have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hreal : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hseq : Tendsto seq atTop (𝓝 (x : ℂ)) := by
    have hcont : Continuous (fun y : ℝ => (x : ℂ) + Complex.I * (y : ℂ)) := by fun_prop
    convert hcont.continuousAt.tendsto.comp hreal using 1
    · funext n
      simp [seq, Complex.ofReal_inv, Nat.cast_add]
    · simp
  have hmem : ∀ n, seq n ∈ emQP := by
    intro n
    have hnreal : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hncomplex : ((n + 1 : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    have hnreal' : (0 : ℝ) < (n : ℝ) + 1 := by simpa [Nat.cast_add] using hnreal
    have hncomplex' : (n : ℂ) + 1 ≠ 0 := by simpa [Nat.cast_add] using hncomplex
    constructor
    · simp [seq, Complex.add_re]
      exact hx
    · simp [seq, Complex.add_im]
      exact div_pos hnreal' (Complex.normSq_pos.mpr hncomplex')
  have hEq : ∀ n, riemannZeta (seq n) = emZetaHighRHS N P (seq n) := by
    intro n
    exact zeta_em_high (hmem n) hN hP
  have hzcont : ContinuousAt riemannZeta (x : ℂ) :=
    (differentiableAt_riemannZeta hx1C).continuousAt
  have hRHScont : ContinuousAt (emZetaHighRHS N P) (x : ℂ) := by
    have hhp : (x : ℂ) ∈ emHP := ⟨hx, hx1C⟩
    exact ((differentiableOn_emZetaHighRHS hN hP).differentiableAt
      (isOpen_emHP.mem_nhds hhp)).continuousAt
  have hleft := hzcont.tendsto.comp hseq
  have hright := hRHScont.tendsto.comp hseq
  have hright' : Tendsto (fun n => riemannZeta (seq n)) atTop
      (𝓝 (emZetaHighRHS N P (x : ℂ))) :=
    hright.congr' (Filter.Eventually.of_forall fun n => (hEq n).symm)
  exact tendsto_nhds_unique hleft hright'

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem emZetaHighTail_norm_le_node {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (_hReLo : (2 / 5 : ℝ) ≤ s.re) (hReHi : s.re ≤ (3 / 5 : ℝ))
    (hIm : |s.im| ≤ (128 / 100000 : ℝ)) :
    ‖∑' k : ℕ, emZetaHighBlock s 300 ((k + 100 : ℕ) : ℝ)‖ <
      (1 / 10 ^ 250 : ℝ) := by
  have hsNorm : ‖s‖ ≤ 1 := by
    have hre : |s.re| ≤ (3 / 5 : ℝ) := abs_le.mpr ⟨by linarith, hReHi⟩
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ (3 / 5 : ℝ) + (128 / 100000 : ℝ) := add_le_add hre hIm
      _ ≤ 1 := by norm_num
  have hpoch : ‖emPochhammer s 600‖ ≤ (Nat.factorial 600 : ℝ) :=
    emPochhammer_norm_le_factorial hsNorm 600
  have hq : 600 ≤ s.re + 600 := by linarith
  have hq1 : 599 ≤ s.re + 600 - 1 := by linarith
  have hqpos : 0 < s.re + 600 - 1 := by linarith
  have hpow0 : (100 : ℝ) ^ (-(s.re + (600 : ℝ))) ≤
      (100 : ℝ) ^ (-(600 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 100) (by linarith)
  have hpow1 : (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) ≤ (100 : ℝ) ^ (-599 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 100) (by linarith)
  have hinv : (s.re + 600 - 1)⁻¹ ≤ (599 : ℝ)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hq1
  have htailSum : (100 : ℝ) ^ (-(s.re + 600)) +
      (100 : ℝ) ^ (1 - (s.re + 600)) / (s.re + 600 - 1) ≤
        (100 : ℝ) ^ (-(600 : ℝ)) + (100 : ℝ) ^ (-(599 : ℝ)) / 599 := by
    apply add_le_add hpow0
    calc
      (100 : ℝ) ^ (1 - (s.re + 600)) / (s.re + 600 - 1) =
          (100 : ℝ) ^ (1 - (s.re + 600)) * (s.re + 600 - 1)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (100 : ℝ) ^ (-599) * (599 : ℝ)⁻¹ :=
        mul_le_mul hpow1 hinv (by positivity) (by positivity)
      _ = (100 : ℝ) ^ (-(599 : ℝ)) / 599 := by rw [div_eq_mul_inv]
  have hcoeff : 0 ≤ (4 / (6 : ℝ) ^ 600) := by positivity
  have hcoeff' : (4 / (6 : ℝ) ^ 600) * ‖emPochhammer s 600‖ ≤
      (4 / (6 : ℝ) ^ 600) * (Nat.factorial 600 : ℝ) :=
    mul_le_mul_of_nonneg_left hpoch hcoeff
  have hrat : (4 / (6 : ℝ) ^ 600) * (Nat.factorial 600 : ℝ) *
      ((100 : ℝ) ^ (-(600 : ℝ)) + (100 : ℝ) ^ (-(599 : ℝ)) / 599) <
        (1 / 10 ^ 250 : ℝ) := by
    have hpow600 : (100 : ℝ) ^ (-(600 : ℝ)) = (100 ^ 600 : ℝ)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 100) (600 : ℝ)]
      have harg : (600 : ℝ) = (600 : ℕ) := by norm_num
      rw [harg, Real.rpow_natCast]
    have hpow599 : (100 : ℝ) ^ (-(599 : ℝ)) = (100 ^ 599 : ℝ)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 100) (599 : ℝ)]
      have harg : (599 : ℝ) = (599 : ℕ) := by norm_num
      rw [harg, Real.rpow_natCast]
    rw [hpow600, hpow599]
    have hnat : 2796 * Nat.factorial 600 * 10 ^ 250 <
        599 * 6 ^ 600 * 100 ^ 600 := by
      norm_num [Nat.factorial]
      omega
    have hnatR : (2796 : ℝ) * (Nat.factorial 600 : ℝ) * 10 ^ 250 <
        599 * 6 ^ 600 * 100 ^ 600 := by exact_mod_cast hnat
    have hratioR : (2796 : ℝ) * (Nat.factorial 600 : ℝ) /
        (599 * 6 ^ 600 * 100 ^ 600) < 1 / (10 ^ 250 : ℝ) := by
      exact (div_lt_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hnatR)
    have hratR : (4 : ℝ) / 6 ^ 600 * (Nat.factorial 600 : ℝ) *
        (1 / (100 ^ 600 : ℝ) + (1 / (100 ^ 599 : ℝ)) / 599) <
          1 / (10 ^ 250 : ℝ) := by
      calc
        _ = (2796 : ℝ) * (Nat.factorial 600 : ℝ) /
            (599 * 6 ^ 600 * 100 ^ 600) := by field_simp; ring
        _ < 1 / (10 ^ 250 : ℝ) := hratioR
    simpa only [one_div] using hratR
  have htail := emZetaHighTail_norm_le hs hs1 (P := 300) (N := 100) (by norm_num) (by norm_num)
  have htail' : ‖∑' k : ℕ, emZetaHighBlock s 300 ((k + 100 : ℕ) : ℝ)‖ ≤
      (4 / (6 : ℝ) ^ 600) * ‖emPochhammer s 600‖ *
        ((100 : ℝ) ^ (-(s.re + (600 : ℝ))) +
          (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) / (s.re + 600 - 1)) := by
    simpa using htail
  have hmul : (4 / (6 : ℝ) ^ 600) * ‖emPochhammer s 600‖ *
      ((100 : ℝ) ^ (-(s.re + (600 : ℝ))) +
        (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) / (s.re + 600 - 1)) ≤
      (4 / (6 : ℝ) ^ 600) * (Nat.factorial 600 : ℝ) *
        ((100 : ℝ) ^ (-(600 : ℝ)) + (100 : ℝ) ^ (-(599 : ℝ)) / 599) := by
    exact mul_le_mul hcoeff' htailSum (by positivity) (by positivity)
  exact lt_of_le_of_lt (le_trans htail' hmul) hrat

end
end SigmaC5Zeta

#print axioms SigmaC5Zeta.emBernoulliCell
#print axioms SigmaC5Zeta.zeta_em_high_of_two_lt
#print axioms SigmaC5Zeta.zeta_em_high
#print axioms SigmaC5Zeta.zeta_em_high_real
#print axioms SigmaC5Zeta.emZetaHighTail_norm_le
#print axioms SigmaC5Zeta.emZetaHighTail_norm_le_node
