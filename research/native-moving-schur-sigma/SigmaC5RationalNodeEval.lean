import SigmaC5EulerMaclaurin
import SigmaC5GammaRationalCore
import ZetaLean.IntervalCExp

/-!
# Rational point evaluation of the C5 Euler–Maclaurin formula

This file factors the order-300 Bernoulli correction by the single power
`100⁻ˢ`.  At a rational point, the remaining coefficient is exact rational
complex arithmetic.  The decomposition is the first step toward evaluating
the original completed source at the C5 interpolation nodes.
-/

namespace CarrySigmaObstruction

open SigmaC5Zeta SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
open scoped BigOperators

noncomputable section
set_option autoImplicit false

abbrev C5RatComplex := SigmaC5Gamma.RatComplex

def c5RatComplexPow (z : C5RatComplex) : ℕ → C5RatComplex
  | 0 => (1, 0)
  | n + 1 => ratComplexMul (c5RatComplexPow z n) z

def c5RatPochhammer (a b : ℚ) : ℕ → C5RatComplex
  | 0 => (1, 0)
  | n + 1 => ratComplexMul (c5RatPochhammer a b n) (a + (n : ℚ), b)

def c5RatBernoulliCoefficient (j : ℕ) : ℚ :=
  (bernoulli (2 * j + 2) : ℚ) / (Nat.factorial (2 * j + 2) : ℚ)

def c5RatCorrectionTerm (a b : ℚ) (N j : ℕ) : C5RatComplex :=
  ratComplexMul
    (ratComplexMul (c5RatBernoulliCoefficient j, 0)
      (c5RatPochhammer a b (2 * j + 1)))
    (c5RatComplexPow ((1 / (N : ℚ)), 0) (2 * j + 1))

def c5RatCorrectionSum (a b : ℚ) (P N : ℕ) : C5RatComplex :=
  ∑ j ∈ Finset.range P, c5RatCorrectionTerm a b N j

def c5RatComplexAdd (z w : C5RatComplex) : C5RatComplex :=
  (z.1 + w.1, z.2 + w.2)

def c5RatScale (a b : ℚ) (P N : ℕ) : C5RatComplex :=
  c5RatComplexAdd
    (c5RatComplexAdd
      (ratComplexMul (N, 0) (ratComplexInv (a - 1, b)))
      (1 / 2, 0))
    (c5RatCorrectionSum a b P N)

def c5RatComplexInterval (z : C5RatComplex) : ComplexInterval :=
  ComplexInterval.exact z.1 z.2

lemma c5RatComplexToComplex_add (z w : C5RatComplex) :
    ratComplexToComplex (c5RatComplexAdd z w) =
      ratComplexToComplex z + ratComplexToComplex w := by
  apply Complex.ext <;> simp [c5RatComplexAdd, ratComplexToComplex, Complex.add_re,
    Complex.add_im]

lemma c5RatComplexToComplex_pow (z : C5RatComplex) (n : ℕ) :
    ratComplexToComplex (c5RatComplexPow z n) =
      ratComplexToComplex z ^ n := by
  induction n with
  | zero =>
      change ratComplexToComplex (1, 0) = 1
      apply Complex.ext <;> norm_num [ratComplexToComplex]
  | succ n ih =>
      simp only [c5RatComplexPow, ratComplexToComplex_mul, ih, pow_succ]

lemma c5RatPochhammer_toComplex (a b : ℚ) (n : ℕ) :
    ratComplexToComplex (c5RatPochhammer a b n) =
      emPochhammer ((a : ℂ) + (b : ℂ) * Complex.I) n := by
  induction n with
  | zero =>
      change ratComplexToComplex (1, 0) = 1
      apply Complex.ext <;> norm_num [ratComplexToComplex]
  | succ n ih =>
      rw [c5RatPochhammer, ratComplexToComplex_mul, ih]
      have hfactor : ratComplexToComplex (a + (n : ℚ), b) =
          ((a : ℂ) + (b : ℂ) * Complex.I) + (n : ℂ) := by
        apply Complex.ext <;> simp [ratComplexToComplex, Complex.add_re, Complex.add_im]
      rw [hfactor]
      simp [emPochhammer, Finset.prod_range_succ]

lemma c5RatBernoulliCoefficient_toComplex (j : ℕ) :
    ratComplexToComplex (c5RatBernoulliCoefficient j, 0) =
      emBernoulliCoefficient j := by
  apply Complex.ext <;>
    norm_num [c5RatBernoulliCoefficient, emBernoulliCoefficient,
      ratComplexToComplex]

lemma c5RatComplexInterval_contains (z : C5RatComplex) :
    (c5RatComplexInterval z).contains (ratComplexToComplex z) := by
  exact ⟨Interval.contains_exact _, Interval.contains_exact _⟩

lemma c5ExactRatPoint_contains (a b : ℚ) :
    (ComplexInterval.exact a b).contains ((a : ℂ) + (b : ℂ) * Complex.I) := by
  constructor <;>
    simp [ComplexInterval.exact, Interval.contains,
      Interval.exact, Complex.add_re, Complex.add_im]

lemma c5RatInversePower_toComplex {N : ℕ} (k : ℕ) :
    ratComplexToComplex (c5RatComplexPow ((1 / (N : ℚ)), 0) k) =
      (N : ℂ) ^ (-(k : ℂ)) := by
  have hinv : ratComplexToComplex ((1 / (N : ℚ)), 0) = (N : ℂ)⁻¹ := by
    apply Complex.ext <;> simp [ratComplexToComplex]
  rw [c5RatComplexToComplex_pow, hinv, inv_pow]
  calc
    ((N : ℂ) ^ k)⁻¹ = ((N : ℂ) ^ (k : ℂ))⁻¹ := by rw [Complex.cpow_natCast]
    _ = (N : ℂ) ^ (-(k : ℂ)) := by rw [Complex.cpow_neg]

lemma c5RatCorrectionTerm_toComplex (a b : ℚ) (N j : ℕ) :
    ratComplexToComplex (c5RatCorrectionTerm a b N j) =
      emBernoulliCoefficient j *
        emPochhammer ((a : ℂ) + (b : ℂ) * Complex.I) (2 * j + 1) *
          (N : ℂ) ^ (-((2 * j + 1 : ℕ) : ℂ)) := by
  rw [c5RatCorrectionTerm, ratComplexToComplex_mul, ratComplexToComplex_mul,
    c5RatBernoulliCoefficient_toComplex, c5RatPochhammer_toComplex,
    c5RatInversePower_toComplex]

lemma c5RatCorrectionSum_toComplex (a b : ℚ) (P N : ℕ) :
    ratComplexToComplex (c5RatCorrectionSum a b P N) =
      ∑ j ∈ Finset.range P,
        emBernoulliCoefficient j *
          emPochhammer ((a : ℂ) + (b : ℂ) * Complex.I) (2 * j + 1) *
            (N : ℂ) ^ (-((2 * j + 1 : ℕ) : ℂ)) := by
  rw [c5RatCorrectionSum, ratComplexToComplex_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact c5RatCorrectionTerm_toComplex a b N j

lemma emZetaCorrectionTerm_factor {a b : ℚ} {N : ℕ} (hN : 0 < N) (j : ℕ) :
    -emBernoulliCoefficient j *
        emZetaDerivative ((a : ℂ) + (b : ℂ) * Complex.I) (2 * j + 1) (N : ℝ) =
      (N : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I)) *
        (emBernoulliCoefficient j *
          emPochhammer ((a : ℂ) + (b : ℂ) * Complex.I) (2 * j + 1) *
            (N : ℂ) ^ (-((2 * j + 1 : ℕ) : ℂ))) := by
  rw [emZetaDerivative_nat_eq]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsplit :
      (N : ℂ) ^ (-(((a : ℂ) + (b : ℂ) * Complex.I) + ((2 * j + 1 : ℕ) : ℂ))) =
        (N : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I)) *
          (N : ℂ) ^ (-((2 * j + 1 : ℕ) : ℂ)) := by
    rw [show -(((a : ℂ) + (b : ℂ) * Complex.I) + ((2 * j + 1 : ℕ) : ℂ)) =
      -((a : ℂ) + (b : ℂ) * Complex.I) + -((2 * j + 1 : ℕ) : ℂ) by ring]
    exact Complex.cpow_add _ _ hN0
  have hsign : (-1 : ℂ) ^ (2 * j + 1) = -1 := by
    rw [pow_succ, pow_mul]
    simp
  rw [hsplit, hsign]
  ring

theorem emZetaHighCorrection_eq_rational_scale {a b : ℚ} {P N : ℕ}
    (hN : 0 < N) :
    emZetaHighCorrection ((a : ℂ) + (b : ℂ) * Complex.I) P N =
      (N : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I)) *
        ratComplexToComplex (c5RatCorrectionSum a b P N) := by
  rw [emZetaHighCorrection, c5RatCorrectionSum_toComplex a b P N]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact emZetaCorrectionTerm_factor hN j

lemma c5RatScale_toComplex {a b : ℚ} (P N : ℕ)
    (hden : (a - 1) ^ 2 + b ^ 2 ≠ 0) :
    ratComplexToComplex (c5RatScale a b P N) =
      (N : ℂ) / (((a : ℂ) + (b : ℂ) * Complex.I) - 1) +
        (1 / 2 : ℂ) + ratComplexToComplex (c5RatCorrectionSum a b P N) := by
  have hinv := ratComplexToComplex_inv (a - 1, b) hden
  have harg : ratComplexToComplex (a - 1, b) =
      ((a : ℂ) + (b : ℂ) * Complex.I) - 1 := by
    apply Complex.ext <;> simp [ratComplexToComplex, Complex.sub_re, Complex.sub_im]
  simp only [c5RatScale, c5RatComplexToComplex_add, ratComplexToComplex_mul,
    hinv]
  rw [ratComplexToComplex_real, harg, ratComplexToComplex_real]
  norm_num [div_eq_mul_inv]

theorem c5_emZetaHighRHS_factor {a b : ℚ} {P N : ℕ} (hN : 0 < N)
    (hden : (a - 1) ^ 2 + b ^ 2 ≠ 0) :
    emZetaHighRHS N P ((a : ℂ) + (b : ℂ) * Complex.I) =
      (∑ i ∈ Finset.range N,
        (i : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I))) +
        (N : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I)) *
          ratComplexToComplex (c5RatScale a b P N) -
        ∑' k : ℕ,
          emZetaHighBlock ((a : ℂ) + (b : ℂ) * Complex.I) P
            ((k + N : ℕ) : ℝ) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmain :
      (N : ℂ) ^ (1 - ((a : ℂ) + (b : ℂ) * Complex.I)) =
        (N : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I)) * (N : ℂ) := by
    rw [show (1 : ℂ) - ((a : ℂ) + (b : ℂ) * Complex.I) =
      -((a : ℂ) + (b : ℂ) * Complex.I) + 1 by ring,
      Complex.cpow_add, Complex.cpow_one]
    exact hN0
  rw [emZetaHighRHS, hmain,
    emZetaHighCorrection_eq_rational_scale hN,
    c5RatScale_toComplex P N hden]
  ring

def c5ComplexIntervalRangeSum (f : ℕ → ComplexInterval) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 0 0
  | n + 1 => (c5ComplexIntervalRangeSum f n).add (f n)

theorem c5ComplexIntervalRangeSum_contains {n : ℕ}
    (f : ℕ → ComplexInterval) (g : ℕ → ℂ)
    (hf : ∀ i < n, (f i).contains (g i)) :
    (c5ComplexIntervalRangeSum f n).contains (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simp [c5ComplexIntervalRangeSum, ComplexInterval.contains_zero]
  | succ n ih =>
      rw [c5ComplexIntervalRangeSum, Finset.sum_range_succ]
      apply ComplexInterval.contains_add
      · apply ih
        intro i hi
        exact hf i (by omega)
      · exact hf n (by omega)

def c5RationalZetaHeadBox (nLog nExp p kL kE : ℕ) (a b : ℚ) :
    ComplexInterval :=
  c5ComplexIntervalRangeSum
    (fun i => ComplexInterval.dirichletTermBox2 nLog nExp p kL kE (i + 1)
      (ComplexInterval.exact a b)) 99

def c5RationalZetaBasePowerBox (nLog nExp p kL kE : ℕ) (a b : ℚ) :
    ComplexInterval :=
  ComplexInterval.dirichletTermBox2 nLog nExp p kL kE 100
    (ComplexInterval.exact a b)

def c5RationalZetaFiniteBox (nLog nExp p kL kE : ℕ) (a b : ℚ) :
    ComplexInterval :=
  (c5RationalZetaHeadBox nLog nExp p kL kE a b).add
    ((c5RationalZetaBasePowerBox nLog nExp p kL kE a b).mul
      (c5RatComplexInterval (c5RatScale a b 300 100)))

def c5RationalZetaNodeBox (nLog nExp p kL kE : ℕ) (a b : ℚ) :
    ComplexInterval :=
  (c5RationalZetaFiniteBox nLog nExp p kL kE a b).inflate (1 / 10 ^ 250)

theorem c5RationalZetaHeadBox_contains {nLog nExp p kL kE : ℕ}
    {a b : ℚ} (hnLog : 0 < nLog) (hnExp : 0 < nExp)
    (hside : ∀ i < 99,
      0 < ((i + 1 : ℕ) : ℚ) / 2 ^ kL ∧
      ((i + 1 : ℕ) : ℚ) / 2 ^ kL < 2 ∧
      ComplexInterval.normBound
        ((ComplexInterval.exact a b).neg.mul
          { re := Interval.logQ nLog kL ((i + 1 : ℕ) : ℚ),
            im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (c5RationalZetaHeadBox nLog nExp p kL kE a b).contains
      (∑ i ∈ Finset.range 99,
        ((i + 1 : ℕ) : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I))) := by
  apply c5ComplexIntervalRangeSum_contains
  intro i hi
  have h := hside i hi
  exact ComplexInterval.contains_dirichletTermBox2
    (nLog := nLog) (nExp := nExp) (p := p) (kL := kL) (kE := kE)
    hnLog hnExp (m := i + 1) (by omega)
    (S := ComplexInterval.exact a b)
    (s := (a : ℂ) + (b : ℂ) * Complex.I)
    (c5ExactRatPoint_contains a b) h.1 h.2.1 h.2.2

theorem c5RationalZetaBasePowerBox_contains {nLog nExp p kL kE : ℕ}
    {a b : ℚ} (hnLog : 0 < nLog) (hnExp : 0 < nExp)
    (hside : 0 < (100 : ℚ) / 2 ^ kL ∧
      (100 : ℚ) / 2 ^ kL < 2 ∧
      ComplexInterval.normBound
        ((ComplexInterval.exact a b).neg.mul
          { re := Interval.logQ nLog kL 100, im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (c5RationalZetaBasePowerBox nLog nExp p kL kE a b).contains
      ((100 : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I))) := by
  exact ComplexInterval.contains_dirichletTermBox2
    (nLog := nLog) (nExp := nExp) (p := p) (kL := kL) (kE := kE)
    hnLog hnExp (m := 100) (by norm_num)
    (S := ComplexInterval.exact a b)
    (s := (a : ℂ) + (b : ℂ) * Complex.I)
    (c5ExactRatPoint_contains a b) hside.1 hside.2.1 hside.2.2

theorem c5_sum_zeta_head_eq_shifted (s : ℂ) (hs : s ≠ 0) :
    (∑ i ∈ Finset.range 100, (i : ℂ) ^ (-s)) =
      ∑ i ∈ Finset.range 99, ((i + 1 : ℕ) : ℂ) ^ (-s) := by
  rw [show 100 = 99 + 1 by norm_num, Finset.sum_range_succ']
  simp [Complex.zero_cpow, neg_ne_zero.mpr hs]

theorem c5RationalZetaNodeBox_contains {nLog nExp p kL kE : ℕ}
    {a b : ℚ} (haLo : (2 / 5 : ℝ) ≤ (a : ℝ))
    (haHi : (a : ℝ) ≤ 3 / 5) (hbLo : (0 : ℝ) ≤ (b : ℝ))
    (hbHi : (b : ℝ) ≤ 128 / 100000)
    (hden : (a - 1) ^ 2 + b ^ 2 ≠ 0)
    (hnLog : 0 < nLog) (hnExp : 0 < nExp)
    (hhead : ∀ i < 99,
      0 < ((i + 1 : ℕ) : ℚ) / 2 ^ kL ∧
      ((i + 1 : ℕ) : ℚ) / 2 ^ kL < 2 ∧
      ComplexInterval.normBound
        ((ComplexInterval.exact a b).neg.mul
          { re := Interval.logQ nLog kL ((i + 1 : ℕ) : ℚ),
            im := Interval.exact 0 }) ≤ 2 ^ kE)
    (hbase : 0 < (100 : ℚ) / 2 ^ kL ∧
      (100 : ℚ) / 2 ^ kL < 2 ∧
      ComplexInterval.normBound
        ((ComplexInterval.exact a b).neg.mul
          { re := Interval.logQ nLog kL 100, im := Interval.exact 0 }) ≤ 2 ^ kE) :
    (c5RationalZetaNodeBox nLog nExp p kL kE a b).contains
      (riemannZeta ((a : ℂ) + (b : ℂ) * Complex.I)) := by
  let s : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  let tail : ℂ := ∑' k : ℕ, emZetaHighBlock s 300 ((k + 100 : ℕ) : ℝ)
  let finite : ℂ := (∑ i ∈ Finset.range 100, (i : ℂ) ^ (-s)) +
    (100 : ℂ) ^ (-s) * ratComplexToComplex (c5RatScale a b 300 100)
  have hsre : (2 / 5 : ℝ) ≤ s.re := by simpa [s] using haLo
  have hsre' : s.re ≤ (3 / 5 : ℝ) := by simpa [s] using haHi
  have hsIm : |s.im| ≤ (128 / 100000 : ℝ) := by
    rw [show s.im = (b : ℝ) by simp [s]]
    rw [abs_of_nonneg hbLo]
    exact hbHi
  have hspos : 0 < s.re := lt_of_lt_of_le (by norm_num) hsre
  have hsne : s ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    simp [s] at hRe
    linarith
  have hzeta : riemannZeta s = emZetaHighRHS 100 300 s := by
    by_cases hb : b = 0
    · have hreal := zeta_em_high_real (x := (a : ℝ))
        (N := 100) (P := 300)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 5) haLo)
        (ne_of_lt (lt_of_le_of_lt haHi (by norm_num : (3 / 5 : ℝ) < 1)))
        (by norm_num) (by norm_num)
      simpa [s, hb] using hreal
    · have hbpos : (0 : ℝ) < (b : ℝ) := by
        rcases eq_or_lt_of_le hbLo with heq | hlt
        · have hbzero : b = 0 := by exact_mod_cast heq.symm
          exact (hb hbzero).elim
        · exact hlt
      have hsMem : s ∈ emQP := by
        constructor
        · exact hspos
        · simpa [s] using hbpos
      exact zeta_em_high (N := 100) (P := 300) hsMem (by norm_num) (by norm_num)
  have hfactor := c5_emZetaHighRHS_factor (a := a) (b := b)
    (P := 300) (N := 100) (by norm_num) hden
  have hfactor' : emZetaHighRHS 100 300 s = finite - tail := by
    simpa [s, finite, tail] using hfactor
  have hheadBox := c5RationalZetaHeadBox_contains
    (nLog := nLog) (nExp := nExp) (p := p) (kL := kL) (kE := kE)
    hnLog hnExp hhead
  have hheadEq :
      (∑ i ∈ Finset.range 100, (i : ℂ) ^ (-s)) =
        ∑ i ∈ Finset.range 99,
          ((i + 1 : ℕ) : ℂ) ^ (-s) :=
    c5_sum_zeta_head_eq_shifted s (by
      intro h
      have hRe := congrArg Complex.re h
      simp at hRe
      linarith [hspos])
  have hheadBox' :
      (c5RationalZetaHeadBox nLog nExp p kL kE a b).contains
        (∑ i ∈ Finset.range 100, (i : ℂ) ^ (-s)) := by
    rw [hheadEq]
    simpa [s] using hheadBox
  have hbaseBox := c5RationalZetaBasePowerBox_contains
    (nLog := nLog) (nExp := nExp) (p := p) (kL := kL) (kE := kE)
    hnLog hnExp hbase
  have hscaleBox := c5RatComplexInterval_contains (c5RatScale a b 300 100)
  have hprodBox := ComplexInterval.contains_mul hbaseBox hscaleBox
  have hfiniteBox := ComplexInterval.contains_add hheadBox' hprodBox
  have htail := emZetaHighTail_norm_le_node hspos hsne hsre hsre' hsIm
  have hdiff : ‖riemannZeta s - finite‖ ≤ (1 / 10 ^ 250 : ℝ) := by
    rw [hzeta, hfactor']
    calc
      ‖(finite - tail) - finite‖ = ‖-tail‖ := by congr 1; ring
      _ = ‖tail‖ := norm_neg _
      _ ≤ (1 / 10 ^ 250 : ℝ) := htail.le
  let finite' : ℂ :=
    (∑ i ∈ Finset.range 100, (i : ℂ) ^
      (-((a : ℂ) + (b : ℂ) * Complex.I))) +
      (100 : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I)) *
        ratComplexToComplex (c5RatScale a b 300 100)
  have hdiff' :
      ‖riemannZeta ((a : ℂ) + (b : ℂ) * Complex.I) - finite'‖ ≤
        (((1 / 10 ^ 250 : ℚ) : ℝ)) := by
    simpa [s, finite, finite'] using hdiff
  have hfiniteBox' :
      (c5RationalZetaFiniteBox nLog nExp p kL kE a b).contains finite' := by
    simpa [c5RationalZetaFiniteBox, s, finite'] using hfiniteBox
  have hcontained := ComplexInterval.contains_inflate
    (x := c5RationalZetaFiniteBox nLog nExp p kL kE a b)
    (z := finite')
    (w := riemannZeta ((a : ℂ) + (b : ℂ) * Complex.I))
    (r := (1 / 10 ^ 250 : ℚ)) hfiniteBox' hdiff'
  simpa [c5RationalZetaNodeBox, c5RationalZetaFiniteBox,
    c5RationalZetaHeadBox, c5RationalZetaBasePowerBox, c5RatComplexInterval, s, finite]
    using hcontained

end
end CarrySigmaObstruction
