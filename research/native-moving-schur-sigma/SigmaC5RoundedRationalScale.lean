import SigmaC5RationalNodeInstantiate
import SigmaC5FastBernoulliTable

namespace CarrySigmaObstruction

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
open scoped BigOperators

set_option autoImplicit false

/-! Specialized multiplication by an exact rational complex number.  The
generic rectangle product visits all sixteen corner products; here each
coordinate is scaled by one exact rational before the two coordinates are
added. -/
def c5RatIntervalMulExact (x : Interval) (c : ℚ) : Interval :=
  if hc : 0 ≤ c then
    { lo := x.lo * c, hi := x.hi * c,
      le := mul_le_mul_of_nonneg_right x.le hc }
  else
    { lo := x.hi * c, hi := x.lo * c,
      le := mul_le_mul_of_nonpos_right x.le (le_of_not_ge hc) }

theorem c5RatIntervalMulExact_contains {x : Interval} {c : ℚ} {t : ℝ}
    (hx : x.contains t) : (c5RatIntervalMulExact x c).contains (t * c) := by
  by_cases hc : 0 ≤ c
  · have hcR : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    simp [c5RatIntervalMulExact, hc, Interval.contains]
    exact ⟨mul_le_mul_of_nonneg_right hx.1 hcR,
      mul_le_mul_of_nonneg_right hx.2 hcR⟩
  · have hcR : (c : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hc)
    simp [c5RatIntervalMulExact, hc, Interval.contains]
    exact ⟨mul_le_mul_of_nonpos_right hx.2 hcR,
      mul_le_mul_of_nonpos_right hx.1 hcR⟩

def c5RatComplexMulExact (x : ComplexInterval) (a b : ℚ) : ComplexInterval :=
  { re := (c5RatIntervalMulExact x.re a).sub
      (c5RatIntervalMulExact x.im b),
    im := (c5RatIntervalMulExact x.re b).add
      (c5RatIntervalMulExact x.im a) }

theorem c5RatComplexMulExact_contains {x : ComplexInterval} {w : ℂ}
    {a b : ℚ} (hx : x.contains w) :
    (c5RatComplexMulExact x a b).contains
      (w * ratComplexToComplex (a, b)) := by
  have hre := Interval.contains_sub
    (c5RatIntervalMulExact_contains (c := a) hx.1)
    (c5RatIntervalMulExact_contains (c := b) hx.2)
  have him := Interval.contains_add
    (c5RatIntervalMulExact_contains (c := b) hx.1)
    (c5RatIntervalMulExact_contains (c := a) hx.2)
  constructor
  · simpa [c5RatComplexMulExact, ratComplexToComplex, Complex.mul_re] using hre
  · simpa [c5RatComplexMulExact, ratComplexToComplex, Complex.mul_im] using him

/-! The inverse powers in the Euler–Maclaurin correction are real. Keeping
them as a real interval avoids widening a zero imaginary component and avoids
the generic four-corner complex rectangle product at every summand. -/
def c5RatComplexMulInterval (x : ComplexInterval) (r : Interval) :
    ComplexInterval :=
  { re := x.re.mul r, im := x.im.mul r }

theorem c5RatComplexMulInterval_contains {x : ComplexInterval} {w : ℂ}
    {r : Interval} {t : ℝ} (hx : x.contains w) (hr : r.contains t) :
    (c5RatComplexMulInterval x r).contains (w * (t : ℂ)) := by
  have hre := Interval.contains_mul hx.1 hr
  have him := Interval.contains_mul hx.2 hr
  constructor
  · simpa [c5RatComplexMulInterval, Complex.mul_re] using hre
  · simpa [c5RatComplexMulInterval, Complex.mul_im] using him

private theorem c5RatComplexPow_real (q : ℚ) (n : ℕ) :
    ratComplexToComplex (c5RatComplexPow (q, 0) n) = ((q ^ n : ℚ) : ℂ) := by
  induction n with
  | zero =>
      apply Complex.ext <;> simp [c5RatComplexPow, ratComplexToComplex]
  | succ n ih =>
      change ratComplexToComplex
        (ratComplexMul (c5RatComplexPow (q, 0) n) (q, 0)) = _
      rw [ratComplexToComplex_mul, ih, ratComplexToComplex_real]
      norm_cast
      rw [pow_succ]

/-- Rounded interval powers for the exact rational-complex powers in the
Euler–Maclaurin correction. -/
def c5RatComplexPowInterval (p : ℕ) (z : C5RatComplex) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 1 0
  | n + 1 =>
      (c5RatComplexMulExact (c5RatComplexPowInterval p z n) z.1 z.2).coarsen p

theorem c5RatComplexPowInterval_contains (p : ℕ) (z : C5RatComplex) :
    ∀ n, (c5RatComplexPowInterval p z n).contains
      (ratComplexToComplex (c5RatComplexPow z n))
  | 0 => by
      change (ComplexInterval.exact 1 0).contains
        (ratComplexToComplex (1, 0))
      exact ⟨Interval.contains_exact _, Interval.contains_exact _⟩
  | n + 1 => by
      rw [c5RatComplexPowInterval, c5RatComplexPow]
      rw [ratComplexToComplex_mul]
      exact ComplexInterval.contains_coarsen p
        (c5RatComplexMulExact_contains
          (c5RatComplexPowInterval_contains p z n))

/-- A dyadically rounded enclosure of the finite rising factorial. -/
def c5RatPochhammerInterval (p : ℕ) (a b : ℚ) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 1 0
  | n + 1 =>
      (c5RatComplexMulExact (c5RatPochhammerInterval p a b n)
        (a + (n : ℚ)) b).coarsen p

theorem c5RatPochhammerInterval_contains (p : ℕ) (a b : ℚ) :
    ∀ n, (c5RatPochhammerInterval p a b n).contains
      (ratComplexToComplex (c5RatPochhammer a b n))
  | 0 => by
      change (ComplexInterval.exact 1 0).contains
        (ratComplexToComplex (1, 0))
      exact ⟨Interval.contains_exact _, Interval.contains_exact _⟩
  | n + 1 => by
      rw [c5RatPochhammerInterval, c5RatPochhammer]
      rw [ratComplexToComplex_mul]
      exact ComplexInterval.contains_coarsen p
        (c5RatComplexMulExact_contains
          (c5RatPochhammerInterval_contains p a b n))

/-- One order-300 correction term, rounded after each complex product. -/
def c5RatCorrectionTermInterval (p : ℕ) (a b : ℚ) (N j : ℕ) :
    ComplexInterval :=
  let k := 2 * j + 1
  let bern := ComplexInterval.exact (c5RatBernoulliCoefficient j) 0
  let poch := c5RatPochhammerInterval p a b k
  let invPow := c5RatComplexPowInterval p ((1 / (N : ℚ)), 0) k
  ((bern.mul poch).coarsen p).mul invPow |>.coarsen p

theorem c5RatCorrectionTermInterval_contains (p : ℕ) (a b : ℚ)
    (N j : ℕ) :
    (c5RatCorrectionTermInterval p a b N j).contains
      (ratComplexToComplex (c5RatCorrectionTerm a b N j)) := by
  let k := 2 * j + 1
  let bern := ComplexInterval.exact (c5RatBernoulliCoefficient j) 0
  let poch := c5RatPochhammerInterval p a b k
  let invPow := c5RatComplexPowInterval p ((1 / (N : ℚ)), 0) k
  have hbern : bern.contains
      (ratComplexToComplex (c5RatBernoulliCoefficient j, 0)) := by
    exact ⟨Interval.contains_exact _, Interval.contains_exact _⟩
  have hpoch := c5RatPochhammerInterval_contains p a b k
  have hinv := c5RatComplexPowInterval_contains p ((1 / (N : ℚ)), 0) k
  have hmul₁ := ComplexInterval.contains_coarsen p
    (ComplexInterval.contains_mul hbern hpoch)
  have hmul₂ := ComplexInterval.contains_coarsen p
    (ComplexInterval.contains_mul hmul₁ hinv)
  have hterm :
      ratComplexToComplex (c5RatCorrectionTerm a b N j) =
        ratComplexToComplex (c5RatBernoulliCoefficient j, 0) *
          ratComplexToComplex (c5RatPochhammer a b k) *
            ratComplexToComplex (c5RatComplexPow ((1 / (N : ℚ)), 0) k) := by
    change ratComplexToComplex
        (ratComplexMul
          (ratComplexMul (c5RatBernoulliCoefficient j, 0)
            (c5RatPochhammer a b k))
          (c5RatComplexPow ((1 / (N : ℚ)), 0) k)) = _
    rw [ratComplexToComplex_mul, ratComplexToComplex_mul]
  change (ComplexInterval.coarsen p
    ((ComplexInterval.coarsen p (bern.mul poch)).mul invPow)).contains _
  rw [hterm]
  exact hmul₂

/-- Carry the current rising factorial, inverse power, and correction sum from
one Bernoulli order to the next, rounding each operation outward. -/
def c5RatCorrectionStateInterval (p : ℕ) (a b : ℚ) (N : ℕ)
    (bernCoeff : ℕ → ℚ) :
    ℕ → ComplexInterval × ℚ × ComplexInterval
  | 0 => (ComplexInterval.exact a b,
      1 / (N : ℚ), ComplexInterval.exact 0 0)
  | j + 1 =>
      let prev := c5RatCorrectionStateInterval p a b N bernCoeff j
      let k := 2 * j + 1
      let term :=
        (c5RatComplexMulExact
          (ComplexInterval.coarsen p
            (c5RatComplexMulExact prev.1 (bernCoeff j) 0))
          prev.2.1 0).coarsen p
      let nextPoch :=
        (c5RatComplexMulExact
          ((c5RatComplexMulExact prev.1 (a + (k : ℚ)) b).coarsen p)
          (a + ((k + 1 : ℕ) : ℚ)) b).coarsen p
      let nextPow :=
        prev.2.1 * (1 / (N : ℚ)) * (1 / (N : ℚ))
      (nextPoch, nextPow, (prev.2.2.add term).coarsen p)

private theorem c5RatCorrectionSum_cast (a b : ℚ) (N P : ℕ) :
    ratComplexToComplex (c5RatCorrectionSum a b P N) =
      ∑ i ∈ Finset.range P,
        ratComplexToComplex (c5RatCorrectionTerm a b N i) := by
  rw [c5RatCorrectionSum, ratComplexToComplex_sum]

set_option maxHeartbeats 2000000

theorem c5RatCorrectionStateInterval_contains (p : ℕ) (a b : ℚ) (N P : ℕ)
    (bernCoeff : ℕ → ℚ)
    (hBernCoeff : ∀ j, j < P → bernCoeff j = c5RatBernoulliCoefficient j) :
    ∀ j, j ≤ P →
      (c5RatCorrectionStateInterval p a b N bernCoeff j).1.contains
        (ratComplexToComplex (c5RatPochhammer a b (2 * j + 1))) ∧
      (c5RatCorrectionStateInterval p a b N bernCoeff j).2.1 =
        (1 / (N : ℚ)) ^ (2 * j + 1) ∧
      (c5RatCorrectionStateInterval p a b N bernCoeff j).2.2.contains
        (ratComplexToComplex (c5RatCorrectionSum a b j N))
  | 0, _ => by
      constructor
      · simpa [c5RatCorrectionStateInterval, c5RatPochhammer,
          ratComplexMul] using
          (show (ComplexInterval.exact a b).contains
              (ratComplexToComplex (a, b)) from
            ⟨Interval.contains_exact _, Interval.contains_exact _⟩)
      constructor
      · simp [c5RatCorrectionStateInterval, pow_one]
      · change (ComplexInterval.exact 0 0).contains
          (ratComplexToComplex (0, 0))
        exact ⟨Interval.contains_exact _, Interval.contains_exact _⟩
  | j + 1, hj => by
      have ih := c5RatCorrectionStateInterval_contains p a b N P bernCoeff hBernCoeff
        j (by omega)
      let k : ℕ := 2 * j + 1
      have hcoeff := hBernCoeff j (by omega)
      have htermMul₁ := ComplexInterval.contains_coarsen p
        (c5RatComplexMulExact_contains
          (a := bernCoeff j) (b := 0) ih.1)
      have htermMul₂ := ComplexInterval.contains_coarsen p
        (c5RatComplexMulExact_contains
          (a := (c5RatCorrectionStateInterval p a b N bernCoeff j).2.1)
          (b := 0) htermMul₁)
      have htermCast :
          ratComplexToComplex (c5RatCorrectionTerm a b N j) =
            ratComplexToComplex (c5RatBernoulliCoefficient j, 0) *
              ratComplexToComplex (c5RatPochhammer a b k) *
                ratComplexToComplex (c5RatComplexPow ((1 / (N : ℚ)), 0) k) := by
        change ratComplexToComplex
            (ratComplexMul
              (ratComplexMul (c5RatBernoulliCoefficient j, 0)
                (c5RatPochhammer a b k))
              (c5RatComplexPow ((1 / (N : ℚ)), 0) k)) = _
        rw [ratComplexToComplex_mul, ratComplexToComplex_mul]
      have htermCastSwap :
          ratComplexToComplex (c5RatCorrectionTerm a b N j) =
            ratComplexToComplex (c5RatPochhammer a b k) *
              ratComplexToComplex (bernCoeff j, 0) *
                ratComplexToComplex
                  ((c5RatCorrectionStateInterval p a b N bernCoeff j).2.1, 0) := by
        rw [htermCast, mul_comm (ratComplexToComplex (c5RatBernoulliCoefficient j, 0))
          (ratComplexToComplex (c5RatPochhammer a b k))]
        rw [← hcoeff]
        rw [c5RatComplexPow_real]
        dsimp [k]
        rw [← ih.2.1]
        simp [ratComplexToComplex_real]
      have hterm :
          ((c5RatComplexMulExact
              (ComplexInterval.coarsen p
              (c5RatComplexMulExact
                (c5RatCorrectionStateInterval p a b N bernCoeff j).1
                (bernCoeff j) 0))
              (c5RatCorrectionStateInterval p a b N bernCoeff j).2.1 0).coarsen p).contains
              (ratComplexToComplex (c5RatCorrectionTerm a b N j)) := by
        rw [htermCastSwap]
        simpa [c5RatCorrectionStateInterval, k] using htermMul₂
      have hsumSplit :
          ratComplexToComplex (c5RatCorrectionSum a b (j + 1) N) =
            ratComplexToComplex (c5RatCorrectionSum a b j N) +
              ratComplexToComplex (c5RatCorrectionTerm a b N j) := by
        calc
          ratComplexToComplex (c5RatCorrectionSum a b (j + 1) N) =
              ∑ i ∈ Finset.range (j + 1),
                ratComplexToComplex (c5RatCorrectionTerm a b N i) :=
            c5RatCorrectionSum_cast a b N (j + 1)
          _ = (∑ i ∈ Finset.range j,
                ratComplexToComplex (c5RatCorrectionTerm a b N i)) +
                ratComplexToComplex (c5RatCorrectionTerm a b N j) := by
            rw [Finset.sum_range_succ]
          _ = ratComplexToComplex (c5RatCorrectionSum a b j N) +
                ratComplexToComplex (c5RatCorrectionTerm a b N j) := by
            rw [← c5RatCorrectionSum_cast a b N j]
      have hsum := ComplexInterval.contains_coarsen p
        (ComplexInterval.contains_add ih.2.2 hterm)
      have hpoch₁ := ComplexInterval.contains_coarsen p
        (c5RatComplexMulExact_contains
          (a := a + (k : ℚ)) (b := b) ih.1)
      have hpoch₂ := ComplexInterval.contains_coarsen p
        (c5RatComplexMulExact_contains
          (a := a + ((k + 1 : ℕ) : ℚ)) (b := b) hpoch₁)
      have hpochCast :
          ratComplexToComplex (c5RatPochhammer a b (2 * (j + 1) + 1)) =
            ratComplexToComplex (c5RatPochhammer a b k) *
              ratComplexToComplex (a + (k : ℚ), b) *
                ratComplexToComplex (a + ((k + 1 : ℕ) : ℚ), b) := by
        have hidx : 2 * (j + 1) + 1 = k + 2 := by
          dsimp [k]
          omega
        rw [hidx, c5RatPochhammer, ratComplexToComplex_mul,
          c5RatPochhammer, ratComplexToComplex_mul]
      have hidx : 2 * (j + 1) + 1 = k + 2 := by
        dsimp [k]
        omega
      have hpowCast :
          ((1 / (N : ℚ)) ^ (2 * (j + 1) + 1) : ℚ) =
            (1 / (N : ℚ)) ^ k * (1 / (N : ℚ)) * (1 / (N : ℚ)) := by
        rw [hidx, pow_add]
        simp [pow_two, mul_assoc]
      simp only [c5RatCorrectionStateInterval]
      refine ⟨?_, ?_, ?_⟩
      · rw [hpochCast]
        exact hpoch₂
      · rw [hpowCast]
        rw [ih.2.1]
      · rw [hsumSplit]
        exact hsum

/-- The full correction sum with rounded interval additions and shared
Pochhammer/power recurrences. -/
def c5RatCorrectionSumIntervalWithTable (p : ℕ) (a b : ℚ) (N P : ℕ)
    (bernTable : Array ℚ) :
    ComplexInterval :=
  let bernCoeff := fun j =>
    bernTable.getD (2 * j + 2) 0 / (Nat.factorial (2 * j + 2) : ℚ)
  (c5RatCorrectionStateInterval p a b N bernCoeff P).2.2

theorem c5RatCorrectionSumIntervalWithTable_contains (p : ℕ) (a b : ℚ)
    (N P : ℕ) (bernTable : Array ℚ)
    (hsize : 2 * P + 1 ≤ bernTable.size)
    (hBernTable : ∀ i, i < bernTable.size →
      bernTable.getD i 0 = bernoulli' i) :
    (c5RatCorrectionSumIntervalWithTable p a b N P bernTable).contains
      (ratComplexToComplex (c5RatCorrectionSum a b P N)) := by
  let bernCoeff := fun j =>
    bernTable.getD (2 * j + 2) 0 / (Nat.factorial (2 * j + 2) : ℚ)
  have hcoeff : ∀ j, j < P → bernCoeff j = c5RatBernoulliCoefficient j := by
    intro j hj
    have hidx : 2 * j + 2 < 2 * P + 1 := by omega
    have hidx' : 2 * j + 2 < bernTable.size := lt_of_lt_of_le hidx hsize
    dsimp [bernCoeff, c5RatBernoulliCoefficient]
    rw [hBernTable (2 * j + 2) hidx']
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by omega : 2 * j + 2 ≠ 1)]
  change (c5RatCorrectionStateInterval p a b N bernCoeff P).2.2.contains _
  exact (c5RatCorrectionStateInterval_contains p a b N P bernCoeff hcoeff
    P (by omega)).2.2

def c5RatCorrectionSumInterval (p : ℕ) (a b : ℚ) (N P : ℕ) :
    ComplexInterval :=
  c5RatCorrectionSumIntervalWithTable p a b N P
    (c5BernoulliPrimeTable (2 * P + 1))

theorem c5RatCorrectionSumInterval_contains (p : ℕ) (a b : ℚ) (N P : ℕ) :
    (c5RatCorrectionSumInterval p a b N P).contains
      (ratComplexToComplex (c5RatCorrectionSum a b P N)) := by
  apply c5RatCorrectionSumIntervalWithTable_contains
  · simp [c5BernoulliPrimeTable_size]
  · intro i hi
    have hi' : i < 2 * P + 1 := by
      simpa [c5BernoulliPrimeTable_size] using hi
    exact c5BernoulliPrimeTable_getD (2 * P + 1) i hi'

/-- A rounded enclosure of the rational factor multiplying `100 ^ (-s)` in
the exact Euler–Maclaurin zeta identity. -/
def c5RatScaleIntervalWithTable (p : ℕ) (a b : ℚ) (P N : ℕ)
    (bernTable : Array ℚ) : ComplexInterval :=
  ((c5RatComplexInterval
      (c5RatComplexAdd
        (ratComplexMul (N, 0) (ratComplexInv (a - 1, b))) (1 / 2, 0))).add
      (c5RatCorrectionSumIntervalWithTable p a b N P bernTable)).coarsen p

theorem c5RatScaleIntervalWithTable_contains (p : ℕ) (a b : ℚ) (P N : ℕ)
    (bernTable : Array ℚ) (hsize : 2 * P + 1 ≤ bernTable.size)
    (hBernTable : ∀ i, i < bernTable.size →
      bernTable.getD i 0 = bernoulli' i) :
    (c5RatScaleIntervalWithTable p a b P N bernTable).contains
      (ratComplexToComplex (c5RatScale a b P N)) := by
  have hbase := c5RatComplexInterval_contains
    (c5RatComplexAdd
      (ratComplexMul (N, 0) (ratComplexInv (a - 1, b))) (1 / 2, 0))
  have hsum := c5RatCorrectionSumIntervalWithTable_contains p a b N P
    bernTable hsize hBernTable
  have hadd := ComplexInterval.contains_add hbase hsum
  have hscale :
      ratComplexToComplex (c5RatScale a b P N) =
        ratComplexToComplex
          (c5RatComplexAdd
            (ratComplexMul (N, 0) (ratComplexInv (a - 1, b))) (1 / 2, 0)) +
          ratComplexToComplex (c5RatCorrectionSum a b P N) := by
    simp [c5RatScale, c5RatComplexToComplex_add]
  rw [c5RatScaleIntervalWithTable, hscale]
  exact ComplexInterval.contains_coarsen p hadd

def c5RatScaleInterval (p : ℕ) (a b : ℚ) (P N : ℕ) : ComplexInterval :=
  c5RatScaleIntervalWithTable p a b P N
    (c5BernoulliPrimeTable (2 * P + 1))

theorem c5RatScaleInterval_contains (p : ℕ) (a b : ℚ) (P N : ℕ) :
    (c5RatScaleInterval p a b P N).contains
      (ratComplexToComplex (c5RatScale a b P N)) := by
  apply c5RatScaleIntervalWithTable_contains
  · simp [c5BernoulliPrimeTable_size]
  · intro i hi
    have hi' : i < 2 * P + 1 := by
      simpa [c5BernoulliPrimeTable_size] using hi
    exact c5BernoulliPrimeTable_getD (2 * P + 1) i hi'

#print axioms c5RatComplexPowInterval_contains
#print axioms c5RatPochhammerInterval_contains
#print axioms c5RatCorrectionTermInterval_contains
#print axioms c5RatCorrectionSumInterval_contains
#print axioms c5RatScaleInterval_contains

end CarrySigmaObstruction
