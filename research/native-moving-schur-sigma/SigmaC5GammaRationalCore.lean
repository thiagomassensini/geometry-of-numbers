import SigmaGammaEulerIntegral
import ZetaLean.IntervalCExp

/-!
# Exact rational core of the finite Gamma evaluator

At rational complex arguments, the finite Euler approximation to Gamma is an
exact rational-complex sum times one real-base complex power. This separates
the cancellation-sensitive rational sum from the single exponential that the
existing interval evaluator already handles.
-/

namespace SigmaC5Gamma

open scoped BigOperators

/-- A rational complex number, stored without introducing interval width. -/
abbrev RatComplex := ℚ × ℚ

def ratComplexToComplex (z : RatComplex) : ℂ := ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

def ratComplexMul (z w : RatComplex) : RatComplex :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

def ratComplexInv (z : RatComplex) : RatComplex :=
  (z.1 / (z.1 ^ 2 + z.2 ^ 2), -z.2 / (z.1 ^ 2 + z.2 ^ 2))

def ratGammaTerm (T a b : ℚ) (k : ℕ) : RatComplex :=
  ratComplexMul
    (((-T) ^ k / (k.factorial : ℚ)), 0)
    (ratComplexInv (a + k, b))

/-- The rational-complex sum appearing in `gammaFinite`, before its common
factor `T^z` is applied. -/
def gammaFiniteRationalCore (N : ℕ) (T a b : ℚ) : RatComplex :=
  ∑ k ∈ Finset.range N, ratGammaTerm T a b k

@[simp] theorem ratComplexToComplex_add (z w : RatComplex) :
    ratComplexToComplex (z + w) = ratComplexToComplex z + ratComplexToComplex w := by
  apply Complex.ext <;> simp [ratComplexToComplex]

@[simp] theorem ratComplexToComplex_real (q : ℚ) :
    ratComplexToComplex (q, 0) = (q : ℂ) := by
  apply Complex.ext <;> simp [ratComplexToComplex]

theorem ratComplexToComplex_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → RatComplex) :
    ratComplexToComplex (∑ i ∈ s, f i) = ∑ i ∈ s, ratComplexToComplex (f i) := by
  induction s using Finset.induction_on with
  | empty => apply Complex.ext <;> simp [ratComplexToComplex]
  | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, ih, ratComplexToComplex_add]

theorem ratComplexToComplex_mul (z w : RatComplex) :
    ratComplexToComplex (ratComplexMul z w) =
      ratComplexToComplex z * ratComplexToComplex w := by
  apply Complex.ext <;>
    simp [ratComplexToComplex, ratComplexMul, Complex.mul_re, Complex.mul_im]

theorem ratComplexToComplex_inv (z : RatComplex)
    (hz : z.1 ^ 2 + z.2 ^ 2 ≠ 0) :
    ratComplexToComplex (ratComplexInv z) =
      (ratComplexToComplex z)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have hden : (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 ≠ 0 := by exact_mod_cast hz
  apply Complex.ext
  · simp [ratComplexToComplex, ratComplexInv, Complex.mul_re]
    field_simp [hden]
    ring
  · simp [ratComplexToComplex, ratComplexInv, Complex.mul_im]
    field_simp [hden]
    ring

private theorem rationalNode_ne_zero (a b : ℚ) (k : ℕ) (ha : 0 < a) :
    ((a : ℂ) + (b : ℂ) * Complex.I) + (k : ℂ) ≠ 0 := by
  intro h
  have hpos : 0 < (((a : ℂ) + (b : ℂ) * Complex.I) + (k : ℂ)).re := by
    have hrepr : (((a : ℂ) + (b : ℂ) * Complex.I) + (k : ℂ)).re =
        (a : ℝ) + (k : ℝ) := by simp [Complex.add_re]
    rw [hrepr]
    exact_mod_cast add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg k)
  rw [h] at hpos
  simp at hpos

private theorem ratGammaTerm_toComplex (T a b : ℚ) (k : ℕ) (ha : 0 < a) :
    ratComplexToComplex (ratGammaTerm T a b k) =
      (-(T : ℂ)) ^ k / (k.factorial : ℂ) /
        (((a : ℂ) + (b : ℂ) * Complex.I) + (k : ℂ)) := by
  have hden : (a + (k : ℚ)) ^ 2 + b ^ 2 ≠ 0 := by
    have hpos : 0 < a + (k : ℚ) := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg k)
    positivity
  rw [ratGammaTerm, ratComplexToComplex_mul, ratComplexToComplex_inv _ hden]
  have hnum : ratComplexToComplex (((-T) ^ k / (k.factorial : ℚ)), 0) =
      (-(T : ℂ)) ^ k / (k.factorial : ℂ) := by
    have hcast : (-(T : ℂ)) ^ k / (k.factorial : ℂ) =
        (((-T) ^ k / (k.factorial : ℚ) : ℚ) : ℂ) := by norm_cast
    rw [ratComplexToComplex_real, hcast]
  rw [hnum]
  have hbase : ratComplexToComplex (a + (k : ℚ), b) =
      ((a : ℂ) + (b : ℂ) * Complex.I) + (k : ℂ) := by
    apply Complex.ext <;>
      simp [ratComplexToComplex, Complex.add_re, Complex.add_im]
  rw [hbase]
  field_simp [rationalNode_ne_zero a b k ha]

theorem gammaFinite_eq_rationalCore (N : ℕ) (T a b : ℚ) (ha : 0 < a) :
    gammaFinite N (T : ℝ) ((a : ℂ) + (b : ℂ) * Complex.I) =
      (T : ℂ) ^ ((a : ℂ) + (b : ℂ) * Complex.I) *
        ratComplexToComplex (gammaFiniteRationalCore N T a b) := by
  unfold gammaFinite gammaFiniteRationalCore
  rw [ratComplexToComplex_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [ratGammaTerm_toComplex T a b k ha]
  push_cast
  field_simp [rationalNode_ne_zero a b k ha]

def gammaFiniteRationalCoreInterval (N T : ℕ) (a b : ℚ) :
    ZetaLean.ComplexInterval :=
  ZetaLean.ComplexInterval.exact
    (gammaFiniteRationalCore N T a b).1 (gammaFiniteRationalCore N T a b).2

def gammaFiniteNegativePointBox (a b : ℚ) : ZetaLean.ComplexInterval :=
  ZetaLean.ComplexInterval.exact (-a) (-b)

/-- The exact rational core and the certified real-base complex power give a
formal rectangle containing the finite Euler approximation to Gamma at any
rational point with positive real part. The caller supplies the usual `expCr`
norm bound for the power box. -/
def gammaFiniteInterval (N T : ℕ) (a b : ℚ)
    (nLog nExp p kL kE : ℕ) : ZetaLean.ComplexInterval :=
  (ZetaLean.ComplexInterval.dirichletTermBox2 nLog nExp p kL kE T
      (gammaFiniteNegativePointBox a b)).mul
    (gammaFiniteRationalCoreInterval N T a b)

theorem gammaFiniteRationalCoreInterval_contains (N T : ℕ) (a b : ℚ) :
    (gammaFiniteRationalCoreInterval N T a b).contains
      (ratComplexToComplex (gammaFiniteRationalCore N T a b)) := by
  change (ZetaLean.Interval.exact (gammaFiniteRationalCore N T a b).1).contains
      ((gammaFiniteRationalCore N T a b).1 : ℝ) ∧
    (ZetaLean.Interval.exact (gammaFiniteRationalCore N T a b).2).contains
      ((gammaFiniteRationalCore N T a b).2 : ℝ)
  exact ⟨ZetaLean.Interval.contains_exact _, ZetaLean.Interval.contains_exact _⟩

theorem gammaFiniteInterval_contains (N T : ℕ) (a b : ℚ) (ha : 0 < a)
    (nLog nExp p kL kE : ℕ) (hnLog : 0 < nLog) (hnExp : 0 < nExp)
    (hT0 : 0 < (T : ℚ) / 2 ^ kL) (hT2 : (T : ℚ) / 2 ^ kL < 2)
    (hbound : ZetaLean.ComplexInterval.normBound
      ((gammaFiniteNegativePointBox a b).neg.mul
        { re := ZetaLean.Interval.logQ nLog kL (T : ℚ),
          im := ZetaLean.Interval.exact 0 }) ≤ 2 ^ kE) :
    (gammaFiniteInterval N T a b nLog nExp p kL kE).contains
      (gammaFinite N (T : ℝ) ((a : ℂ) + (b : ℂ) * Complex.I)) := by
  let z : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  change (gammaFiniteInterval N T a b nLog nExp p kL kE).contains
    (gammaFinite N (T : ℝ) z)
  have hza : z.re = (a : ℝ) := by simp [z]
  have hzb : z.im = (b : ℝ) := by simp [z]
  have hpoint : (gammaFiniteNegativePointBox a b).contains (-z) := by
    constructor
    · change (ZetaLean.Interval.exact (-a)).contains (-z.re)
      rw [hza]
      simpa using ZetaLean.Interval.contains_exact (-a)
    · change (ZetaLean.Interval.exact (-b)).contains (-z.im)
      rw [hzb]
      simpa using ZetaLean.Interval.contains_exact (-b)
  have hTpow : (0 : ℚ) < (2 : ℚ) ^ kL := by positivity
  have hTposq : (0 : ℚ) < (T : ℚ) := by
    calc
      0 < ((T : ℚ) / 2 ^ kL) * 2 ^ kL := mul_pos hT0 hTpow
      _ = (T : ℚ) := div_mul_cancel₀ _ (ne_of_gt hTpow)
  have hTpos : 0 < T := by exact_mod_cast hTposq
  have hpower := ZetaLean.ComplexInterval.contains_dirichletTermBox2
    (nLog := nLog) (nExp := nExp) (p := p) (kL := kL) (kE := kE)
    hnLog hnExp (m := T) hTpos hpoint hT0 hT2 hbound
  have hpower' :
      (ZetaLean.ComplexInterval.dirichletTermBox2 nLog nExp p kL kE T
        (gammaFiniteNegativePointBox a b)).contains ((T : ℂ) ^ z) := by
    simpa [gammaFiniteNegativePointBox, z] using hpower
  have hcore := gammaFiniteRationalCoreInterval_contains N T a b
  have hTcast : ((T : ℚ) : ℝ) = (T : ℝ) := by norm_cast
  have hgamma : gammaFinite N (T : ℝ) z =
      (T : ℂ) ^ z * ratComplexToComplex (gammaFiniteRationalCore N T a b) := by
    simpa [z, hTcast] using gammaFinite_eq_rationalCore N (T : ℚ) a b ha
  rw [hgamma]
  simpa [gammaFiniteInterval] using
    (ZetaLean.ComplexInterval.contains_mul hpower' hcore)

/-- The exact Gamma box obtained by inflating the rational-core finite
enclosure by the already proved `10⁻²⁵⁹` Euler error. -/
def gamma3072Interval (a b : ℚ) (nLog nExp p kL kE : ℕ) :
    ZetaLean.ComplexInterval :=
  (gammaFiniteInterval 3072 620 a b nLog nExp p kL kE).inflate (1 / 10 ^ 259)

theorem gamma3072Interval_contains (a b : ℚ) (ha : 0 < a)
    (hRe : (1495 / 20000 : ℝ) ≤ (a : ℝ)) (hRe1 : (a : ℝ) ≤ 1)
    (nLog nExp p kL kE : ℕ) (hnLog : 0 < nLog) (hnExp : 0 < nExp)
    (hT0 : 0 < (620 : ℚ) / 2 ^ kL) (hT2 : (620 : ℚ) / 2 ^ kL < 2)
    (hbound : ZetaLean.ComplexInterval.normBound
      ((gammaFiniteNegativePointBox a b).neg.mul
        { re := ZetaLean.Interval.logQ nLog kL 620,
          im := ZetaLean.Interval.exact 0 }) ≤ 2 ^ kE) :
    (gamma3072Interval a b nLog nExp p kL kE).contains
      (Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)) := by
  have hfinite := gammaFiniteInterval_contains 3072 620 a b ha
    nLog nExp p kL kE hnLog hnExp hT0 hT2 hbound
  have herr := gamma_finite_3072_620_error
    ((a : ℂ) + (b : ℂ) * Complex.I) (by simpa using hRe) (by simpa using hRe1)
  have hfinite' :
      (gammaFiniteInterval 3072 620 a b nLog nExp p kL kE).contains
        (gammaFinite 3072 620 ((a : ℂ) + (b : ℂ) * Complex.I)) := by
    convert hfinite using 1; norm_num
  have herr' :
      ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I) -
        gammaFinite 3072 620 ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          (((1 : ℚ) / 10 ^ 259 : ℚ) : ℝ) := by
    calc
      _ ≤ (1 : ℝ) / (10 : ℝ) ^ 259 := by simpa using herr
      _ = (((1 : ℚ) / 10 ^ 259 : ℚ) : ℝ) := by norm_num
  exact ZetaLean.ComplexInterval.contains_inflate hfinite' herr'

#print axioms ratComplexToComplex_mul
#print axioms ratComplexToComplex_inv
#print axioms gammaFinite_eq_rationalCore
#print axioms gammaFiniteInterval_contains
#print axioms gamma3072Interval_contains

end SigmaC5Gamma
