import SigmaC5RationalNodeLogBounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace CarrySigmaObstruction

open SigmaC5Zeta SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem c5AdaptiveLogScaleReducedRange (m : ℕ)
    (hm0 : 1 ≤ m) (hm100 : m ≤ 100) :
    (1 / 2 : ℚ) ≤ (m : ℚ) / 2 ^ c5AdaptiveLogScale m ∧
      (m : ℚ) / 2 ^ c5AdaptiveLogScale m ≤ 1 := by
  interval_cases m <;> norm_num [c5AdaptiveLogScale]

theorem c5RationalZetaAdaptiveTermSide {a b : ℚ} (m : ℕ)
    (hm0 : 1 ≤ m) (hm100 : m ≤ 100)
    (haLo : (2 / 5 : ℚ) ≤ a) (haHi : a ≤ 3 / 5)
    (hbLo : 0 ≤ b) (hbHi : b ≤ 128 / 100000) :
    0 < (m : ℚ) / 2 ^ c5AdaptiveLogScale m ∧
      (m : ℚ) / 2 ^ c5AdaptiveLogScale m < 2 ∧
      ComplexInterval.normBound
        ((ComplexInterval.exact a b).neg.mul
          { re := Interval.logQ 128 (c5AdaptiveLogScale m) (m : ℚ),
            im := Interval.exact 0 }) ≤ 2 ^ 2 := by
  have hscale := c5AdaptiveLogScaleValid m hm0 hm100
  have hlog := c5LogQAdaptiveAbsBound m hm0 hm100
  have hnorm := c5AdaptiveProductNormBoundLeFour haLo haHi hbLo hbHi
    hlog.1 hlog.2
  exact ⟨hscale.1, hscale.2, hnorm.trans (by norm_num)⟩

def c5RationalZetaAdaptiveHeadBox (nExp p : ℕ) (a b : ℚ) :
    ComplexInterval :=
  c5ComplexIntervalRangeSum
    (fun i => ComplexInterval.dirichletTermBox2 128 nExp p
      (c5AdaptiveLogScale (i + 1)) 2 (i + 1) (ComplexInterval.exact a b)) 99

theorem c5RationalZetaAdaptiveHeadBox_contains {nExp p : ℕ}
    {a b : ℚ} (hnExp : 0 < nExp)
    (haLo : (2 / 5 : ℚ) ≤ a) (haHi : a ≤ 3 / 5)
    (hbLo : 0 ≤ b) (hbHi : b ≤ 128 / 100000) :
    (c5RationalZetaAdaptiveHeadBox nExp p a b).contains
      (∑ i ∈ Finset.range 99,
        ((i + 1 : ℕ) : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I))) := by
  apply c5ComplexIntervalRangeSum_contains
  intro i hi
  have hside := c5RationalZetaAdaptiveTermSide (a := a) (b := b) (m := i + 1)
    (by omega) (by omega) haLo haHi hbLo hbHi
  exact ComplexInterval.contains_dirichletTermBox2
    (nLog := 128) (nExp := nExp) (p := p)
    (kL := c5AdaptiveLogScale (i + 1)) (kE := 2)
    (by norm_num) hnExp (by omega)
    (S := ComplexInterval.exact a b)
    (s := (a : ℂ) + (b : ℂ) * Complex.I)
    (c5ExactRatPoint_contains a b) hside.1 hside.2.1 hside.2.2

def c5RationalZetaAdaptiveBasePowerBox (nExp p : ℕ) (a b : ℚ) :
    ComplexInterval :=
  ComplexInterval.dirichletTermBox2 128 nExp p (c5AdaptiveLogScale 100) 2 100
    (ComplexInterval.exact a b)

theorem c5RationalZetaAdaptiveBasePowerBox_contains {nExp p : ℕ}
    {a b : ℚ} (hnExp : 0 < nExp)
    (haLo : (2 / 5 : ℚ) ≤ a) (haHi : a ≤ 3 / 5)
    (hbLo : 0 ≤ b) (hbHi : b ≤ 128 / 100000) :
    (c5RationalZetaAdaptiveBasePowerBox nExp p a b).contains
      ((100 : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I))) := by
  have hside := c5RationalZetaAdaptiveTermSide (a := a) (b := b) (m := 100)
    (by norm_num) (by norm_num) haLo haHi hbLo hbHi
  exact ComplexInterval.contains_dirichletTermBox2
    (nLog := 128) (nExp := nExp) (p := p)
    (kL := c5AdaptiveLogScale 100) (kE := 2)
    (by norm_num) hnExp (by norm_num)
    (S := ComplexInterval.exact a b)
    (s := (a : ℂ) + (b : ℂ) * Complex.I)
    (c5ExactRatPoint_contains a b) hside.1 hside.2.1 hside.2.2

def c5RationalZetaAdaptiveFiniteBox (nExp p : ℕ) (a b : ℚ) :
    ComplexInterval :=
  (c5RationalZetaAdaptiveHeadBox nExp p a b).add
    ((c5RationalZetaAdaptiveBasePowerBox nExp p a b).mul
      (c5RatComplexInterval (c5RatScale a b 300 100)))

def c5RationalZetaAdaptiveNodeBox (nExp p : ℕ) (a b : ℚ) :
    ComplexInterval :=
  (c5RationalZetaAdaptiveFiniteBox nExp p a b).inflate (1 / 10 ^ 250)

theorem c5RationalZetaAdaptiveNodeBox_contains {nExp p : ℕ}
    {a b : ℚ} (haLo : (2 / 5 : ℝ) ≤ (a : ℝ))
    (haHi : (a : ℝ) ≤ 3 / 5) (hbLo : (0 : ℝ) ≤ (b : ℝ))
    (hbHi : (b : ℝ) ≤ 128 / 100000)
    (hden : (a - 1) ^ 2 + b ^ 2 ≠ 0) (hnExp : 0 < nExp) :
    (c5RationalZetaAdaptiveNodeBox nExp p a b).contains
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
  have hcastLo : ((2 / 5 : ℚ) : ℝ) = (2 / 5 : ℝ) := by norm_num
  have hcastHi : ((3 / 5 : ℚ) : ℝ) = (3 / 5 : ℝ) := by norm_num
  have hcastB : ((128 / 100000 : ℚ) : ℝ) = (128 / 100000 : ℝ) := by norm_num
  have haLoQ : (2 / 5 : ℚ) ≤ a := by
    have h : ((2 / 5 : ℚ) : ℝ) ≤ (a : ℝ) := by rw [hcastLo]; exact haLo
    norm_cast at h
  have haHiQ : a ≤ 3 / 5 := by
    have h : (a : ℝ) ≤ ((3 / 5 : ℚ) : ℝ) := by rw [hcastHi]; exact haHi
    norm_cast at h
  have hbLoQ : (0 : ℚ) ≤ b := by exact_mod_cast hbLo
  have hbHiQ : b ≤ 128 / 100000 := by
    have h : (b : ℝ) ≤ ((128 / 100000 : ℚ) : ℝ) := by rw [hcastB]; exact hbHi
    norm_cast at h
  have hheadBox := c5RationalZetaAdaptiveHeadBox_contains
    (nExp := nExp) (p := p) hnExp haLoQ haHiQ hbLoQ hbHiQ
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
      (c5RationalZetaAdaptiveHeadBox nExp p a b).contains
        (∑ i ∈ Finset.range 100, (i : ℂ) ^ (-s)) := by
    rw [hheadEq]
    simpa [s] using hheadBox
  have hbaseBox := c5RationalZetaAdaptiveBasePowerBox_contains
    (nExp := nExp) (p := p) hnExp haLoQ haHiQ hbLoQ hbHiQ
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
      (c5RationalZetaAdaptiveFiniteBox nExp p a b).contains finite' := by
    simpa [c5RationalZetaAdaptiveFiniteBox, s, finite'] using hfiniteBox
  have hcontained := ComplexInterval.contains_inflate
    (x := c5RationalZetaAdaptiveFiniteBox nExp p a b)
    (z := finite')
    (w := riemannZeta ((a : ℂ) + (b : ℂ) * Complex.I))
    (r := (1 / 10 ^ 250 : ℚ)) hfiniteBox' hdiff'
  simpa [c5RationalZetaAdaptiveNodeBox, c5RationalZetaAdaptiveFiniteBox,
    c5RationalZetaAdaptiveHeadBox, c5RationalZetaAdaptiveBasePowerBox,
    c5AdaptiveLogScale, c5RatComplexInterval, s, finite] using hcontained

theorem c5RationalZetaAdaptiveNodeBox_contains_at {nExp p j : ℕ} {a : ℚ}
    (hnExp : 0 < nExp) (hj : j ≤ 128)
    (haLo : (2 / 5 : ℚ) ≤ a) (haHi : a ≤ 3 / 5) :
    (c5RationalZetaAdaptiveNodeBox nExp p a ((j : ℚ) / 100000)).contains
      (riemannZeta ((a : ℂ) + (((j : ℚ) / 100000 : ℚ) : ℂ) * Complex.I)) := by
  have hjQ : (j : ℚ) ≤ 128 := by exact_mod_cast hj
  have hbLoQ : (0 : ℚ) ≤ (j : ℚ) / 100000 := by positivity
  have hbHiQ : (j : ℚ) / 100000 ≤ 128 / 100000 :=
    div_le_div_of_nonneg_right hjQ (by norm_num)
  have hcastLo : (2 / 5 : ℝ) = ((2 / 5 : ℚ) : ℝ) := by norm_num
  have hcastHi : (3 / 5 : ℝ) = ((3 / 5 : ℚ) : ℝ) := by norm_num
  have haLoR : (2 / 5 : ℝ) ≤ (a : ℝ) := by
    rw [hcastLo]
    exact_mod_cast haLo
  have haHiR : (a : ℝ) ≤ 3 / 5 := by
    rw [hcastHi]
    exact_mod_cast haHi
  have hjR : (j : ℝ) ≤ 128 := by exact_mod_cast hj
  have hbLoR : (0 : ℝ) ≤ (j : ℝ) / 100000 := by positivity
  have hbHiR : (j : ℝ) / 100000 ≤ 128 / 100000 :=
    div_le_div_of_nonneg_right hjR (by norm_num)
  have hcastB : (((j : ℚ) / 100000 : ℚ) : ℝ) = (j : ℝ) / 100000 := by
    push_cast
    ring
  rw [← hcastB] at hbLoR hbHiR
  have haNe : a ≠ 1 := by
    intro h
    rw [h] at haHi
    norm_num at haHi
  have hbaseNe : a - 1 ≠ 0 := sub_ne_zero.mpr haNe
  have hbasePos : 0 < (a - 1) ^ 2 := sq_pos_of_ne_zero hbaseNe
  have hden : (a - 1) ^ 2 + ((j : ℚ) / 100000) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hbasePos (sq_nonneg _))
  exact c5RationalZetaAdaptiveNodeBox_contains haLoR haHiR hbLoR hbHiR hden hnExp

def c5ComplexIntervalConjugateBox (x : ComplexInterval) : ComplexInterval :=
  { re := x.re, im := x.im.neg }

theorem c5ComplexIntervalConjugateBox_contains {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) :
    (c5ComplexIntervalConjugateBox x).contains (star z) := by
  constructor
  · simpa [c5ComplexIntervalConjugateBox] using hx.1
  · simpa [c5ComplexIntervalConjugateBox] using Interval.contains_neg hx.2

theorem c5RationalZetaAdaptiveNodeConjugateBox_contains_at
    {nExp p j : ℕ} {a : ℚ} (hnExp : 0 < nExp)
    (hj : j ≤ 128) (haLo : (2 / 5 : ℚ) ≤ a) (haHi : a ≤ 3 / 5) :
    (c5ComplexIntervalConjugateBox
      (c5RationalZetaAdaptiveNodeBox nExp p a ((j : ℚ) / 100000))).contains
      (riemannZeta ((a : ℂ) - (((j : ℚ) / 100000 : ℚ) : ℂ) * Complex.I)) := by
  let s : ℂ := (a : ℂ) + (((j : ℚ) / 100000 : ℚ) : ℂ) * Complex.I
  have hs : star s =
      (a : ℂ) - (((j : ℚ) / 100000 : ℚ) : ℂ) * Complex.I := by
    simp [s]
    ring
  have hpositive := c5RationalZetaAdaptiveNodeBox_contains_at
    (nExp := nExp) (p := p) (j := j) (a := a) hnExp hj haLo haHi
  have hpositive' :
      (c5RationalZetaAdaptiveNodeBox nExp p a ((j : ℚ) / 100000)).contains
        (riemannZeta s) := by simpa [s] using hpositive
  have hconj := c5ComplexIntervalConjugateBox_contains hpositive'
  have hzeta : riemannZeta (star s) = star (riemannZeta s) :=
    riemannZeta_conj s
  rw [← hs, hzeta]
  exact hconj

end CarrySigmaObstruction
