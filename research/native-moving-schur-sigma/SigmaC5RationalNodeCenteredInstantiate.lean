import SigmaC5RationalNodeCenteredBoxes
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace CarrySigmaObstruction

open SigmaC5Zeta SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5RationalZetaCenteredHeadBox (nLog nExp p : ℕ) (a b : ℚ) : ComplexInterval :=
  let logTwo := c5CenteredLog2I nLog
  c5ComplexIntervalRangeSum
    (fun i => c5CenteredDirichletTermBoxWithLogTwo nLog nExp p 4 logTwo
      (i + 1) (ComplexInterval.exact a b)) 99

theorem c5RationalZetaCenteredHeadBox_contains {nLog nExp p : ℕ}
    {a b : ℚ} (_hnLog : 0 < nLog) (hnExp : 0 < nExp)
    (haLo : 2 / 5 ≤ a) (haHi : a ≤ 3 / 5)
    (hbLo : 0 ≤ b) (hbHi : b ≤ 128 / 100000) :
    (c5RationalZetaCenteredHeadBox nLog nExp p a b).contains
      (∑ i ∈ Finset.range 99,
        ((i + 1 : ℕ) : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I))) := by
  apply c5ComplexIntervalRangeSum_contains
  intro i hi
  have hm0 : 1 ≤ i + 1 := by omega
  have hm100 : i + 1 ≤ 100 := by omega
  have hterm := c5CenteredDirichletTermBoxContains
    (nLog := nLog) (nExp := nExp) (p := p) (by omega) hnExp
    (hm := by omega) (hm100 := hm100) haLo haHi hbLo hbHi
  simpa [c5RationalZetaCenteredHeadBox, c5CenteredDirichletTermBox] using hterm

def c5RationalZetaCenteredBasePowerBox (nLog nExp p : ℕ) (a b : ℚ) :
    ComplexInterval :=
  let logTwo := c5CenteredLog2I nLog
  c5CenteredDirichletTermBoxWithLogTwo nLog nExp p 4 logTwo 100
    (ComplexInterval.exact a b)

theorem c5RationalZetaCenteredBasePowerBox_contains {nLog nExp p : ℕ}
    {a b : ℚ} (_hnLog : 0 < nLog) (hnExp : 0 < nExp)
    (haLo : 2 / 5 ≤ a) (haHi : a ≤ 3 / 5)
    (hbLo : 0 ≤ b) (hbHi : b ≤ 128 / 100000) :
    (c5RationalZetaCenteredBasePowerBox nLog nExp p a b).contains
      ((100 : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I))) := by
  have hterm := c5CenteredDirichletTermBoxContains
    (nLog := nLog) (nExp := nExp) (p := p) (m := 100) (by omega) hnExp
    (hm := by norm_num) (hm100 := by norm_num) haLo haHi hbLo hbHi
  simpa [c5RationalZetaCenteredBasePowerBox, c5CenteredDirichletTermBox]
    using hterm

def c5RationalZetaCenteredFiniteBoxWithTable (nLog nExp p : ℕ)
    (a b : ℚ) (bernTable : Array ℚ) : ComplexInterval :=
  (c5RationalZetaCenteredHeadBox nLog nExp p a b).add
    ((c5RationalZetaCenteredBasePowerBox nLog nExp p a b).mul
      (c5RatScaleIntervalWithTable p a b 300 100 bernTable))

def c5RationalZetaCenteredFiniteBox (nLog nExp p : ℕ) (a b : ℚ) :
    ComplexInterval :=
  c5RationalZetaCenteredFiniteBoxWithTable nLog nExp p a b
    (c5BernoulliPrimeTable 601)

def c5RationalZetaCenteredNodeBoxWithTable (nLog nExp p : ℕ)
    (a b : ℚ) (bernTable : Array ℚ) : ComplexInterval :=
  (c5RationalZetaCenteredFiniteBoxWithTable nLog nExp p a b bernTable).inflate
    (1 / 10 ^ 250)

def c5RationalZetaCenteredNodeBox (nLog nExp p : ℕ) (a b : ℚ) :
    ComplexInterval :=
  c5RationalZetaCenteredNodeBoxWithTable nLog nExp p a b
    (c5BernoulliPrimeTable 601)

theorem c5RationalZetaCenteredNodeBoxWithTable_contains {nLog nExp p : ℕ}
    (bernTable : Array ℚ) (hsize : 601 ≤ bernTable.size)
    (hBernTable : ∀ i, i < bernTable.size →
      bernTable.getD i 0 = bernoulli' i)
    {a b : ℚ} (haLo : (2 / 5 : ℝ) ≤ (a : ℝ))
    (haHi : (a : ℝ) ≤ 3 / 5) (hbLo : (0 : ℝ) ≤ (b : ℝ))
    (hbHi : (b : ℝ) ≤ 128 / 100000)
    (hden : (a - 1) ^ 2 + b ^ 2 ≠ 0)
    (hnLog : 0 < nLog) (hnExp : 0 < nExp) :
    (c5RationalZetaCenteredNodeBoxWithTable nLog nExp p a b bernTable).contains
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
  have hheadBox := c5RationalZetaCenteredHeadBox_contains
    (nLog := nLog) (nExp := nExp) (p := p) hnLog hnExp
    haLoQ haHiQ hbLoQ hbHiQ
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
      (c5RationalZetaCenteredHeadBox nLog nExp p a b).contains
        (∑ i ∈ Finset.range 100, (i : ℂ) ^ (-s)) := by
    rw [hheadEq]
    simpa [s] using hheadBox
  have hbaseBox := c5RationalZetaCenteredBasePowerBox_contains
    (nLog := nLog) (nExp := nExp) (p := p) hnLog hnExp
    haLoQ haHiQ hbLoQ hbHiQ
  have hscaleBox := c5RatScaleIntervalWithTable_contains p a b 300 100
    bernTable hsize hBernTable
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
      (c5RationalZetaCenteredFiniteBoxWithTable nLog nExp p a b bernTable).contains
        finite' := by
    simpa [c5RationalZetaCenteredFiniteBoxWithTable, s, finite'] using hfiniteBox
  have hcontained := ComplexInterval.contains_inflate
    (x := c5RationalZetaCenteredFiniteBoxWithTable nLog nExp p a b bernTable)
    (z := finite')
    (w := riemannZeta ((a : ℂ) + (b : ℂ) * Complex.I))
    (r := (1 / 10 ^ 250 : ℚ)) hfiniteBox' hdiff'
  simpa [c5RationalZetaCenteredNodeBoxWithTable] using hcontained

theorem c5RationalZetaCenteredNodeBox_contains {nLog nExp p : ℕ}
    {a b : ℚ} (haLo : (2 / 5 : ℝ) ≤ (a : ℝ))
    (haHi : (a : ℝ) ≤ 3 / 5) (hbLo : (0 : ℝ) ≤ (b : ℝ))
    (hbHi : (b : ℝ) ≤ 128 / 100000)
    (hden : (a - 1) ^ 2 + b ^ 2 ≠ 0)
    (hnLog : 0 < nLog) (hnExp : 0 < nExp) :
    (c5RationalZetaCenteredNodeBox nLog nExp p a b).contains
      (riemannZeta ((a : ℂ) + (b : ℂ) * Complex.I)) := by
  apply c5RationalZetaCenteredNodeBoxWithTable_contains
    (c5BernoulliPrimeTable 601)
  · simp [c5BernoulliPrimeTable_size]
  · intro i hi
    have hi' : i < 601 := by
      simpa [c5BernoulliPrimeTable_size] using hi
    exact c5BernoulliPrimeTable_getD 601 i hi'
  · exact haLo
  · exact haHi
  · exact hbLo
  · exact hbHi
  · exact hden
  · exact hnLog
  · exact hnExp

#print axioms c5RationalZetaCenteredHeadBox_contains
#print axioms c5RationalZetaCenteredBasePowerBox_contains
#print axioms c5RationalZetaCenteredNodeBox_contains
#print axioms c5RationalZetaCenteredNodeBoxWithTable_contains

end CarrySigmaObstruction
