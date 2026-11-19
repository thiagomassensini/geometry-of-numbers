import CPFormal.Analytic.CpGenuineFirstOrthogonalMultibaseGreen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Quantitative separation of the aligned Green flux

The identity for a single camera retains a strictly positive reflected bulk.
At a Genuine zero the boundary tends to zero. The lower bound below keeps the
dependence on the transverse displacement and the first reflected edge.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

/-- The first reflected edge gives a lower bound at every aligned cutoff,
up to the actual signed boundary of that cutoff. -/
theorem alignedGreenFlux_abs_ge_first_pairing_sub_boundary
    (p q L : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    |cpRadialDifference p (criticalDisplacement s.re)| *
        (finiteReflectedGradientPairing 1 s).re -
        |finiteBracketCoupledSignedBoundary (crossPrimeAlignedCutoff q L) s| ≤
      |finiteBracketCoupledCpGreenFlux p (crossPrimeAlignedCutoff q L) s| := by
  let c := cpRadialDifference p (criticalDisplacement s.re)
  let cut := crossPrimeAlignedCutoff q L
  let E := (finiteReflectedGradientPairing cut s).re
  let E₁ := (finiteReflectedGradientPairing 1 s).re
  let B := finiteBracketCoupledSignedBoundary cut s
  change |c| * E₁ - |B| ≤ |finiteBracketCoupledCpGreenFlux p cut s|
  have hfirst : 0 < E₁ :=
    finiteReflectedGradientPairing_re_pos (by decide) hs
  have hbulk : E₁ ≤ E :=
    finiteReflectedGradientPairing_re_monotone hs (crossPrimeAlignedCutoff_pos q L hq hqodd)
  rw [finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing p cut hp s]
  change |c| * E₁ - |B| ≤ |c * E + B|
  have htriangle : |c * E| ≤ |c * E + B| + |B| := by
    rcases le_total 0 (c * E) with hpos | hneg
    · rw [abs_of_nonneg hpos]
      linarith [le_abs_self (c * E + B), neg_le_abs B]
    · rw [abs_of_nonpos hneg]
      linarith [neg_le_abs (c * E + B), le_abs_self B]
  rw [abs_mul, abs_of_nonneg (hfirst.le.trans hbulk)] at htriangle
  linarith [mul_le_mul_of_nonneg_left hbulk (abs_nonneg c)]

/-- At a Genuine zero the error is arbitrarily small at all sufficiently
large aligned cutoffs. This statement uses no Green closure hypothesis. -/
theorem alignedGreenFlux_eventually_abs_ge_first_pairing_sub
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) (hzero : genuineContinuation s = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop,
      |cpRadialDifference p (criticalDisplacement s.re)| *
          (finiteReflectedGradientPairing 1 s).re - ε ≤
        |finiteBracketCoupledCpGreenFlux p (crossPrimeAlignedCutoff q L) s| := by
  have hboundary :=
    (finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero hs hzero).comp
      (crossPrimeAlignedCutoff_tendsto_atTop q hq.pos)
  have hsmall := (Metric.tendsto_nhds.mp hboundary) ε hε
  filter_upwards [hsmall] with L hL
  have hL' : |finiteBracketCoupledSignedBoundary (crossPrimeAlignedCutoff q L) s| < ε := by
    simpa [Function.comp_def, Real.dist_eq] using hL
  linarith [alignedGreenFlux_abs_ge_first_pairing_sub_boundary p q L hp hq hqodd hs]

/-- A single camera with vanishing flux along any cofinal subsequence forces
the critical displacement to vanish at a Genuine zero. -/
theorem criticalDisplacement_eq_zero_of_alignedGreenFlux_subsequence
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) (hzero : genuineContinuation s = 0)
    (cutoff : ℕ → ℕ) (hcofinal : Tendsto cutoff atTop atTop)
    (hflux : Tendsto (fun n =>
      finiteBracketCoupledCpGreenFlux p (crossPrimeAlignedCutoff q (cutoff n)) s)
      atTop (nhds 0)) :
    criticalDisplacement s.re = 0 := by
  by_contra hoff
  let C := |cpRadialDifference p (criticalDisplacement s.re)| *
    (finiteReflectedGradientPairing 1 s).re
  have hradial : cpRadialDifference p (criticalDisplacement s.re) ≠ 0 :=
    fun h => hoff ((cpRadialDifference_eq_zero_iff p hp _).mp h)
  have hC : 0 < C := mul_pos (abs_pos.mpr hradial)
    (finiteReflectedGradientPairing_re_pos (by decide) hs)
  have hhalf : 0 < C / 2 := half_pos hC
  have hsep := (alignedGreenFlux_eventually_abs_ge_first_pairing_sub
    p q hp hq hqodd hs hzero hhalf).filter_mono hcofinal
  have hsep' : ∀ᶠ n : ℕ in atTop, C / 2 ≤
      |finiteBracketCoupledCpGreenFlux p (crossPrimeAlignedCutoff q (cutoff n)) s| := by
    filter_upwards [hsep] with n hn
    change C - C / 2 ≤ _ at hn
    linarith
  have habs := hflux.abs
  rw [abs_zero] at habs
  exact (not_le_of_gt hhalf) (ge_of_tendsto habs hsep')


/-- The radial factor is odd and grows at least linearly in the absolute
transverse displacement. -/
theorem abs_cpRadialDifference_ge_two_mul_log
    (p : ℕ) (hp : Nat.Prime p) (d : ℝ) :
    2 * |d| * Real.log p ≤ |cpRadialDifference p d| := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog := Real.log_pos hp1
  let x := Real.log p * d
  have hfactor : cpRadialDifference p d = 2 * Real.sinh x := by
    rw [cpRadialDifference, Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0,
      Real.sinh_eq]
    dsimp only [x]
    rw [mul_neg]
    ring
  have hbound : |x| ≤ |Real.sinh x| := by
    rcases le_total 0 x with hpos | hneg
    · rw [abs_of_nonneg hpos]
      exact (Real.self_le_sinh_iff.mpr hpos).trans (le_abs_self _)
    · rw [abs_of_nonpos hneg]
      have h := Real.self_le_sinh_iff.mpr (neg_nonneg.mpr hneg)
      rw [Real.sinh_neg] at h
      exact h.trans (neg_le_abs _)
  rw [hfactor, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  dsimp only [x] at hbound
  rw [abs_mul, abs_of_pos hlog] at hbound
  linarith

end CPFormal.Analytic.Cp

#print axioms CPFormal.Analytic.Cp.alignedGreenFlux_abs_ge_first_pairing_sub_boundary
#print axioms CPFormal.Analytic.Cp.alignedGreenFlux_eventually_abs_ge_first_pairing_sub
#print axioms CPFormal.Analytic.Cp.criticalDisplacement_eq_zero_of_alignedGreenFlux_subsequence
#print axioms CPFormal.Analytic.Cp.abs_cpRadialDifference_ge_two_mul_log
