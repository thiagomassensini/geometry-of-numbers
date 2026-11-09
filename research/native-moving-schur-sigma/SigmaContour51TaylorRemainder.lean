import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic
import ZetaLean.IntervalCExp

/-!
# Kernel-checked Cauchy coefficient budgets for contour Taylor models

The Arb contour computation uses Cauchy estimates for Taylor coefficients and then sums the
geometric tail. This module formalizes the coefficient part directly from Mathlib's Cauchy
estimate. It deliberately does not claim that any particular zeta/digamma Taylor coefficients
or contour boxes have been enclosed; those require a separate evaluator certificate.
-/

namespace CarrySigmaObstruction

open Complex Metric
open ZetaLean

noncomputable section
set_option maxHeartbeats 1000000

/-- The `n`th Taylor coefficient, in the convention used by Mathlib's complex Taylor series. -/
def contourTaylorCoefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f c

/-- The Taylor polynomial through degree `N` at `c`. -/
def contourTaylorPolynomial (f : ℂ → ℂ) (c z : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1),
    contourTaylorCoefficient f c k * (z - c) ^ k

/-- The Taylor polynomial of the derivative through degree `N-1`. -/
def contourTaylorDerivativePolynomial (f : ℂ → ℂ) (c z : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N,
    contourTaylorCoefficient (deriv f) c k * (z - c) ^ k

/-- A uniform boundary bound for an analytic function gives the standard Cauchy bound
`M / r^n` for every Taylor coefficient at the center. -/
theorem contourTaylorCoefficient_norm_le {f : ℂ → ℂ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : DiffContOnCl ℂ f (Metric.ball c r))
    (hM : ∀ w ∈ Metric.sphere c r, ‖f w‖ ≤ M) (n : ℕ) :
    ‖contourTaylorCoefficient f c n‖ ≤ M / r ^ n := by
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hr hf hM
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hnorm : ‖contourTaylorCoefficient f c n‖ =
      ((n.factorial : ℝ)⁻¹) * ‖iteratedDeriv n f c‖ := by
    simp [contourTaylorCoefficient]
  rw [hnorm]
  calc
    ((n.factorial : ℝ)⁻¹) * ‖iteratedDeriv n f c‖ ≤
        ((n.factorial : ℝ)⁻¹) * ((n.factorial : ℝ) * M / r ^ n) :=
      mul_le_mul_of_nonneg_left hcauchy (inv_nonneg.mpr hfact.le)
    _ = M / r ^ n := by field_simp [ne_of_gt hfact]

/-- The derivative Taylor coefficient of order `n` is bounded by the Cauchy estimate for
the original function at order `n+1`. The extra factor `(n+1)/r` is the usual derivative
loss in the Taylor tail. -/
theorem contourTaylorDerivativeCoefficient_norm_le {f : ℂ → ℂ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : DiffContOnCl ℂ f (Metric.ball c r))
    (hM : ∀ w ∈ Metric.sphere c r, ‖f w‖ ≤ M) (n : ℕ) :
    ‖contourTaylorCoefficient (deriv f) c n‖ ≤
      ((n + 1 : ℕ) : ℝ) * M / r ^ (n + 1) := by
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (n + 1) hr hf hM
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  rw [contourTaylorCoefficient, ← iteratedDeriv_succ']
  have hnorm : ‖(n.factorial : ℂ)⁻¹ * iteratedDeriv (n + 1) f c‖ =
      ((n.factorial : ℝ)⁻¹) * ‖iteratedDeriv (n + 1) f c‖ := by
    simp
  rw [hnorm]
  calc
    ((n.factorial : ℝ)⁻¹) * ‖iteratedDeriv (n + 1) f c‖ ≤
        ((n.factorial : ℝ)⁻¹) *
          (((n + 1).factorial : ℝ) * M / r ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left hcauchy (inv_nonneg.mpr hfact.le)
    _ = ((n + 1 : ℕ) : ℝ) * M / r ^ (n + 1) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp [ne_of_gt hfact]

/-- Closed form of the weighted geometric series that bounds the derivative tail after
retaining Taylor terms of the original function through degree `N`. -/
theorem contourTaylorWeightedGeometricShift_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (N : ℕ) :
    (∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N)) =
      q ^ N * (((N + 1 : ℕ) : ℝ) - (N : ℝ) * q) / (1 - q) ^ 2 := by
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have hqnorm : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hweighted := hasSum_coe_mul_geometric_of_norm_lt_one hqnorm
  have hsumSplit :
      (∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N)) =
        ∑' j : ℕ, (((N + 1 : ℕ) : ℝ) * q ^ N * q ^ j +
          q ^ N * ((j : ℝ) * q ^ j)) := by
    apply tsum_congr
    intro j
    rw [pow_add]
    push_cast
    ring
  have hA : Summable (fun j : ℕ => ((N + 1 : ℕ) : ℝ) * q ^ N * q ^ j) :=
    hgeom.mul_left _
  have hB : Summable (fun j : ℕ => q ^ N * ((j : ℝ) * q ^ j)) :=
    hweighted.summable.mul_left _
  have hsumParts :
      (∑' j : ℕ, (((N + 1 : ℕ) : ℝ) * q ^ N * q ^ j +
          q ^ N * ((j : ℝ) * q ^ j))) =
        (∑' j : ℕ, ((N + 1 : ℕ) : ℝ) * q ^ N * q ^ j) +
          (∑' j : ℕ, q ^ N * ((j : ℝ) * q ^ j)) := by
    simpa using (hA.hasSum.add hB.hasSum).tsum_eq
  rw [hsumSplit, hsumParts]
  rw [hgeom.tsum_mul_left, hweighted.summable.tsum_mul_left]
  rw [tsum_geometric_of_lt_one hq0 hq1, hweighted.tsum_eq]
  field_simp [ne_of_lt hq1]
  push_cast
  ring_nf

/-- The exact Taylor tail on a smaller disk is bounded by its Cauchy geometric majorant. The
parameter `q` can be chosen as any rationally certified upper bound for `‖z-c‖/r`; this isolates
the analytic remainder from the separate interval enclosures of the Taylor coefficients. -/
theorem contourTaylorRemainder_norm_le {f : ℂ → ℂ} {c z : ℂ} {r M q : ℝ} {N : ℕ}
    (hr : 0 < r) (hf : DiffContOnCl ℂ f (Metric.ball c r))
    (hM : ∀ w ∈ Metric.sphere c r, ‖f w‖ ≤ M)
    (hz : z ∈ Metric.ball c r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdelta : ‖z - c‖ ≤ q * r) :
    ‖f z - contourTaylorPolynomial f c z N‖ ≤ M * q ^ (N + 1) / (1 - q) := by
  let term : ℕ → ℂ := fun k =>
    contourTaylorCoefficient f c k * (z - c) ^ k
  have hTaylor : HasSum term (f z) := by
    simpa [term, contourTaylorCoefficient, smul_eq_mul, mul_assoc, mul_left_comm,
      mul_comm] using
      (Complex.hasSum_taylorSeries_on_ball (f := f) hf.differentiableOn hz)
  have htail := (hasSum_nat_add_iff' (N + 1)).mpr hTaylor
  have hM0 : 0 ≤ M := by
    let w : ℂ := c + (r : ℂ)
    have hw : w ∈ Metric.sphere c r := by
      rw [mem_sphere_iff_norm]
      simp [w, abs_of_pos hr]
    exact (norm_nonneg (f w)).trans (hM w hw)
  have htailBound (j : ℕ) :
      ‖term (j + (N + 1))‖ ≤ M * q ^ (j + (N + 1)) := by
    have hcoeff := contourTaylorCoefficient_norm_le hr hf hM (j + (N + 1))
    have hpow := pow_le_pow_left₀ (norm_nonneg (z - c)) hdelta (j + (N + 1))
    change ‖contourTaylorCoefficient f c (j + (N + 1)) *
      (z - c) ^ (j + (N + 1))‖ ≤ _
    rw [norm_mul, norm_pow]
    calc
      ‖contourTaylorCoefficient f c (j + (N + 1))‖ * ‖z - c‖ ^ (j + (N + 1)) ≤
          (M / r ^ (j + (N + 1))) * (q * r) ^ (j + (N + 1)) :=
        mul_le_mul hcoeff hpow (pow_nonneg (norm_nonneg (z - c)) _)
          (div_nonneg hM0 (pow_nonneg hr.le _))
      _ = M * q ^ (j + (N + 1)) := by
        field_simp [ne_of_gt hr]
        ring
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have hmajor : Summable (fun j : ℕ => M * q ^ (j + (N + 1))) := by
    have hbase := hgeom.mul_left (M * q ^ (N + 1))
    refine hbase.congr ?_
    intro j
    rw [pow_add]
    ring
  have hsumMajor :
      (∑' j : ℕ, M * q ^ (j + (N + 1))) = M * q ^ (N + 1) / (1 - q) := by
    calc
      (∑' j : ℕ, M * q ^ (j + (N + 1))) =
          ∑' j : ℕ, (M * q ^ (N + 1)) * q ^ j := by
            apply tsum_congr
            intro j
            rw [pow_add]
            ring
      _ = (M * q ^ (N + 1)) * (∑' j : ℕ, q ^ j) := hgeom.tsum_mul_left _
      _ = M * q ^ (N + 1) / (1 - q) := by
        rw [tsum_geometric_of_lt_one hq0 hq1]
        ring
  have hnormTail :
      ‖∑' j : ℕ, term (j + (N + 1))‖ ≤
        ∑' j : ℕ, M * q ^ (j + (N + 1)) := by
    calc
      ‖∑' j : ℕ, term (j + (N + 1))‖ ≤
          ∑' j : ℕ, ‖term (j + (N + 1))‖ :=
        norm_tsum_le_tsum_norm htail.summable.norm
      _ ≤ ∑' j : ℕ, M * q ^ (j + (N + 1)) :=
        htail.summable.norm.tsum_le_tsum htailBound hmajor
  have hrem : f z - contourTaylorPolynomial f c z N =
      ∑' j : ℕ, term (j + (N + 1)) := by
    simpa [contourTaylorPolynomial, term] using htail.tsum_eq.symm
  calc
    ‖f z - contourTaylorPolynomial f c z N‖ =
        ‖∑' j : ℕ, term (j + (N + 1))‖ := by rw [hrem]
    _ ≤ ∑' j : ℕ, M * q ^ (j + (N + 1)) := hnormTail
    _ = M * q ^ (N + 1) / (1 - q) := hsumMajor

/-- The derivative tail used by the Arb enclosure is certified from the same Cauchy bound.
The polynomial retains the derivative terms through degree `N-1`, corresponding to the derivative
of the original Taylor polynomial through degree `N`. -/
theorem contourTaylorDerivativeRemainder_norm_le {f : ℂ → ℂ} {c z : ℂ}
    {r M q : ℝ} {N : ℕ}
    (hr : 0 < r) (hf : DiffContOnCl ℂ f (Metric.ball c r))
    (hdf : DifferentiableOn ℂ (deriv f) (Metric.ball c r))
    (hM : ∀ w ∈ Metric.sphere c r, ‖f w‖ ≤ M)
    (hz : z ∈ Metric.ball c r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdelta : ‖z - c‖ ≤ q * r) :
    ‖deriv f z - contourTaylorDerivativePolynomial f c z N‖ ≤
      (M / r) * q ^ N *
        (((N + 1 : ℕ) : ℝ) - (N : ℝ) * q) / (1 - q) ^ 2 := by
  let term : ℕ → ℂ := fun k =>
    contourTaylorCoefficient (deriv f) c k * (z - c) ^ k
  have hTaylor : HasSum term (deriv f z) := by
    simpa [term, contourTaylorCoefficient, smul_eq_mul, mul_assoc, mul_left_comm,
      mul_comm] using
      (Complex.hasSum_taylorSeries_on_ball (f := deriv f) hdf hz)
  have htail := (hasSum_nat_add_iff' N).mpr hTaylor
  have hM0 : 0 ≤ M := by
    let w : ℂ := c + (r : ℂ)
    have hw : w ∈ Metric.sphere c r := by
      rw [mem_sphere_iff_norm]
      simp [w, abs_of_pos hr]
    exact (norm_nonneg (f w)).trans (hM w hw)
  have htailBound (j : ℕ) :
      ‖term (j + N)‖ ≤
        (M / r) * ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N) := by
    let k : ℕ := j + N
    have hcoeff := contourTaylorDerivativeCoefficient_norm_le hr hf hM k
    have hpow := pow_le_pow_left₀ (norm_nonneg (z - c)) hdelta k
    change ‖contourTaylorCoefficient (deriv f) c k * (z - c) ^ k‖ ≤
      (M / r) * ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N)
    rw [norm_mul, norm_pow]
    have hcoeffNonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) * M / r ^ (k + 1) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) hM0) (pow_nonneg hr.le _)
    calc
      ‖contourTaylorCoefficient (deriv f) c k‖ * ‖z - c‖ ^ k ≤
          (((k + 1 : ℕ) : ℝ) * M / r ^ (k + 1)) * (q * r) ^ k :=
        mul_le_mul hcoeff hpow (pow_nonneg (norm_nonneg (z - c)) _) hcoeffNonneg
      _ = (M / r) * ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N) := by
        dsimp [k]
        field_simp [ne_of_gt hr]
        ring
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have hqnorm : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hweighted := hasSum_coe_mul_geometric_of_norm_lt_one hqnorm
  have hA : Summable (fun j : ℕ => ((N + 1 : ℕ) : ℝ) * q ^ N * q ^ j) :=
    hgeom.mul_left _
  have hB : Summable (fun j : ℕ => q ^ N * ((j : ℝ) * q ^ j)) :=
    hweighted.summable.mul_left _
  have hparts : Summable (fun j : ℕ =>
      ((N + 1 : ℕ) : ℝ) * q ^ N * q ^ j + q ^ N * ((j : ℝ) * q ^ j)) :=
    hA.add hB
  have hshift : Summable (fun j : ℕ =>
      ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N)) := by
    refine hparts.congr ?_
    intro j
    rw [pow_add]
    push_cast
    ring
  have hmajor : Summable (fun j : ℕ =>
      (M / r) * ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N)) := by
    simpa [mul_assoc] using hshift.mul_left (M / r)
  have hsumMajor :
      (∑' j : ℕ, (M / r) * ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N)) =
        (M / r) * q ^ N *
          (((N + 1 : ℕ) : ℝ) - (N : ℝ) * q) / (1 - q) ^ 2 := by
    calc
      (∑' j : ℕ, (M / r) * ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N)) =
          ∑' j : ℕ, (M / r) * (((j + N + 1 : ℕ) : ℝ) * q ^ (j + N)) := by
        apply tsum_congr
        intro j
        ring
      _ = (M / r) *
            (∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N)) :=
        hshift.tsum_mul_left _
      _ = (M / r) * q ^ N *
          (((N + 1 : ℕ) : ℝ) - (N : ℝ) * q) / (1 - q) ^ 2 := by
        rw [contourTaylorWeightedGeometricShift_sum hq0 hq1 N]
        ring
  have hnormTail :
      ‖∑' j : ℕ, term (j + N)‖ ≤
        ∑' j : ℕ, (M / r) * ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N) := by
    calc
      ‖∑' j : ℕ, term (j + N)‖ ≤ ∑' j : ℕ, ‖term (j + N)‖ :=
        norm_tsum_le_tsum_norm htail.summable.norm
      _ ≤ ∑' j : ℕ, (M / r) * ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N) :=
        htail.summable.norm.tsum_le_tsum htailBound hmajor
  have hrem : deriv f z - contourTaylorDerivativePolynomial f c z N =
      ∑' j : ℕ, term (j + N) := by
    simpa [contourTaylorDerivativePolynomial, term] using htail.tsum_eq.symm
  calc
    ‖deriv f z - contourTaylorDerivativePolynomial f c z N‖ =
        ‖∑' j : ℕ, term (j + N)‖ := by rw [hrem]
    _ ≤ ∑' j : ℕ, (M / r) * ((j + N + 1 : ℕ) : ℝ) * q ^ (j + N) := hnormTail
    _ = (M / r) * q ^ N *
        (((N + 1 : ℕ) : ℝ) - (N : ℝ) * q) / (1 - q) ^ 2 := hsumMajor

/-- Rectangle evaluation of a finite Taylor polynomial. `n` counts the coefficients retained. -/
def contourTaylorIntervalPolynomial (coeff : ℕ → ComplexInterval)
    (delta : ComplexInterval) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 0 0
  | n + 1 =>
      (contourTaylorIntervalPolynomial coeff delta n).add
        ((coeff n).mul (ComplexInterval.powI delta n))

/-- A rational complex interval evaluation of the finite Taylor polynomial contains its exact
value whenever every coefficient box and the displacement box contain the corresponding values. -/
theorem contourTaylorIntervalPolynomial_contains {coeff : ℕ → ComplexInterval}
    {coeffExact : ℕ → ℂ} {deltaBox : ComplexInterval} {delta : ℂ}
    (hdelta : deltaBox.contains delta) :
    ∀ n : ℕ, (∀ k < n, (coeff k).contains (coeffExact k)) →
      (contourTaylorIntervalPolynomial coeff deltaBox n).contains
        (∑ k ∈ Finset.range n, coeffExact k * delta ^ k)
  | 0, _ => by
      simp [contourTaylorIntervalPolynomial, ComplexInterval.contains_zero]
  | n + 1, hcoeff => by
      rw [contourTaylorIntervalPolynomial, Finset.sum_range_succ]
      apply ComplexInterval.contains_add
      · exact contourTaylorIntervalPolynomial_contains hdelta n
          (fun k hk => hcoeff k (by omega))
      · exact ComplexInterval.contains_mul (hcoeff n (by omega))
          (ComplexInterval.contains_powI hdelta n)

/-- If rational boxes contain all exact Taylor coefficients and the displacement, then inflating
the interval Taylor polynomial by a proved Cauchy remainder encloses the original function value.
This is the generic bridge from a validated finite Taylor evaluator to the analytic function; the
caller still has to prove the coefficient-box and displacement inclusions. -/
theorem contourTaylorIntervalPolynomial_inflate_contains {f : ℂ → ℂ}
    {c z : ℂ} {coeff : ℕ → ComplexInterval} {deltaBox : ComplexInterval}
    {err : ℚ} {N : ℕ}
    (hcoeff : ∀ k < N + 1,
      (coeff k).contains (contourTaylorCoefficient f c k))
    (hdelta : deltaBox.contains (z - c))
    (hrem : ‖f z - contourTaylorPolynomial f c z N‖ ≤ (err : ℝ)) :
    (contourTaylorIntervalPolynomial coeff deltaBox (N + 1)).inflate err |>.contains (f z) := by
  have hpoly :
      (contourTaylorIntervalPolynomial coeff deltaBox (N + 1)).contains
        (contourTaylorPolynomial f c z N) := by
    simpa [contourTaylorPolynomial] using
      (contourTaylorIntervalPolynomial_contains hdelta (N + 1) hcoeff)
  exact ComplexInterval.contains_inflate hpoly hrem

/-- Interval enclosure of the derivative polynomial after inflating by its separately proved
Taylor/Cauchy remainder. `N` is the number of derivative coefficients retained. -/
theorem contourTaylorDerivativeIntervalPolynomial_inflate_contains {f : ℂ → ℂ}
    {c z : ℂ} {coeff : ℕ → ComplexInterval} {deltaBox : ComplexInterval}
    {err : ℚ} {N : ℕ}
    (hcoeff : ∀ k < N,
      (coeff k).contains (contourTaylorCoefficient (deriv f) c k))
    (hdelta : deltaBox.contains (z - c))
    (hrem : ‖deriv f z - contourTaylorDerivativePolynomial f c z N‖ ≤ (err : ℝ)) :
    (contourTaylorIntervalPolynomial coeff deltaBox N).inflate err |>.contains (deriv f z) := by
  have hpoly :
      (contourTaylorIntervalPolynomial coeff deltaBox N).contains
        (contourTaylorDerivativePolynomial f c z N) := by
    simpa [contourTaylorDerivativePolynomial] using
      (contourTaylorIntervalPolynomial_contains hdelta N hcoeff)
  exact ComplexInterval.contains_inflate hpoly hrem

#print axioms contourTaylorCoefficient_norm_le
#print axioms contourTaylorDerivativeCoefficient_norm_le
#print axioms contourTaylorWeightedGeometricShift_sum
#print axioms contourTaylorRemainder_norm_le
#print axioms contourTaylorDerivativeRemainder_norm_le
#print axioms contourTaylorIntervalPolynomial_contains
#print axioms contourTaylorIntervalPolynomial_inflate_contains
#print axioms contourTaylorDerivativeIntervalPolynomial_inflate_contains

end
end CarrySigmaObstruction
