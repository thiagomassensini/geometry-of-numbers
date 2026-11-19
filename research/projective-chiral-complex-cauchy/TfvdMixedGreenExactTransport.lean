import CPFormal.Analytic.CpTfvdSeededReconstructionBridgeProbe
import CPFormal.Analytic.CpFiniteGenuineOneSidedGreenBudget
import CPFormal.Analytic.CpNativeCarryAngularCorrectionExactLimit
import Mathlib.Tactic

/-!
# Exact TFVD transport of the reflected Dirichlet gradient pairing

This module keeps:
* the original ordinary gradient core of the genuine Dirichlet wave;
* the reflected parameter 1-conj(s) and both distinct edges;
* the enriched TFVD analysis and its ORIGINAL Green/return reconstruction;
* the angular scalar ledger, including the nonzero correction.

The finite mixed Green bulk is preserved exactly under reconstruction.
The zero Genuine kills the scalar readout, NOT this bulk. This is
not a proof of boundary-domain isotropy or all-zero confinement.
-/

open scoped Topology BigOperators ComplexConjugate

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Realization of the FINITE reflected-gradient Green bulk after enriched
TFVD analysis and exact inverse reconstruction of both native states. -/
def tfvdReconstructedReflectedGradientPairing
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    (starRingEnd ℂ)
      ((nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (c2DirichletGradientPrefixEnrichedAnalysis q S s N)) n) *
      ((nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (c2DirichletGradientPrefixEnrichedAnalysis q S
          (reflectedParameter s) N)) n)

/-- Exact preservation of the MIXED Green bulk. This is not a condition
imposed on the boundary relation: it holds for all s, N, admissible q, S. -/
theorem tfvdReconstructedReflectedGradientPairing_eq
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (s : ℂ) (N : ℕ) :
    tfvdReconstructedReflectedGradientPairing q hqpos hq1 S s N =
      finiteReflectedGradientPairing N s := by
  unfold tfvdReconstructedReflectedGradientPairing finiteReflectedGradientPairing
  apply Finset.sum_congr rfl
  intro n hn
  have hlt : n < N := Finset.mem_range.mp hn
  have hleft :
      (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (c2DirichletGradientPrefixEnrichedAnalysis q S s N)) n =
        positiveDirichletGradient s n := by
    rw [c2DirichletGradientPrefixEnrichedAnalysis_reconstruction q hqpos hq1 S s N]
    simp [c2DirichletGradientPrefixCore_apply, hlt]
  have hright :
      (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (c2DirichletGradientPrefixEnrichedAnalysis q S
          (reflectedParameter s) N)) n =
        positiveDirichletGradient (reflectedParameter s) n := by
    rw [c2DirichletGradientPrefixEnrichedAnalysis_reconstruction q hqpos hq1 S (reflectedParameter s) N]
    simp [c2DirichletGradientPrefixCore_apply, hlt]
  rw [hleft, hright]

/-- Positive bulk survives faithful TFVD transport at EVERY nonempty cutoff. -/
theorem tfvdReconstructedReflectedGradientPairing_re_pos
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    {N : ℕ} (hN : 0 < N) :
    0 < (tfvdReconstructedReflectedGradientPairing q hqpos hq1 S s N).re := by
  rw [tfvdReconstructedReflectedGradientPairing_eq]
  exact finiteReflectedGradientPairing_re_pos hN hs

/-- The reconstructed pair has the ORIGINAL positive infinite Green limit. -/
theorem tfvdReconstructedReflectedGradientPairing_re_tendsto
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun N : ℕ =>
        (tfvdReconstructedReflectedGradientPairing q hqpos hq1 S s N).re)
      atTop (nhds (infiniteReflectedGreenEnergy s)) := by
  simpa only [tfvdReconstructedReflectedGradientPairing_eq]
    using finiteReflectedGradientPairing_re_tendsto_infiniteEnergy hs

/-- The true scalar-versus-Green ledger: the scalar bracket trace equals
the TFVD-reconstructed gradient pairing PLUS the angular correction.
No terms are thrown away during the finite transport. -/
theorem finiteCanonicalAngularScalarPairing_eq_tfvd_mixed_add_correction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularScalarPairing M s =
      tfvdReconstructedReflectedGradientPairing q hqpos hq1 S s (3 * M) +
        finiteCanonicalAngularGreenCorrection M s := by
  rw [finiteCanonicalAngularScalarPairing_eq_green_add_correction]
  rw [tfvdReconstructedReflectedGradientPairing_eq]

/-- At a Genuine zero, the scalar bracket pairing closes while the
TFVD-reconstructed Green bulk remains strictly POSITIVE in the limit. -/
theorem genuine_zero_tfvd_mixed_green_survival
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ => finiteCanonicalAngularScalarPairing M s)
      atTop (nhds 0) ∧
    Tendsto
      (fun M : ℕ =>
        (tfvdReconstructedReflectedGradientPairing
          q hqpos hq1 S s (3 * M)).re)
      atTop (nhds (infiniteReflectedGreenEnergy s)) ∧
    0 < infiniteReflectedGreenEnergy s := by
  refine ⟨finiteCanonicalAngularScalarPairing_tendsto_zero_of_genuine_zero
    hs hzero, ?_, infiniteReflectedGreenEnergy_pos hs⟩
  have hM : Tendsto (fun M : ℕ => 3 * M) atTop atTop :=
    tendsto_three_mul_atTop
  exact (tfvdReconstructedReflectedGradientPairing_re_tendsto
    q hqpos hq1 S hs).comp hM

/-- Even at a Genuine zero the reconstructed mixed Green bulk does NOT
converge to zero; it converges to a nonzero source-determined pairing. -/
theorem genuine_zero_tfvd_mixed_green_not_tendsto_zero
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (_hzero : genuineContinuation s = 0) :
    ¬ Tendsto
      (fun M : ℕ =>
        tfvdReconstructedReflectedGradientPairing q hqpos hq1 S s (3 * M))
      atTop (nhds 0) := by
  intro hzeroBulk
  have hlim :
      Tendsto
        (fun M : ℕ =>
          tfvdReconstructedReflectedGradientPairing q hqpos hq1 S s (3 * M))
        atTop (nhds (infiniteReflectedGradientPairing s)) := by
    simpa only [tfvdReconstructedReflectedGradientPairing_eq, Function.comp_def] using
      (finiteReflectedGradientPairing_tendsto_infinite hs).comp
        tendsto_three_mul_atTop
  have hnonzero : infiniteReflectedGradientPairing s ≠ 0 :=
    infiniteReflectedGradientPairing_ne_zero hs
  exact hnonzero (tendsto_nhds_unique hlim hzeroBulk)

/-- The ENTIRE polarized Green ledger still closes at a Genuine zero:
the angular correction cancels the nonzero reconstructed mixed bulk.
We do not drop the correction before reconstruction or before the limit. -/
theorem genuine_zero_tfvd_mixed_green_full_ledger_tendsto_zero
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ =>
        tfvdReconstructedReflectedGradientPairing q hqpos hq1 S s (3 * M) +
          finiteCanonicalAngularGreenCorrection M s)
      atTop (nhds 0) := by
  have hscalar :=
    finiteCanonicalAngularScalarPairing_tendsto_zero_of_genuine_zero hs hzero
  convert hscalar using 1
  funext M
  exact (finiteCanonicalAngularScalarPairing_eq_tfvd_mixed_add_correction
    q hqpos hq1 S M s).symm

end

end CPFormal.Analytic.Cp

#print axioms CPFormal.Analytic.Cp.genuine_zero_tfvd_mixed_green_not_tendsto_zero
#print axioms CPFormal.Analytic.Cp.genuine_zero_tfvd_mixed_green_full_ledger_tendsto_zero
#print axioms CPFormal.Analytic.Cp.tfvdReconstructedReflectedGradientPairing_eq
#print axioms CPFormal.Analytic.Cp.tfvdReconstructedReflectedGradientPairing_re_pos
#print axioms CPFormal.Analytic.Cp.finiteCanonicalAngularScalarPairing_eq_tfvd_mixed_add_correction
#print axioms CPFormal.Analytic.Cp.genuine_zero_tfvd_mixed_green_survival
