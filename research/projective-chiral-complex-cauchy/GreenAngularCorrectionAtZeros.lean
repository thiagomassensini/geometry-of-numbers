import CPFormal.Analytic.CpNativeCarryAngularCorrectionExactLimit
import Mathlib.Tactic

/-!
# Genuine zero: angular Green correction is eventually strictly negative

This uses the ORIGINAL one-sided angular correction, not a synthetic
fitted remainder. The scalar Genuine angular pairing tends to zero, but
the positive reflected Green bulk has a nonzero limit. The correction
must tend to the exact negative Green bulk. We record its strict
eventual real-part sign, and rule out tending to zero.

The radially SCALED correction is a different object: it may vanish on
the critical line. Do not infer a global all-zero statement from this file.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

theorem genuine_zero_angular_green_correction_real_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ => (finiteCanonicalAngularGreenCorrection M s).re)
      atTop (nhds (-infiniteReflectedGreenEnergy s)) := by
  have h := finiteCanonicalAngularGreenCorrection_tendsto_neg_infinitePairing_of_genuine_zero
    hs hzero
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa [infiniteReflectedGreenEnergy, Function.comp_def] using hreal

/-- The correction keeps at least half of the positive infinite bulk,
with the NEGATIVE sign, for all sufficiently large cutoffs. -/
theorem genuine_zero_angular_green_correction_eventually_negative
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    ∀ᶠ M : ℕ in atTop,
      (finiteCanonicalAngularGreenCorrection M s).re <
        -infiniteReflectedGreenEnergy s / 2 := by
  have hpositive : 0 < infiniteReflectedGreenEnergy s :=
    infiniteReflectedGreenEnergy_pos hs
  have hstrict :
      -infiniteReflectedGreenEnergy s <
        -infiniteReflectedGreenEnergy s / 2 := by
    linarith
  exact (genuine_zero_angular_green_correction_real_tendsto hs hzero).eventually
    (Iio_mem_nhds hstrict)

/-- At an actual Genuine zero, the unscaled correction does NOT close to
zero. This pinpoints exactly which Green transport premise is missing. -/
theorem genuine_zero_angular_green_correction_not_tendsto_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    ¬ Tendsto (fun M : ℕ => finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0) := by
  intro hzeroCorr
  have hneg := finiteCanonicalAngularGreenCorrection_tendsto_neg_infinitePairing_of_genuine_zero
    hs hzero
  have heq := tendsto_nhds_unique hneg hzeroCorr
  have hnonzero : infiniteReflectedGradientPairing s ≠ 0 :=
    infiniteReflectedGradientPairing_ne_zero hs
  exact hnonzero (neg_eq_zero.mp heq)

end

end CPFormal.Analytic.Cp

#print axioms CPFormal.Analytic.Cp.genuine_zero_angular_green_correction_eventually_negative
#print axioms CPFormal.Analytic.Cp.genuine_zero_angular_green_correction_not_tendsto_zero
