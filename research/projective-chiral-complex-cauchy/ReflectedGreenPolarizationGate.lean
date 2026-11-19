import CPFormal.Analytic.CpNativeCarryReflectedLogBoundarySymmetry
import CPFormal.Analytic.CpGenuineRiemannZetaIdentification
import CPFormal.Analytic.CpGenuineReflectionRigidity
import Mathlib.Tactic

/-!
# Polarized reflected Green test: what linear bracket closure does and does not imply

The scalar Cp chart is linear in its input samples, so the combination
f_z + I * f_conj(z) also closes whenever both waves close.

The characteristic flux of this combination is the linear combination
of the reflected fluxes. Its ORIENTED GREEN SELF PAIRING is generically
NONZERO, even though both component self pairings vanish identically.

This isolates exactly the extra operator-domain/Green-symmetry premise:
the bracket kernel is not yet known to be isotropic for this Green form.
No off-critical Genuine zero is assumed or constructed.
-/

open scoped BigOperators ComplexConjugate Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Linear superposition of both reflected characteristic fluxes. -/
def reflectedPolarizedFlux (z : ℂ) : NativeCarryReflectedLogBoundary :=
  (z + Complex.I * conj z, conj z + Complex.I * z)

/-- The superposition really combines the existing two fluxes, not a new
parameter chosen to have the desired Green sign. -/
theorem reflectedPolarizedFlux_eq_sum (z : ℂ) :
    reflectedPolarizedFlux z =
      nativeCarryReflectedLogBoundaryFlux z +
        Complex.I • nativeCarryReflectedLogBoundaryFlux (conj z) := by
  ext <;> simp [reflectedPolarizedFlux, nativeCarryReflectedLogBoundaryFlux_eq]

/-- Both endpoint VALUES are diagonal for all z, including non-real time. -/
theorem reflectedPolarizedValue_is_diagonal (z : ℂ) :
    (nativeCarryReflectedLogBoundaryValue z +
      Complex.I • nativeCarryReflectedLogBoundaryValue (conj z)) ∈
        nativeCarryReflectedLogDiagonal := by
  rw [mem_nativeCarryReflectedLogDiagonal]
  simp

/-- Exact polarization formula. Neither diagonal self term detects the
transverse coordinate; the superposition does. -/
theorem reflectedPolarizedFlux_green_eq_mixed (z : ℂ) :
    nativeCarryReflectedLogBoundaryForm
        (reflectedPolarizedFlux z) (reflectedPolarizedFlux z) =
      -2 * Complex.I * (z ^ 2 - (conj z) ^ 2) := by
  simp [nativeCarryReflectedLogBoundaryForm, reflectedPolarizedFlux,
    map_add, map_mul]
  ring

/-- The superposed Green self form vanishes exactly at real carry time,
provided the spectral height is nonzero. -/
theorem reflectedPolarizedFlux_green_zero_iff
    {z : ℂ} (hz : z.re ≠ 0) :
    nativeCarryReflectedLogBoundaryForm
        (reflectedPolarizedFlux z) (reflectedPolarizedFlux z) = 0
      ↔ z.im = 0 := by
  rw [reflectedPolarizedFlux_green_eq_mixed]
  constructor
  · intro h
    have hcoef : (-2 : ℂ) * Complex.I ≠ 0 := by simp
    have hmix : z ^ 2 - (conj z) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hcoef
    have him := congrArg Complex.im hmix
    simp only [Complex.sub_im, pow_two, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.zero_im] at him
    have hmul : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hz
  · intro him
    have hconj : conj z = z := by
      apply Complex.ext <;> simp [him]
    simp [hconj]

/-- A complex linear boundary space whose EVERY state has vanishing
oriented Green self-pairing. This is the minimum symmetry premise used
below; maximality or a completed self-adjoint operator is not assumed. -/
def ReflectedGreenSelfIsotropic (D : Submodule ℂ NativeCarryReflectedLogBoundary) :
    Prop :=
  ∀ v, v ∈ D → nativeCarryReflectedLogBoundaryForm v v = 0

/-- At nonreal carry time with nonzero height, no complex-linear
Green-isotropic boundary subspace can contain BOTH reflected fluxes.
The obstruction is already present before any infinite Green limit.
This statement does not assert that bracket closure supplies such a
subspace; that is the remaining analytic domain-transport problem. -/
theorem no_isotropic_submodule_containing_reflected_pair
    (z : ℂ) (hre : z.re ≠ 0) (him : z.im ≠ 0)
    (D : Submodule ℂ NativeCarryReflectedLogBoundary)
    (hiso : ReflectedGreenSelfIsotropic D)
    (hdirect : nativeCarryReflectedLogBoundaryFlux z ∈ D)
    (hreflected : nativeCarryReflectedLogBoundaryFlux (conj z) ∈ D) :
    False := by
  have hsuper : reflectedPolarizedFlux z ∈ D := by
    rw [reflectedPolarizedFlux_eq_sum]
    exact D.add_mem hdirect (D.smul_mem Complex.I hreflected)
  have hgreen : nativeCarryReflectedLogBoundaryForm
      (reflectedPolarizedFlux z) (reflectedPolarizedFlux z) = 0 :=
    hiso _ hsuper
  exact him ((reflectedPolarizedFlux_green_zero_iff hre).mp hgreen)

/-- Pointwise superposition of the original *integer samples*. -/
def polarizedNativeIntegerSample (z : ℂ) : ℤ → ℂ :=
  fun n => nativeCarryLogWaveIntegerSample z n +
    Complex.I * nativeCarryLogWaveIntegerSample (conj z) n

/-- The finite Cp camera acts linearly on arbitrary sample fields.
This lemma retains the original seed, centres and legs. -/
theorem finiteCpChart_superposition (p M : ℕ)
    (f g : ℤ → ℂ) (c : ℂ) :
    CPFormal.Genuine.Cp.finiteChart p M
      (fun n => f n + c * g n) =
      CPFormal.Genuine.Cp.finiteChart p M f +
        c * CPFormal.Genuine.Cp.finiteChart p M g := by
  classical
  simp [CPFormal.Genuine.Cp.finiteChart, CPFormal.Genuine.Cp.seedSum,
    CPFormal.Genuine.Cp.bracket, CPFormal.Genuine.Cp.legSum,
    Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_sub]
  simp only [← Finset.mul_sum]
  ring

/-- The trace of the polarized native wave is the genuine linear
superposition at EACH finite cutoff, before passage to the limit. -/
theorem polarizedNativeIntegerSample_finiteChart (z : ℂ) (M : ℕ) :
    CPFormal.Genuine.Cp.finiteChart 3 M
      (polarizedNativeIntegerSample z) =
      CPFormal.Genuine.Cp.finiteChart 3 M
        (nativeCarryLogWaveIntegerSample z) +
      Complex.I * CPFormal.Genuine.Cp.finiteChart 3 M
        (nativeCarryLogWaveIntegerSample (conj z)) := by
  exact finiteCpChart_superposition 3 M
    (nativeCarryLogWaveIntegerSample z)
    (nativeCarryLogWaveIntegerSample (conj z)) Complex.I

/-- Both closing brackets imply closure of their combined scalar chart.
No isotropy claim is used in this result. -/
theorem polarizedNativeIntegerSample_bracket_closes
    {z : ℂ}
    (hz : NativeCarryLogWaveBoundaryCloses z)
    (hzc : NativeCarryLogWaveBoundaryCloses (conj z)) :
    Tendsto
      (fun M : ℕ =>
        CPFormal.Genuine.Cp.finiteChart 3 M (polarizedNativeIntegerSample z))
      atTop (nhds 0) := by
  have hmult :
      Tendsto
        (fun M : ℕ =>
          Complex.I * CPFormal.Genuine.Cp.finiteChart 3 M
            (nativeCarryLogWaveIntegerSample (conj z)))
        atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hzc)
  have hadd := hz.add hmult
  simpa only [NativeCarryLogWaveBoundaryCloses,
    polarizedNativeIntegerSample_finiteChart, add_zero] using hadd

/-- A genuine zero gives bracket closure of the superposed sample
with no new spectral assumption: use the existing reflected-zero theorem. -/
theorem polarizedNativeIntegerSample_closes_of_genuine_zero
    {z : ℂ} (hz : carryComplexTimeParameter z ∈ genuineCriticalStrip)
    (hzero : genuineContinuation (carryComplexTimeParameter z) = 0) :
    Tendsto
      (fun M : ℕ =>
        CPFormal.Genuine.Cp.finiteChart 3 M (polarizedNativeIntegerSample z))
      atTop (nhds 0) := by
  have hclose : NativeCarryLogWaveBoundaryCloses z :=
    (nativeCarryLogWaveBoundaryCloses_iff_resonance hz).2 (by
      simpa [IsNativeCarryComplexTimeResonance, carryComplexTimeGenuine] using hzero)
  have hreflect : carryComplexTimeParameter (conj z) ∈ genuineCriticalStrip := by
    rw [← reflectedParameter_carryComplexTimeParameter]
    exact reflectedParameter_mem_genuineCriticalStrip_zeta hz
  have hrefzero :=
    genuineContinuation_reflectedParameter_eq_zero_of_zero hz hzero
  rw [reflectedParameter_carryComplexTimeParameter] at hrefzero
  have hcloseReflected : NativeCarryLogWaveBoundaryCloses (conj z) :=
    (nativeCarryLogWaveBoundaryCloses_iff_resonance hreflect).2 (by
      simpa [IsNativeCarryComplexTimeResonance, carryComplexTimeGenuine] using hrefzero)
  exact polarizedNativeIntegerSample_bracket_closes hclose hcloseReflected

/-- At a Genuine zero the polarized SELF Green condition is EXACTLY the
still-open half-abscissa statement; bracket closure alone was proven above
and must not be silently promoted to self-adjoint domain membership. -/
theorem polarizedGreen_isotropy_iff_critical_at_genuine_zero
    {z : ℂ} (hz : carryComplexTimeParameter z ∈ genuineCriticalStrip)
    (hzero : genuineContinuation (carryComplexTimeParameter z) = 0) :
    nativeCarryReflectedLogBoundaryForm
        (reflectedPolarizedFlux z) (reflectedPolarizedFlux z) = 0
      ↔ (carryComplexTimeParameter z).re = (1 / 2 : ℝ) := by
  have hre : z.re ≠ 0 := by
    simpa only [carryComplexTimeParameter_im] using
      (genuineContinuation_zero_offReal_and_conjPaired hz hzero).1
  rw [reflectedPolarizedFlux_green_zero_iff hre,
    carryComplexTimeParameter_re]
  constructor <;> intro h <;> linarith

end

end CPFormal.Analytic.Cp

#print axioms CPFormal.Analytic.Cp.no_isotropic_submodule_containing_reflected_pair
#print axioms CPFormal.Analytic.Cp.polarizedNativeIntegerSample_closes_of_genuine_zero
#print axioms CPFormal.Analytic.Cp.polarizedGreen_isotropy_iff_critical_at_genuine_zero
#print axioms CPFormal.Analytic.Cp.reflectedPolarizedFlux_green_eq_mixed
#print axioms CPFormal.Analytic.Cp.reflectedPolarizedFlux_green_zero_iff
#print axioms CPFormal.Analytic.Cp.finiteCpChart_superposition
#print axioms CPFormal.Analytic.Cp.polarizedNativeIntegerSample_bracket_closes
