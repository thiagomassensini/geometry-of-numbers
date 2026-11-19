import CPFormal.Analytic.CpNativeCarryReflectedLogBoundarySymmetry
import CPFormal.Analytic.CpGenuinePrimeGreenBessel
import CPFormal.Analytic.CpGenuineReflectionRigidity
import CPFormal.Analytic.CpGenuineRiemannZetaIdentification

/-!
# Reflected boundary tests for the Genuine Green flux

The signed diagonal test on the characteristic endpoint is zero for every
complex time. A mixed test with the seed retains the missing transverse
coordinate. In the arithmetic cutoff, subtraction across cameras removes
the common bracket boundary but retains the radial factor.
-/

open scoped BigOperators ComplexConjugate Topology

namespace CPFormal.Analytic.Cp

open Filter

/-- Diagonal isotropy of a single reflected flux is independent of its
membership in the fixed diagonal boundary relation. -/
theorem nativeReflectedLogFlux_self_green_zero (z : ℂ) :
    nativeCarryReflectedLogBoundaryForm
        (nativeCarryReflectedLogBoundaryFlux z)
        (nativeCarryReflectedLogBoundaryFlux z) = 0 := by
  simp only [nativeCarryReflectedLogBoundaryFlux_eq, nativeCarryReflectedLogBoundaryForm,
    Complex.conj_conj]
  ring

/-- Testing the same flux against the actual normalized endpoint value
retains the difference of the two characteristic coordinates. -/
theorem nativeReflectedLogFlux_seed_green_eq (z : ℂ) :
    nativeCarryReflectedLogBoundaryForm
        (nativeCarryReflectedLogBoundaryValue z)
        (nativeCarryReflectedLogBoundaryFlux z) = z - conj z := by
  simp [nativeCarryReflectedLogBoundaryForm]

/-- The reflected wave supplies a second characteristic endpoint. The
mixed test against it retains the transverse displacement. -/
theorem nativeReflectedLogFlux_reflected_green_eq (z : ℂ) :
    nativeCarryReflectedLogBoundaryForm
        (nativeCarryReflectedLogBoundaryFlux (conj z))
        (nativeCarryReflectedLogBoundaryFlux z) = z ^ 2 - (conj z) ^ 2 := by
  simp only [nativeCarryReflectedLogBoundaryFlux_eq, nativeCarryReflectedLogBoundaryForm,
    Complex.conj_conj]
  ring

/-- At a nonzero imaginary part of the Genuine parameter, a single mixed
reflected-wave Green entry suffices to recover the diagonal condition. -/
theorem nativeReflectedLogFlux_reflected_green_zero_iff
    {z : ℂ} (hz : z.re ≠ 0) :
    nativeCarryReflectedLogBoundaryForm
        (nativeCarryReflectedLogBoundaryFlux (conj z))
        (nativeCarryReflectedLogBoundaryFlux z) = 0 ↔ z.im = 0 := by
  rw [nativeReflectedLogFlux_reflected_green_eq]
  constructor
  · intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, pow_two, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.zero_im] at him
    have hmul : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hz
  · intro him
    have hconj : conj z = z := by
      apply Complex.ext <;> simp [him]
    rw [hconj, sub_self]

/-- Both waves already satisfy the original arithmetic bracket boundary.
For their characteristic fluxes, one mixed Green entry detects matching. -/
theorem nativeReflectedWave_mixed_green_test_of_bracket_closure
    {z : ℂ} (hz : carryComplexTimeParameter z ∈ genuineCriticalStrip)
    (hbracket : NativeCarryLogWaveBoundaryCloses z) :
    NativeCarryLogWaveBoundaryCloses (conj z) ∧
      (nativeCarryReflectedLogBoundaryForm
          (nativeCarryReflectedLogBoundaryFlux (conj z))
          (nativeCarryReflectedLogBoundaryFlux z) = 0 ↔
        NativeCarryReflectedLogFluxMatches z) := by
  have hzero : genuineContinuation (carryComplexTimeParameter z) = 0 := by
    simpa [IsNativeCarryComplexTimeResonance, carryComplexTimeGenuine] using
      (nativeCarryLogWaveBoundaryCloses_iff_resonance hz).mp hbracket
  have hreflect : carryComplexTimeParameter (conj z) ∈ genuineCriticalStrip := by
    rw [← reflectedParameter_carryComplexTimeParameter]
    exact reflectedParameter_mem_genuineCriticalStrip_zeta hz
  have hrefzero := genuineContinuation_reflectedParameter_eq_zero_of_zero hz hzero
  rw [reflectedParameter_carryComplexTimeParameter] at hrefzero
  have hrefBracket : NativeCarryLogWaveBoundaryCloses (conj z) :=
    (nativeCarryLogWaveBoundaryCloses_iff_resonance hreflect).mpr (by
      simpa [IsNativeCarryComplexTimeResonance, carryComplexTimeGenuine] using hrefzero)
  have hre : z.re ≠ 0 := by
    simpa only [carryComplexTimeParameter_im] using
      (genuineContinuation_zero_offReal_and_conjPaired hz hzero).1
  exact ⟨hrefBracket, by
    rw [nativeReflectedLogFlux_reflected_green_zero_iff hre,
      nativeCarryReflectedLogFluxMatches_iff_im_eq_zero]⟩

/-- Reflection exchanges the two gradient slots of the arithmetic pairing. -/
theorem finiteReflectedGradientPairing_reflected_eq_conj (M : ℕ) (s : ℂ) :
    finiteReflectedGradientPairing M (reflectedParameter s) =
      conj (finiteReflectedGradientPairing M s) := by
  have hreflect : reflectedParameter (reflectedParameter s) = s := by
    apply Complex.ext
    · simp [reflectedParameter]
    · simp [reflectedParameter]
  unfold finiteReflectedGradientPairing
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [hreflect, map_mul]
  simp only [Complex.conj_conj]
  ring

/-- The real reflected energy is even in the signed displacement. Hence the
uncompressed bulk has opposite signs at reflected parameters. -/
theorem finiteCoupledGreenBulk_reflected_eq_neg (p M : ℕ) (hp : Nat.Prime p)
    (s : ℂ) :
    finiteBracketCoupledCpGreenFlux p M (reflectedParameter s) -
        finiteBracketCoupledSignedBoundary M (reflectedParameter s) =
      -(finiteBracketCoupledCpGreenFlux p M s - finiteBracketCoupledSignedBoundary M s) := by
  have hdelta : criticalDisplacement (reflectedParameter s).re =
      -criticalDisplacement s.re := by
    rw [reflectedParameter_re, criticalDisplacement, criticalDisplacement]
    ring
  rw [finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing p M hp,
    finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing p M hp,
    add_sub_cancel_right, add_sub_cancel_right, hdelta, cpRadialDifference_neg,
    finiteReflectedGradientPairing_reflected_eq_conj, Complex.conj_re]
  ring

/-- Camera subtraction eliminates the bracket boundary at every finite
cutoff, without a zero hypothesis. -/
theorem finiteCoupledGreenFlux_camera_sub_eq (p q M : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (s : ℂ) :
    finiteBracketCoupledCpGreenFlux q M s - finiteBracketCoupledCpGreenFlux p M s =
      (cpRadialDifference q (criticalDisplacement s.re) -
        cpRadialDifference p (criticalDisplacement s.re)) *
        (finiteReflectedGradientPairing M s).re := by
  rw [finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing q M hq s,
    finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing p M hp s]
  ring

/-- The camera difference converges in the open strip, with the same
coefficient and the infinite reflected energy. -/
theorem finiteCoupledGreenFlux_camera_sub_tendsto (p q : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto (fun M => finiteBracketCoupledCpGreenFlux q M s -
        finiteBracketCoupledCpGreenFlux p M s) atTop
      (nhds ((cpRadialDifference q (criticalDisplacement s.re) -
        cpRadialDifference p (criticalDisplacement s.re)) *
          infiniteReflectedGreenEnergy s)) := by
  simpa only [finiteCoupledGreenFlux_camera_sub_eq p q _ hp hq s] using
    tendsto_const_nhds.mul (finiteReflectedGradientPairing_re_tendsto_infiniteEnergy hs)

end CPFormal.Analytic.Cp

#print axioms CPFormal.Analytic.Cp.nativeReflectedLogFlux_self_green_zero
#print axioms CPFormal.Analytic.Cp.nativeReflectedLogFlux_seed_green_eq
#print axioms CPFormal.Analytic.Cp.nativeReflectedLogFlux_reflected_green_eq
#print axioms CPFormal.Analytic.Cp.nativeReflectedLogFlux_reflected_green_zero_iff
#print axioms CPFormal.Analytic.Cp.nativeReflectedWave_mixed_green_test_of_bracket_closure
#print axioms CPFormal.Analytic.Cp.finiteReflectedGradientPairing_reflected_eq_conj
#print axioms CPFormal.Analytic.Cp.finiteCoupledGreenBulk_reflected_eq_neg
#print axioms CPFormal.Analytic.Cp.finiteCoupledGreenFlux_camera_sub_eq
#print axioms CPFormal.Analytic.Cp.finiteCoupledGreenFlux_camera_sub_tendsto
