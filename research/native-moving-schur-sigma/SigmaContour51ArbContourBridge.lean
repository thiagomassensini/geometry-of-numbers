import SigmaContour51ArbResidualGate
import SigmaContour51ArbArcSumCertificate4096
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Exact path reduction for the radius-51 Arb residuals

The Arb script integrates the even C2 quotient along the lower semicircle, parameterized by
`u ↦ circleMap 0 51 (-π*u)`. This file formalizes the exact real-variable reduction from a full
circle integral to that path. It does not certify the interval enclosures of the resulting path
integral.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator Complex MeasureTheory
open Filter Topology
open scoped Interval

noncomputable section
set_option autoImplicit false

/-- A π-periodic angular integrand has the same integral on the upper and lower semicircles. -/
theorem periodic_pi_integral_upper_eq_lower (q : ℝ → ℂ)
    (hq : Function.Periodic q Real.pi) :
    (∫ θ in (0 : ℝ)..Real.pi, q θ) =
      ∫ θ in (-Real.pi)..0, q θ := by
  simpa using hq.intervalIntegral_add_eq 0 (-Real.pi)

/-- The full angular integral of a π-periodic function equals twice its lower semicircle
integral, with the lower path oriented by `θ = -πu`. Integrability is stated explicitly so this
lemma can also be used independently of the analyticity proof for the source quotient. -/
theorem periodic_pi_integral_full_eq_lower_parameter (q : ℝ → ℂ)
    (hq : Function.Periodic q Real.pi)
    (hint : ∀ a b : ℝ, IntervalIntegrable q volume a b) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) =
      (2 * Real.pi : ℂ) * (∫ u in (0 : ℝ)..1, q (-Real.pi * u)) := by
  have hfull := hq.intervalIntegral_add_zsmul_eq (2 : ℤ) 0 hint
  have hpi := periodic_pi_integral_upper_eq_lower q hq
  have hparam := intervalIntegral.integral_comp_mul_right (f := q) (a := 0) (b := 1)
    (c := -Real.pi)
    (by exact neg_ne_zero.mpr Real.pi_ne_zero)
  have hparam' : (∫ u in (0 : ℝ)..1, q (-Real.pi * u)) =
      (-(Real.pi : ℝ))⁻¹ • (∫ θ in (0 : ℝ)..(-Real.pi), q θ) := by
    simpa [mul_comm] using hparam
  have hfull' : (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) =
      (2 : ℂ) * (∫ θ in (0 : ℝ)..Real.pi, q θ) := by
    simpa [smul_eq_mul] using hfull
  rw [hpi] at hfull'
  have hparam'' : (∫ u in (0 : ℝ)..1, q (-Real.pi * u)) =
      (Real.pi : ℂ)⁻¹ * (∫ θ in (-Real.pi)..0, q θ) := by
    calc
      (∫ u in (0 : ℝ)..1, q (-Real.pi * u)) =
          (-(Real.pi : ℝ))⁻¹ • (∫ θ in (0 : ℝ)..(-Real.pi), q θ) := hparam'
      _ = (Real.pi : ℂ)⁻¹ * (∫ θ in (-Real.pi)..0, q θ) := by
        rw [intervalIntegral.integral_symm]
        rw [Complex.real_smul]
        have hpi_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
        push_cast
        field_simp [hpi_ne]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) =
        (2 : ℂ) * (∫ θ in (-Real.pi)..0, q θ) := hfull'
    _ = (2 * Real.pi : ℂ) *
        ((Real.pi : ℂ)⁻¹ * (∫ θ in (-Real.pi)..0, q θ)) := by
      field_simp [hpi_ne]
    _ = _ := by rw [← hparam'']

/-- The original completed characteristic is even, so its logarithmic derivative is odd. -/
def contour51OriginalResponse (z : ℂ) : ℂ :=
  -deriv completedNativeCharacteristicContinuation z /
    ((2 : ℂ) * completedNativeCharacteristicContinuation z)

/-- The logarithmic derivative of the same completed-zeta parameter function used by the exact
Lean continuation identity. -/
def contour51SigmaXiLogDerivative (s : ℂ) : ℂ :=
  deriv sigmaCompletedXiParameter s / sigmaCompletedXiParameter s

theorem contour51OriginalResponse_eq_sigmaXiLogDerivative {z : ℂ}
    (hF : completedNativeCharacteristicContinuation z ≠ 0) :
    contour51OriginalResponse z =
      (-(Complex.I / 2 : ℂ)) *
        contour51SigmaXiLogDerivative (operatorHeightParameter z) := by
  let s := operatorHeightParameter z
  have hFvalue : completedNativeCharacteristicContinuation z =
      sigmaCompletedXiParameter s :=
    completedNativeCharacteristicContinuation_eq_sigmaCompletedXiParameter z
  have hXi : sigmaCompletedXiParameter s ≠ 0 := by
    rw [← hFvalue]
    exact hF
  have hXiDiff : DifferentiableAt ℂ sigmaCompletedXiParameter s := by
    change DifferentiableAt ℂ (fun x : ℂ =>
      (1 / 2 : ℂ) + (1 / 2 : ℂ) * x * (x - 1) * completedRiemannZeta₀ x) s
    exact (differentiableAt_const (1 / 2 : ℂ)).add
      ((((differentiableAt_const (1 / 2 : ℂ)).mul differentiableAt_id).mul
        (differentiableAt_id.sub (differentiableAt_const (1 : ℂ)))).mul
        differentiable_completedZeta₀.differentiableAt)
  have hparamAnalytic : AnalyticAt ℂ operatorHeightParameter z :=
    operatorHeightParameter_analyticAt z
  have hcomp : completedNativeCharacteristicContinuation =
      sigmaCompletedXiParameter ∘ operatorHeightParameter := by
    funext w
    exact completedNativeCharacteristicContinuation_eq_sigmaCompletedXiParameter w
  have hderivComp := congrArg (fun f : ℂ → ℂ => deriv f z) hcomp
  have hderivComp' : deriv completedNativeCharacteristicContinuation z =
      deriv sigmaCompletedXiParameter (operatorHeightParameter z) *
        deriv operatorHeightParameter z := by
    calc
      deriv completedNativeCharacteristicContinuation z =
          deriv (sigmaCompletedXiParameter ∘ operatorHeightParameter) z := hderivComp
      _ = _ := by
        simpa only [Function.comp_def] using
          deriv_comp_of_eq (x := z) (y := operatorHeightParameter z)
            hXiDiff hparamAnalytic.differentiableAt rfl
  have hparamDeriv : deriv operatorHeightParameter z = Complex.I := by
    change deriv (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) z = Complex.I
    simp
  have hFderiv : deriv completedNativeCharacteristicContinuation z =
      Complex.I * deriv sigmaCompletedXiParameter s := by
    calc
      deriv completedNativeCharacteristicContinuation z =
          deriv sigmaCompletedXiParameter (operatorHeightParameter z) *
            deriv operatorHeightParameter z := hderivComp'
      _ = Complex.I * deriv sigmaCompletedXiParameter s := by
        rw [hparamDeriv]
        dsimp [s]
        ring
  dsimp [contour51OriginalResponse, contour51SigmaXiLogDerivative]
  rw [hFvalue, hFderiv]
  have hs : operatorHeightParameter z = s := rfl
  rw [hs]
  field_simp [hXi]

/-- On the zero-free right half-plane region used by the Arb arcs, the completed-xi logarithmic
derivative splits into the elementary, completed-Gamma, and zeta factors. The remaining Gamma
factor can be expanded using Mathlib's `Complex.digamma`. -/
theorem contour51SigmaXiLogDerivative_eq_zeta_gamma_factors {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    contour51SigmaXiLogDerivative s =
      1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s +
        logDeriv riemannZeta s := by
  let prefactor : ℂ → ℂ := fun w =>
    (1 / 2 : ℂ) * w * (w - 1) * Complex.Gammaℝ w
  have hs0 : s ≠ 0 := by
    intro h
    have hr : s.re = 0 := by simpa using congrArg Complex.re h
    linarith
  have hsSubOne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hGammaNonzero : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hGammaDiff : DifferentiableAt ℂ Complex.Gammaℝ s := by
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hexponent : DifferentiableAt ℂ (fun w : ℂ => -w / 2) s := by fun_prop
    have hpiPow : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s :=
      hexponent.const_cpow (Or.inl hpi)
    have hhalf : DifferentiableAt ℂ (fun w : ℂ => w / 2) s := by fun_prop
    have hGammaAt : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
      Complex.differentiableAt_Gamma (s / 2) (by
        intro n hneg
        have hre : (s / 2).re = -(n : ℝ) := by
          simpa using congrArg Complex.re hneg
        rw [Complex.div_re] at hre
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        norm_num at hre
        linarith)
    have hGammaComp : DifferentiableAt ℂ
        (fun w : ℂ => Complex.Gamma (w / 2)) s := hGammaAt.comp s hhalf
    change DifferentiableAt ℂ
      (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) s
    exact hpiPow.mul hGammaComp
  have hprefactorNonzero : prefactor s ≠ 0 := by
    dsimp [prefactor]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hsSubOne)
      hGammaNonzero
  have hprefactorDiff : DifferentiableAt ℂ prefactor s := by
    dsimp [prefactor]
    exact (((differentiableAt_const (1 / 2 : ℂ)).mul differentiableAt_id).mul
      (differentiableAt_id.sub_const 1)).mul hGammaDiff
  have hzetaDiff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hproductNear :
      (fun w : ℂ => sigmaCompletedXiParameter w) =ᶠ[𝓝 s]
        (fun w : ℂ => prefactor w * riemannZeta w) := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_Ioi.preimage continuous_re
    filter_upwards [hopen.eventually_mem hs, eventually_ne_nhds hs1] with w hw hw1
    simpa [prefactor] using sigmaCompletedXiParameter_eq_completedFactor_mul_zeta hw hw1
  have hproductValue : sigmaCompletedXiParameter s = prefactor s * riemannZeta s :=
    sigmaCompletedXiParameter_eq_completedFactor_mul_zeta hs hs1
  have hproductLogDeriv :
      logDeriv (fun w : ℂ => prefactor w * riemannZeta w) s =
        logDeriv prefactor s + logDeriv riemannZeta s :=
    logDeriv_mul s hprefactorNonzero hzeta hprefactorDiff hzetaDiff
  have hlinearDiff : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) * w) s :=
    differentiableAt_id.const_mul (1 / 2 : ℂ)
  have hshiftDiff : DifferentiableAt ℂ (fun w : ℂ => w - 1) s :=
    differentiableAt_id.sub_const 1
  have hlinearNonzero : (1 / 2 : ℂ) * s ≠ 0 :=
    mul_ne_zero (by norm_num) hs0
  have hshiftNonzero : s - 1 ≠ 0 := hsSubOne
  have hlinearLogDeriv :
      logDeriv (fun w : ℂ => (1 / 2 : ℂ) * w) s = 1 / s := by
    rw [logDeriv_apply, deriv_const_mul_id]
    field_simp [hs0]
  have hshiftLogDeriv : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  have hpolynomialLogDeriv :
      logDeriv (fun w : ℂ => ((1 / 2 : ℂ) * w) * (w - 1)) s =
        1 / s + 1 / (s - 1) := by
    calc
      logDeriv (fun w : ℂ => ((1 / 2 : ℂ) * w) * (w - 1)) s =
          logDeriv (fun w : ℂ => (1 / 2 : ℂ) * w) s +
            logDeriv (fun w : ℂ => w - 1) s :=
        logDeriv_mul s hlinearNonzero hshiftNonzero hlinearDiff hshiftDiff
      _ = 1 / s + 1 / (s - 1) := by rw [hlinearLogDeriv, hshiftLogDeriv]
  have hpolynomialNonzero :
      (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := mul_ne_zero hlinearNonzero hshiftNonzero
  have hpolynomialDiff : DifferentiableAt ℂ
      (fun w : ℂ => ((1 / 2 : ℂ) * w) * (w - 1)) s := hlinearDiff.mul hshiftDiff
  have hprefactorLogDeriv : logDeriv prefactor s =
      1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s := by
    change logDeriv
      (fun w : ℂ => ((1 / 2 : ℂ) * w * (w - 1)) * Complex.Gammaℝ w) s = _
    calc
      logDeriv
          (fun w : ℂ => ((1 / 2 : ℂ) * w * (w - 1)) * Complex.Gammaℝ w) s =
          logDeriv (fun w : ℂ => (1 / 2 : ℂ) * w * (w - 1)) s +
            logDeriv Complex.Gammaℝ s :=
        logDeriv_mul s hpolynomialNonzero hGammaNonzero hpolynomialDiff hGammaDiff
      _ = 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s := by
        rw [hpolynomialLogDeriv]
  unfold contour51SigmaXiLogDerivative
  rw [hproductNear.deriv_eq, hproductValue]
  have hcombine := hproductLogDeriv
  rw [hprefactorLogDeriv] at hcombine
  simpa [logDeriv_apply, add_assoc, add_left_comm, add_comm] using hcombine

/-- The real Gamma completion contributes the usual `-log(pi)/2 + digamma(s/2)/2`
term to the completed-xi logarithmic derivative. -/
theorem contour51GammaReal_logDeriv_eq_digamma {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hexponent : DifferentiableAt ℂ (fun w : ℂ => -w / 2) s := by fun_prop
  have hhalf : DifferentiableAt ℂ (fun w : ℂ => w / 2) s := by fun_prop
  have hpiPowDiff : DifferentiableAt ℂ
      (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s :=
    hexponent.const_cpow (Or.inl hpi)
  have hpiPowNonzero : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hGammaAt : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma (s / 2) (by
      intro n hneg
      have hre : (s / 2).re = -(n : ℝ) := by
        simpa using congrArg Complex.re hneg
      rw [Complex.div_re] at hre
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      norm_num at hre
      linarith)
  have hGammaComp : DifferentiableAt ℂ
      (fun w : ℂ => Complex.Gamma (w / 2)) s := hGammaAt.comp s hhalf
  have hGammaNonzero : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      rw [Complex.div_re]
      norm_num
      linarith)
  have hexponentDeriv : deriv (fun w : ℂ => -w / 2) s = -(1 / 2 : ℂ) := by
    simp [deriv_div_const, one_div]
    norm_num [one_div]
  have hpiPowLogDeriv :
      logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s =
        -(Complex.log (Real.pi : ℂ)) / 2 := by
    rw [logDeriv_apply, Complex.deriv_const_cpow hexponent (Real.pi : ℂ), hexponentDeriv]
    field_simp [hpiPowNonzero]
  have hGammaCompLogDeriv :
      logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) s =
        Complex.digamma (s / 2) / 2 := by
    calc
      logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) s =
          logDeriv Complex.Gamma (s / 2) * deriv (fun w : ℂ => w / 2) s := by
        simpa only [Function.comp_def] using
          logDeriv_comp (f := Complex.Gamma) (g := fun w : ℂ => w / 2) (x := s)
            hGammaAt hhalf
      _ = Complex.digamma (s / 2) / 2 := by
        rw [Complex.digamma_def]
        simp [deriv_div_const]
        ring
  change logDeriv
    (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) s = _
  calc
    logDeriv
        (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) s =
        logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s +
          logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) s := by
      exact logDeriv_mul s hpiPowNonzero hGammaNonzero hpiPowDiff hGammaComp
    _ = -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2) / 2 := by
      rw [hpiPowLogDeriv, hGammaCompLogDeriv]

/-- This is the exact logarithmic-derivative formula evaluated by the Arb arc scripts, now
expressed for Lean's original completed characteristic with the explicit nonvanishing premises. -/
theorem contour51SigmaXiLogDerivative_eq_arb_formula {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    contour51SigmaXiLogDerivative s =
      1 / s + 1 / (s - 1) - (Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma (s / 2) / 2 + deriv riemannZeta s / riemannZeta s := by
  rw [contour51SigmaXiLogDerivative_eq_zeta_gamma_factors hs hs1 hzeta,
    contour51GammaReal_logDeriv_eq_digamma hs, logDeriv_apply]
  ring

/-- The original response itself equals the explicit zeta/Gamma/digamma expression evaluated by
the Arb scripts throughout the zero-free right-half-plane region. The zeta nonvanishing condition
is derived from the original source's nonvanishing and the exact completed-zeta factorization. -/
theorem contour51OriginalResponse_eq_arb_formula {z : ℂ}
    (hF : completedNativeCharacteristicContinuation z ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re)
    (hs1 : operatorHeightParameter z ≠ 1) :
    contour51OriginalResponse z =
      (-(Complex.I / 2 : ℂ)) *
        (1 / operatorHeightParameter z +
          1 / (operatorHeightParameter z - 1) -
          (Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (operatorHeightParameter z / 2) / 2 +
          deriv riemannZeta (operatorHeightParameter z) /
            riemannZeta (operatorHeightParameter z)) := by
  have hXi : sigmaCompletedXiParameter (operatorHeightParameter z) ≠ 0 := by
    rw [← completedNativeCharacteristicContinuation_eq_sigmaCompletedXiParameter z]
    exact hF
  have hzeta : riemannZeta (operatorHeightParameter z) ≠ 0 := by
    intro hz
    have hfactor := sigmaCompletedXiParameter_eq_completedFactor_mul_zeta hs hs1
    exact hXi (by simpa [hz] using hfactor)
  rw [contour51OriginalResponse_eq_sigmaXiLogDerivative hF,
    contour51SigmaXiLogDerivative_eq_arb_formula hs hs1 hzeta]

/-- The original response on the complete lower semicircle is already in the exact explicit
zeta/Gamma/digamma form evaluated by Arb. The circle's zero-free boundary comes from C1; the
right-half-plane and pole-avoidance conditions follow from the lower-path geometry and radius 51. -/
theorem contour51OriginalResponse_eq_arb_formula_lower_path {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    contour51OriginalResponse (circleMap 0 51 (-Real.pi * u)) =
      (-(Complex.I / 2 : ℂ)) *
        (1 / operatorHeightParameter (circleMap 0 51 (-Real.pi * u)) +
          1 / (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)) - 1) -
          (Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)) / 2) / 2 +
          deriv riemannZeta (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))) /
            riemannZeta (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)))) := by
  let z : ℂ := circleMap 0 51 (-Real.pi * u)
  have huAngle0 : -Real.pi * u ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) hu.1
  have huAngleLower : -Real.pi ≤ -Real.pi * u := by
    have := mul_le_mul_of_nonpos_left hu.2 (neg_nonpos.mpr Real.pi_pos.le)
    simpa using this
  have him : z.im = 51 * Real.sin (-Real.pi * u) := by
    simp only [z, circleMap_zero_im]
  have hsin : Real.sin (-Real.pi * u) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le huAngle0 huAngleLower
  have hs : 0 < (operatorHeightParameter z).re := by
    rw [operatorHeightParameter_re, him]
    nlinarith
  have hs1 : operatorHeightParameter z ≠ 1 := by
    intro h
    have hnorm : ‖z‖ = 51 := by simp [z, norm_circleMap_zero]
    have hparamNorm : ‖operatorHeightParameter z - (1 / 2 : ℂ)‖ = ‖z‖ := by
      simp [CarrySelfAdjointOperator.operatorHeightParameter]
    rw [h] at hparamNorm
    rw [hnorm] at hparamNorm
    norm_num at hparamNorm
  have hF : completedNativeCharacteristicContinuation z ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, hboundary, _⟩ :=
      sigmaContour51_original_characteristic_roots
    apply hboundary z
    simp [z, norm_circleMap_zero]
  simpa [z] using contour51OriginalResponse_eq_arb_formula hF hs hs1

theorem contour51OriginalResponse_odd (z : ℂ) :
    contour51OriginalResponse (-z) = -contour51OriginalResponse z := by
  have hevenFun : (fun w : ℂ => completedNativeCharacteristicContinuation (-w)) =
      completedNativeCharacteristicContinuation :=
    funext completedNativeCharacteristicContinuation_even
  have hderivComp := congrArg (fun f : ℂ → ℂ => deriv f z) hevenFun
  rw [deriv_comp_neg] at hderivComp
  have hderivNeg : deriv completedNativeCharacteristicContinuation (-z) =
      -deriv completedNativeCharacteristicContinuation z := by
    simpa using congrArg (fun w : ℂ => -w) hderivComp
  simp only [contour51OriginalResponse, completedNativeCharacteristicContinuation_even,
    hderivNeg]
  ring

/-- The quotient used for `e_n` is even. Its angular restriction is consequently π-periodic. -/
def contour51OriginalResidualQuotient (n : ℕ) (z : ℂ) : ℂ :=
  contour51OriginalResponse z / z ^ (2 * n + 1)

theorem contour51OriginalResidualQuotient_neg (n : ℕ) (z : ℂ) :
    contour51OriginalResidualQuotient n (-z) =
      contour51OriginalResidualQuotient n z := by
  have hpowEven : (-z) ^ (2 * n) = z ^ (2 * n) := by
    calc
      (-z) ^ (2 * n) = ((-z) ^ 2) ^ n := by rw [pow_mul]
      _ = (z ^ 2) ^ n := by simp
      _ = z ^ (2 * n) := by rw [pow_mul]
  have hpowOdd : (-z) ^ (2 * n + 1) = -(z ^ (2 * n + 1)) := by
    calc
      (-z) ^ (2 * n + 1) = (-z) ^ (2 * n) * (-z) := by rw [pow_add]; simp
      _ = z ^ (2 * n) * (-z) := by rw [hpowEven]
      _ = -(z ^ (2 * n + 1)) := by rw [pow_succ]; ring
  simp only [contour51OriginalResidualQuotient, contour51OriginalResponse_odd,
    hpowOdd]
  simp [div_eq_mul_inv]

def contour51OriginalAngularResidualIntegrand (n : ℕ) (θ : ℝ) : ℂ :=
  contour51OriginalResidualQuotient n (circleMap 0 51 θ)

theorem contour51OriginalAngularResidualIntegrand_periodic (n : ℕ) :
    Function.Periodic (contour51OriginalAngularResidualIntegrand n) Real.pi := by
  intro θ
  have hneg : circleMap 0 51 (θ + Real.pi) = -circleMap 0 51 θ := by
    simp [circleMap, add_mul, Complex.exp_add]
  rw [contour51OriginalAngularResidualIntegrand, hneg,
    contour51OriginalResidualQuotient_neg]
  rfl

/-- Continuity of the original residual integrand as a function of the angular parameter. -/
theorem continuous_contour51OriginalAngularResidualIntegrand (n : ℕ) :
    Continuous (contour51OriginalAngularResidualIntegrand n) := by
  have hFcircle : ∀ θ : ℝ,
      completedNativeCharacteristicContinuation (circleMap 0 51 θ) ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, hboundary, _⟩ :=
      sigmaContour51_original_characteristic_roots
    intro θ
    apply hboundary
    simp
  have hFcont : Continuous completedNativeCharacteristicContinuation :=
    continuous_iff_continuousAt.mpr fun z =>
      (completedNativeCharacteristicContinuation_analyticAt z).continuousAt
  have hDcont : Continuous (deriv completedNativeCharacteristicContinuation) :=
    continuous_iff_continuousAt.mpr fun z =>
      (completedNativeCharacteristicContinuation_analyticAt z).deriv.continuousAt
  have hCircleCont : Continuous (circleMap 0 51) := continuous_circleMap _ _
  have hFangle : Continuous
      (fun θ : ℝ => completedNativeCharacteristicContinuation (circleMap 0 51 θ)) :=
    hFcont.comp hCircleCont
  have hDangle : Continuous
      (fun θ : ℝ => deriv completedNativeCharacteristicContinuation (circleMap 0 51 θ)) :=
    hDcont.comp hCircleCont
  have hResponseAngle : Continuous
      (fun θ : ℝ => contour51OriginalResponse (circleMap 0 51 θ)) := by
    change Continuous (fun θ : ℝ =>
      -deriv completedNativeCharacteristicContinuation (circleMap 0 51 θ) /
        ((2 : ℂ) * completedNativeCharacteristicContinuation (circleMap 0 51 θ)))
    apply hDangle.neg.div (continuous_const.mul hFangle)
    intro θ
    exact mul_ne_zero (by norm_num) (hFcircle θ)
  have hCircleNe : ∀ θ : ℝ, circleMap 0 51 θ ≠ 0 := by
    intro θ hz
    have hnorm : ‖circleMap 0 51 θ‖ = 51 := by simp
    rw [hz] at hnorm
    norm_num at hnorm
  have hCircleCont : Continuous (circleMap 0 51) := continuous_circleMap _ _
  change Continuous (fun θ : ℝ =>
    contour51OriginalResponse (circleMap 0 51 θ) /
      (circleMap 0 51 θ) ^ (2 * n + 1))
  apply hResponseAngle.div (hCircleCont.pow _)
  intro θ
  exact pow_ne_zero _ (hCircleNe θ)

/-- Exact Lean path identity used to compare the original source residual with the 4096-arc Arb
sum. C1's exact zero-free boundary theorem gives continuity and integrability of the quotient on
the circle; no integrability premise is left in this identity. The numerical enclosure of this
path integral remains a separate certificate-to-Lean obligation. -/
theorem contour51OriginalResidualIntegral_eq_lower_path (n : ℕ) :
    contour51OriginalResidualIntegral n =
      ∫ u in (0 : ℝ)..1, contour51OriginalAngularResidualIntegrand n (-Real.pi * u) := by
  let q : ℝ → ℂ := contour51OriginalAngularResidualIntegrand n
  have hperiodic : Function.Periodic q Real.pi :=
    contour51OriginalAngularResidualIntegrand_periodic n
  have hFcircle : ∀ θ : ℝ,
      completedNativeCharacteristicContinuation (circleMap 0 51 θ) ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, hboundary, _⟩ :=
      sigmaContour51_original_characteristic_roots
    intro θ
    apply hboundary
    simp
  have hFcont : Continuous completedNativeCharacteristicContinuation :=
    continuous_iff_continuousAt.mpr fun z =>
      (completedNativeCharacteristicContinuation_analyticAt z).continuousAt
  have hDcont : Continuous (deriv completedNativeCharacteristicContinuation) :=
    continuous_iff_continuousAt.mpr fun z =>
      (completedNativeCharacteristicContinuation_analyticAt z).deriv.continuousAt
  have hCircleCont : Continuous (circleMap 0 51) := continuous_circleMap _ _
  have hFangle : Continuous
      (fun θ : ℝ => completedNativeCharacteristicContinuation (circleMap 0 51 θ)) :=
    hFcont.comp hCircleCont
  have hDangle : Continuous
      (fun θ : ℝ => deriv completedNativeCharacteristicContinuation (circleMap 0 51 θ)) :=
    hDcont.comp hCircleCont
  have hResponseAngle : Continuous
      (fun θ : ℝ => contour51OriginalResponse (circleMap 0 51 θ)) := by
    change Continuous (fun θ : ℝ =>
      -deriv completedNativeCharacteristicContinuation (circleMap 0 51 θ) /
        ((2 : ℂ) * completedNativeCharacteristicContinuation (circleMap 0 51 θ)))
    apply hDangle.neg.div (continuous_const.mul hFangle)
    intro θ
    exact mul_ne_zero (by norm_num) (hFcircle θ)
  have hQuotientAngle : Continuous
      (contour51OriginalAngularResidualIntegrand n) := by
    change Continuous (fun θ : ℝ =>
      contour51OriginalResponse (circleMap 0 51 θ) /
        (circleMap 0 51 θ) ^ (2 * n + 1))
    apply hResponseAngle.div (hCircleCont.pow _)
    intro θ
    apply pow_ne_zero
    intro hz
    have hnorm : ‖circleMap 0 51 θ‖ = 51 := by simp
    rw [hz] at hnorm
    norm_num at hnorm
  have hQInt : IntervalIntegrable q volume 0 Real.pi := by
    exact hQuotientAngle.intervalIntegrable 0 Real.pi
  have hint : ∀ a b : ℝ, IntervalIntegrable q volume a b :=
    hperiodic.intervalIntegrable₀ Real.pi_ne_zero hQInt
  have hfull := periodic_pi_integral_full_eq_lower_parameter q hperiodic hint
  have hpoint : ∀ θ : ℝ,
      deriv (circleMap 0 51) θ •
          (contour51OriginalResponse (circleMap 0 51 θ) /
            (circleMap 0 51 θ) ^ (2 * n + 2)) =
        Complex.I * contour51OriginalAngularResidualIntegrand n θ := by
    intro θ
    let z := circleMap 0 51 θ
    have hz : z ≠ 0 := by
      intro hz0
      have hzNorm : ‖z‖ = 51 := by simp [z]
      rw [hz0] at hzNorm
      norm_num at hzNorm
    have hexp : 2 * n + 2 = (2 * n + 1) + 1 := by omega
    rw [deriv_circleMap]
    dsimp [z, contour51OriginalAngularResidualIntegrand,
      contour51OriginalResidualQuotient]
    rw [hexp, pow_succ]
    field_simp [hz]
  have hcircle :
      (∮ z in C(0, 51), contour51OriginalResponse z / z ^ (2 * n + 2)) =
        Complex.I * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) := by
    rw [circleIntegral]
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (circleMap 0 51) θ •
            (contour51OriginalResponse (circleMap 0 51 θ) /
              (circleMap 0 51 θ) ^ (2 * n + 2))) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.I * q θ := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        simpa [q] using hpoint θ
      _ = Complex.I * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) := by
        rw [intervalIntegral.integral_const_mul]
  have hnormalized : contour51OriginalResidualIntegral n =
      (2 * Real.pi : ℂ)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) := by
    change (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ z in C(0, 51), contour51OriginalResponse z / z ^ (2 * n + 2)) = _
    rw [hcircle]
    simp only [smul_eq_mul]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    field_simp [hpi, hI]
  rw [hnormalized, hfull]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  rfl

/-- The exact complex-valued path integral enclosed by the external 4096-arc Arb computation. -/
def contour51ArbLowerPathResidualIntegral (n : ℕ) : ℂ :=
  ∫ u in (0 : ℝ)..1,
    contour51OriginalAngularResidualIntegrand n (-Real.pi * u)

/-- Certificate-to-Lean inclusion proposition in the actual path parameterization used by Arb.
It is still an explicit proposition: no interval arithmetic evidence has been imported as a Lean
proof by this definition. -/
def contour51ArbLowerPathResidualIntervalBounds : Prop :=
  ∀ n : ℕ, n ≤ 5 →
    (contour51ArbRecordedResidualLower n : ℝ) ≤
        (contour51ArbLowerPathResidualIntegral n).re ∧
      (contour51ArbLowerPathResidualIntegral n).re ≤
        (contour51ArbRecordedResidualUpper n : ℝ)

/-- The first determinant only consumes the first three lower-path interval enclosures. -/
def contour51ArbFirstThreeLowerPathResidualIntervalBounds : Prop :=
  ∀ n : ℕ, n ≤ 2 →
    (contour51ArbRecordedResidualLower n : ℝ) ≤
        (contour51ArbLowerPathResidualIntegral n).re ∧
      (contour51ArbLowerPathResidualIntegral n).re ≤
        (contour51ArbRecordedResidualUpper n : ℝ)

/-- On an equal rational partition, pointwise bounds on each closed arc integrate to the
corresponding width-weighted endpoint sums. This isolates the exact integration step from the
separate proof that the Arb evaluator boxes enclose the Lean integrand on each arc. -/
theorem contour51_intervalIntegral_bounds_of_uniform_partition {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) (hf : Continuous f) (lower upper : ℕ → ℝ)
    (hlo : ∀ k < N, ∀ x ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N),
      lower k ≤ f x)
    (hhi : ∀ k < N, ∀ x ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N),
      f x ≤ upper k) :
    (1 / (N : ℝ)) * (∑ k ∈ Finset.range N, lower k) ≤
        (∫ x in (0 : ℝ)..1, f x) ∧
      (∫ x in (0 : ℝ)..1, f x) ≤
        (1 / (N : ℝ)) * (∑ k ∈ Finset.range N, upper k) := by
  let a : ℕ → ℝ := fun k => (k : ℝ) / (N : ℝ)
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNNe : (N : ℝ) ≠ 0 := hNReal.ne'
  have hpartition (g : ℝ → ℝ) (hg : Continuous g) :
      ∑ k ∈ Finset.range N, ∫ x in a k..a (k + 1), g x =
        ∫ x in (0 : ℝ)..1, g x := by
    simpa [a, hNNe] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := g) (μ := volume) (a := a) (n := N)
        (fun k _ => hg.intervalIntegrable _ _))
  have hpartition_f := hpartition f hf
  have hlo_piece : ∀ k < N,
      (1 / (N : ℝ)) * lower k ≤ ∫ x in a k..a (k + 1), f x := by
    intro k hk
    have hab : a k ≤ a (k + 1) := by
      dsimp [a]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast Nat.le_succ k
      · exact le_of_lt hNReal
    have hconst : IntervalIntegrable (fun _ : ℝ => lower k) volume (a k) (a (k + 1)) :=
      intervalIntegrable_const
    have hfun : IntervalIntegrable f volume (a k) (a (k + 1)) :=
      hf.intervalIntegrable _ _
    have hmono : (∫ x in a k..a (k + 1), lower k) ≤
        ∫ x in a k..a (k + 1), f x :=
      intervalIntegral.integral_mono_on hab hconst hfun (by
        intro x hx
        apply hlo k hk x
        simpa [a] using hx)
    have hconstValue : (∫ x in a k..a (k + 1), lower k) =
        (1 / (N : ℝ)) * lower k := by
      rw [intervalIntegral.integral_const]
      dsimp [a]
      push_cast
      field_simp [hNNe]
      ring
    rw [hconstValue] at hmono
    exact hmono
  have hhi_piece : ∀ k < N,
      ∫ x in a k..a (k + 1), f x ≤ (1 / (N : ℝ)) * upper k := by
    intro k hk
    have hab : a k ≤ a (k + 1) := by
      dsimp [a]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast Nat.le_succ k
      · exact le_of_lt hNReal
    have hconst : IntervalIntegrable (fun _ : ℝ => upper k) volume (a k) (a (k + 1)) :=
      intervalIntegrable_const
    have hfun : IntervalIntegrable f volume (a k) (a (k + 1)) :=
      hf.intervalIntegrable _ _
    have hmono : (∫ x in a k..a (k + 1), f x) ≤
        ∫ x in a k..a (k + 1), upper k :=
      intervalIntegral.integral_mono_on hab hfun hconst (by
        intro x hx
        apply hhi k hk x
        simpa [a] using hx)
    have hconstValue : (∫ x in a k..a (k + 1), upper k) =
        (1 / (N : ℝ)) * upper k := by
      rw [intervalIntegral.integral_const]
      dsimp [a]
      push_cast
      field_simp [hNNe]
      ring
    rw [hconstValue] at hmono
    exact hmono
  constructor
  · calc
      (1 / (N : ℝ)) * (∑ k ∈ Finset.range N, lower k) =
          ∑ k ∈ Finset.range N, ((1 / (N : ℝ)) * lower k) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range N, ∫ x in a k..a (k + 1), f x := by
        apply Finset.sum_le_sum
        intro k hk
        exact hlo_piece k (Finset.mem_range.mp hk)
      _ = ∫ x in (0 : ℝ)..1, f x := hpartition_f
  · calc
      (∫ x in (0 : ℝ)..1, f x) =
          ∑ k ∈ Finset.range N, ∫ x in a k..a (k + 1), f x := hpartition_f.symm
      _ ≤ ∑ k ∈ Finset.range N, ((1 / (N : ℝ)) * upper k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hhi_piece k (Finset.mem_range.mp hk)
      _ = (1 / (N : ℝ)) * (∑ k ∈ Finset.range N, upper k) := by
        rw [Finset.mul_sum]

/-- Complex-valued contour-path integrands can use the same partition bounds by taking their real
parts. This matches the residual gates, which consume real parts of the normalized integrals. -/
theorem contour51_complex_intervalIntegral_real_bounds_of_uniform_partition
    {N : ℕ} (hN : 0 < N) (f : ℝ → ℂ) (hf : Continuous f)
    (lower upper : ℕ → ℝ)
    (hlo : ∀ k < N, ∀ x ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N),
      lower k ≤ (f x).re)
    (hhi : ∀ k < N, ∀ x ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N),
      (f x).re ≤ upper k) :
    (1 / (N : ℝ)) * (∑ k ∈ Finset.range N, lower k) ≤
        (∫ x in (0 : ℝ)..1, f x).re ∧
      (∫ x in (0 : ℝ)..1, f x).re ≤
        (1 / (N : ℝ)) * (∑ k ∈ Finset.range N, upper k) := by
  have hfRe : Continuous (fun x => (f x).re) := by fun_prop
  have hreal := contour51_intervalIntegral_bounds_of_uniform_partition hN
    (fun x => (f x).re) hfRe lower upper hlo hhi
  have hfint : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable 0 1
  have hRe : (∫ x in (0 : ℝ)..1, f x).re =
      ∫ x in (0 : ℝ)..1, (f x).re := by
    simpa using (intervalIntegral.intervalIntegral_re (f := f) (μ := volume)
      (a := 0) (b := 1) hfint).symm
  rw [hRe]
  exact hreal

/-- Reindexing lemma for the finite endpoint lists used by the Arb partition certificate. -/
theorem list_sum_eq_finset_range_getD {α : Type*} [AddCommMonoid α] [Inhabited α]
    (values : List α) :
    values.sum = ∑ k ∈ Finset.range values.length, values.getD k default := by
  induction values with
  | nil => simp
  | cons a values ih =>
      simp [List.sum_cons, List.length_cons, Finset.sum_range_succ', List.getD, ih, add_comm]

private theorem list_rat_getD_default_eq_zero (values : List ℚ) (k : ℕ)
    (hk : k < values.length) : values.getD k default = values.getD k 0 := by
  rw [← List.getElem_eq_getD (l := values) (i := k) (h := hk) default]
  rw [← List.getElem_eq_getD (l := values) (i := k) (h := hk) 0]

private theorem rat_weighted_list_sum4096_cast (values : List ℚ) :
    (((1 / 4096 : ℚ) * values.sum : ℚ) : ℝ) =
      (1 / 4096 : ℝ) * ((values.sum : ℚ) : ℝ) := by
  norm_cast
  norm_num

/-- Exact list endpoints for a rational Arb arc table can be fed to the uniform-partition integral
bound. The only analytic premise is the stated enclosure on every point of every closed arc. -/
theorem contour51_complex_intervalIntegral_real_bounds_of_uniform_list_partition
    {N : ℕ} (hN : 0 < N) (f : ℝ → ℂ) (hf : Continuous f)
    (lower upper : List ℚ) (hLowerLength : lower.length = N) (hUpperLength : upper.length = N)
    (hlo : ∀ k < N, ∀ x ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N),
      ((lower.getD k 0 : ℚ) : ℝ) ≤ (f x).re)
    (hhi : ∀ k < N, ∀ x ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N),
      (f x).re ≤ ((upper.getD k 0 : ℚ) : ℝ)) :
    (1 / (N : ℝ)) * ((lower.sum : ℚ) : ℝ) ≤
        (∫ x in (0 : ℝ)..1, f x).re ∧
      (∫ x in (0 : ℝ)..1, f x).re ≤
        (1 / (N : ℝ)) * ((upper.sum : ℚ) : ℝ) := by
  have hLowerSumQ : lower.sum =
      ∑ k ∈ Finset.range N, lower.getD k 0 := by
    calc
      lower.sum = ∑ k ∈ Finset.range lower.length, lower.getD k default :=
        list_sum_eq_finset_range_getD lower
      _ = ∑ k ∈ Finset.range lower.length, lower.getD k 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact list_rat_getD_default_eq_zero lower k (Finset.mem_range.mp hk)
      _ = ∑ k ∈ Finset.range N, lower.getD k 0 := by rw [hLowerLength]
  have hUpperSumQ : upper.sum =
      ∑ k ∈ Finset.range N, upper.getD k 0 := by
    calc
      upper.sum = ∑ k ∈ Finset.range upper.length, upper.getD k default :=
        list_sum_eq_finset_range_getD upper
      _ = ∑ k ∈ Finset.range upper.length, upper.getD k 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact list_rat_getD_default_eq_zero upper k (Finset.mem_range.mp hk)
      _ = ∑ k ∈ Finset.range N, upper.getD k 0 := by rw [hUpperLength]
  have hLowerSum : ((lower.sum : ℚ) : ℝ) =
      ∑ k ∈ Finset.range N, ((lower.getD k 0 : ℚ) : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hLowerSumQ
    simpa only [Rat.cast_list_sum, Rat.cast_sum] using h
  have hUpperSum : ((upper.sum : ℚ) : ℝ) =
      ∑ k ∈ Finset.range N, ((upper.getD k 0 : ℚ) : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hUpperSumQ
    simpa only [Rat.cast_list_sum, Rat.cast_sum] using h
  have hPartition := contour51_complex_intervalIntegral_real_bounds_of_uniform_partition
    hN f hf (fun k => ((lower.getD k 0 : ℚ) : ℝ))
      (fun k => ((upper.getD k 0 : ℚ) : ℝ)) hlo hhi
  constructor
  · calc
      (1 / (N : ℝ)) * ((lower.sum : ℚ) : ℝ) =
          (1 / (N : ℝ)) *
            (∑ k ∈ Finset.range N, ((lower.getD k 0 : ℚ) : ℝ)) := by rw [hLowerSum]
      _ ≤ (∫ x in (0 : ℝ)..1, f x).re := hPartition.1
  · calc
      (∫ x in (0 : ℝ)..1, f x).re ≤
          (1 / (N : ℝ)) *
            (∑ k ∈ Finset.range N, ((upper.getD k 0 : ℚ) : ℝ)) := hPartition.2
      _ = (1 / (N : ℝ)) * ((upper.sum : ℚ) : ℝ) := by rw [hUpperSum]

/-- The unproved Arb-to-Lean inclusion needed to transfer the exact 4096-arc table for
`e₀,e₁,e₂`. It quantifies over every point of each closed arc; the table samples alone do not
establish this proposition. -/
def contour51Arb4096FirstThreeArcEvaluatorInclusion : Prop :=
  (∀ k : ℕ, k < 4096 → ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    ((contour51Arb4096LowerArcEndpoint0 k : ℚ) : ℝ) ≤
        (contour51OriginalAngularResidualIntegrand 0 (-Real.pi * u)).re ∧
      (contour51OriginalAngularResidualIntegrand 0 (-Real.pi * u)).re ≤
        ((contour51Arb4096UpperArcEndpoint0 k : ℚ) : ℝ)) ∧
  (∀ k : ℕ, k < 4096 → ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    ((contour51Arb4096LowerArcEndpoint1 k : ℚ) : ℝ) ≤
        (contour51OriginalAngularResidualIntegrand 1 (-Real.pi * u)).re ∧
      (contour51OriginalAngularResidualIntegrand 1 (-Real.pi * u)).re ≤
        ((contour51Arb4096UpperArcEndpoint1 k : ℚ) : ℝ)) ∧
  (∀ k : ℕ, k < 4096 → ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    ((contour51Arb4096LowerArcEndpoint2 k : ℚ) : ℝ) ≤
        (contour51OriginalAngularResidualIntegrand 2 (-Real.pi * u)).re ∧
      (contour51OriginalAngularResidualIntegrand 2 (-Real.pi * u)).re ≤
        ((contour51Arb4096UpperArcEndpoint2 k : ℚ) : ℝ))

/-- If the original angular evaluator is enclosed on every 4096-arc interval by the external Arb
ranges, the exact rational list sums transfer the recorded interval bounds to the three lower-path
integrals. This theorem isolates the remaining analytic inclusion as an explicit hypothesis. -/
theorem contour51ArbFirstThreeLowerPathResidualIntervalBounds_of_4096_arc_evaluator_inclusion
    (hArc : contour51Arb4096FirstThreeArcEvaluatorInclusion) :
    contour51ArbFirstThreeLowerPathResidualIntervalBounds := by
  have hData := contour51Arb4096FirstThreeWeightedRecordedBounds
  rcases hData with ⟨hLo0, hHi0, hLo1, hHi1, hLo2, hHi2⟩
  have hRecLo0 : contour51ArbRecordedResidualLower 0 = contour51Arb4096RecordedLower0 := by
    norm_num [contour51ArbRecordedResidualLower, contour51Arb4096RecordedLower0]
  have hRecHi0 : contour51ArbRecordedResidualUpper 0 = contour51Arb4096RecordedUpper0 := by
    norm_num [contour51ArbRecordedResidualUpper, contour51Arb4096RecordedUpper0]
  have hRecLo1 : contour51ArbRecordedResidualLower 1 = contour51Arb4096RecordedLower1 := by
    norm_num [contour51ArbRecordedResidualLower, contour51Arb4096RecordedLower1]
  have hRecHi1 : contour51ArbRecordedResidualUpper 1 = contour51Arb4096RecordedUpper1 := by
    norm_num [contour51ArbRecordedResidualUpper, contour51Arb4096RecordedUpper1]
  have hRecLo2 : contour51ArbRecordedResidualLower 2 = contour51Arb4096RecordedLower2 := by
    norm_num [contour51ArbRecordedResidualLower, contour51Arb4096RecordedLower2]
  have hRecHi2 : contour51ArbRecordedResidualUpper 2 = contour51Arb4096RecordedUpper2 := by
    norm_num [contour51ArbRecordedResidualUpper, contour51Arb4096RecordedUpper2]
  have hLine : Continuous (fun u : ℝ => -Real.pi * u) := by fun_prop
  have hCont0 := (continuous_contour51OriginalAngularResidualIntegrand 0).comp hLine
  have hCont1 := (continuous_contour51OriginalAngularResidualIntegrand 1).comp hLine
  have hCont2 := (continuous_contour51OriginalAngularResidualIntegrand 2).comp hLine
  have hArc0 := contour51_complex_intervalIntegral_real_bounds_of_uniform_list_partition
    (N := 4096) (by norm_num) (fun u =>
      contour51OriginalAngularResidualIntegrand 0 (-Real.pi * u)) hCont0
    contour51Arb4096LowerArcRanges0 contour51Arb4096UpperArcRanges0
    contour51Arb4096LowerArcRanges0_length contour51Arb4096UpperArcRanges0_length
    (by intro k hk u hu; exact (hArc.1 k hk u hu).1)
    (by intro k hk u hu; exact (hArc.1 k hk u hu).2)
  have hArc1 := contour51_complex_intervalIntegral_real_bounds_of_uniform_list_partition
    (N := 4096) (by norm_num) (fun u =>
      contour51OriginalAngularResidualIntegrand 1 (-Real.pi * u)) hCont1
    contour51Arb4096LowerArcRanges1 contour51Arb4096UpperArcRanges1
    contour51Arb4096LowerArcRanges1_length contour51Arb4096UpperArcRanges1_length
    (by intro k hk u hu; exact (hArc.2.1 k hk u hu).1)
    (by intro k hk u hu; exact (hArc.2.1 k hk u hu).2)
  have hArc2 := contour51_complex_intervalIntegral_real_bounds_of_uniform_list_partition
    (N := 4096) (by norm_num) (fun u =>
      contour51OriginalAngularResidualIntegrand 2 (-Real.pi * u)) hCont2
    contour51Arb4096LowerArcRanges2 contour51Arb4096UpperArcRanges2
    contour51Arb4096LowerArcRanges2_length contour51Arb4096UpperArcRanges2_length
    (by intro k hk u hu; exact (hArc.2.2 k hk u hu).1)
    (by intro k hk u hu; exact (hArc.2.2 k hk u hu).2)
  have hLo0Q : contour51ArbRecordedResidualLower 0 ≤
      (1 / 4096 : ℚ) * contour51Arb4096LowerArcRanges0.sum := by
    rw [hRecLo0]
    simpa [contour51Arb4096WeightedLower0] using hLo0
  have hHi0Q : (1 / 4096 : ℚ) * contour51Arb4096UpperArcRanges0.sum ≤
      contour51ArbRecordedResidualUpper 0 := by
    rw [hRecHi0]
    simpa [contour51Arb4096WeightedUpper0] using hHi0
  have hLo1Q : contour51ArbRecordedResidualLower 1 ≤
      (1 / 4096 : ℚ) * contour51Arb4096LowerArcRanges1.sum := by
    rw [hRecLo1]
    simpa [contour51Arb4096WeightedLower1] using hLo1
  have hHi1Q : (1 / 4096 : ℚ) * contour51Arb4096UpperArcRanges1.sum ≤
      contour51ArbRecordedResidualUpper 1 := by
    rw [hRecHi1]
    simpa [contour51Arb4096WeightedUpper1] using hHi1
  have hLo2Q : contour51ArbRecordedResidualLower 2 ≤
      (1 / 4096 : ℚ) * contour51Arb4096LowerArcRanges2.sum := by
    rw [hRecLo2]
    simpa [contour51Arb4096WeightedLower2] using hLo2
  have hHi2Q : (1 / 4096 : ℚ) * contour51Arb4096UpperArcRanges2.sum ≤
      contour51ArbRecordedResidualUpper 2 := by
    rw [hRecHi2]
    simpa [contour51Arb4096WeightedUpper2] using hHi2
  have hLo0R : (contour51ArbRecordedResidualLower 0 : ℝ) ≤
      (1 / 4096 : ℝ) *
        ((contour51Arb4096LowerArcRanges0.sum : ℚ) : ℝ) := by
    calc
      (contour51ArbRecordedResidualLower 0 : ℝ) ≤
          (((1 / 4096 : ℚ) * contour51Arb4096LowerArcRanges0.sum : ℚ) : ℝ) := by
        exact_mod_cast hLo0Q
      _ = (1 / 4096 : ℝ) *
          ((contour51Arb4096LowerArcRanges0.sum : ℚ) : ℝ) :=
        rat_weighted_list_sum4096_cast contour51Arb4096LowerArcRanges0
  have hHi0R : (1 / 4096 : ℝ) *
      ((contour51Arb4096UpperArcRanges0.sum : ℚ) : ℝ) ≤
      (contour51ArbRecordedResidualUpper 0 : ℝ) := by
    calc
      (1 / 4096 : ℝ) *
          ((contour51Arb4096UpperArcRanges0.sum : ℚ) : ℝ) =
          (((1 / 4096 : ℚ) * contour51Arb4096UpperArcRanges0.sum : ℚ) : ℝ) :=
        (rat_weighted_list_sum4096_cast contour51Arb4096UpperArcRanges0).symm
      _ ≤ (contour51ArbRecordedResidualUpper 0 : ℝ) := by exact_mod_cast hHi0Q
  have hLo1R : (contour51ArbRecordedResidualLower 1 : ℝ) ≤
      (1 / 4096 : ℝ) *
        ((contour51Arb4096LowerArcRanges1.sum : ℚ) : ℝ) := by
    calc
      (contour51ArbRecordedResidualLower 1 : ℝ) ≤
          (((1 / 4096 : ℚ) * contour51Arb4096LowerArcRanges1.sum : ℚ) : ℝ) := by
        exact_mod_cast hLo1Q
      _ = (1 / 4096 : ℝ) *
          ((contour51Arb4096LowerArcRanges1.sum : ℚ) : ℝ) :=
        rat_weighted_list_sum4096_cast contour51Arb4096LowerArcRanges1
  have hHi1R : (1 / 4096 : ℝ) *
      ((contour51Arb4096UpperArcRanges1.sum : ℚ) : ℝ) ≤
      (contour51ArbRecordedResidualUpper 1 : ℝ) := by
    calc
      (1 / 4096 : ℝ) *
          ((contour51Arb4096UpperArcRanges1.sum : ℚ) : ℝ) =
          (((1 / 4096 : ℚ) * contour51Arb4096UpperArcRanges1.sum : ℚ) : ℝ) :=
        (rat_weighted_list_sum4096_cast contour51Arb4096UpperArcRanges1).symm
      _ ≤ (contour51ArbRecordedResidualUpper 1 : ℝ) := by exact_mod_cast hHi1Q
  have hLo2R : (contour51ArbRecordedResidualLower 2 : ℝ) ≤
      (1 / 4096 : ℝ) *
        ((contour51Arb4096LowerArcRanges2.sum : ℚ) : ℝ) := by
    calc
      (contour51ArbRecordedResidualLower 2 : ℝ) ≤
          (((1 / 4096 : ℚ) * contour51Arb4096LowerArcRanges2.sum : ℚ) : ℝ) := by
        exact_mod_cast hLo2Q
      _ = (1 / 4096 : ℝ) *
          ((contour51Arb4096LowerArcRanges2.sum : ℚ) : ℝ) :=
        rat_weighted_list_sum4096_cast contour51Arb4096LowerArcRanges2
  have hHi2R : (1 / 4096 : ℝ) *
      ((contour51Arb4096UpperArcRanges2.sum : ℚ) : ℝ) ≤
      (contour51ArbRecordedResidualUpper 2 : ℝ) := by
    calc
      (1 / 4096 : ℝ) *
          ((contour51Arb4096UpperArcRanges2.sum : ℚ) : ℝ) =
          (((1 / 4096 : ℚ) * contour51Arb4096UpperArcRanges2.sum : ℚ) : ℝ) :=
        (rat_weighted_list_sum4096_cast contour51Arb4096UpperArcRanges2).symm
      _ ≤ (contour51ArbRecordedResidualUpper 2 : ℝ) := by exact_mod_cast hHi2Q
  intro n hn
  interval_cases n
  · constructor
    · have hPath := hArc0.1
      simpa [contour51ArbLowerPathResidualIntegral] using le_trans hLo0R hPath
    · have hPath := hArc0.2
      simpa [contour51ArbLowerPathResidualIntegral] using le_trans hPath hHi0R
  · constructor
    · have hPath := hArc1.1
      simpa [contour51ArbLowerPathResidualIntegral] using le_trans hLo1R hPath
    · have hPath := hArc1.2
      simpa [contour51ArbLowerPathResidualIntegral] using le_trans hPath hHi1R
  · constructor
    · have hPath := hArc2.1
      simpa [contour51ArbLowerPathResidualIntegral] using le_trans hLo2R hPath
    · have hPath := hArc2.2
      simpa [contour51ArbLowerPathResidualIntegral] using le_trans hPath hHi2R

theorem contour51Arb4096SingleResidualIntervalBounds_of_arc_inclusion
    (n : ℕ) (lower upper : List ℚ)
    (hLowerLength : lower.length = 4096) (hUpperLength : upper.length = 4096)
    (hLoData : contour51ArbRecordedResidualLower n ≤ (1 / 4096 : ℚ) * lower.sum)
    (hHiData : (1 / 4096 : ℚ) * upper.sum ≤ contour51ArbRecordedResidualUpper n)
    (hlo : ∀ k : ℕ, k < 4096 →
      ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
        ((lower.getD k 0 : ℚ) : ℝ) ≤
          (contour51OriginalAngularResidualIntegrand n (-Real.pi * u)).re)
    (hhi : ∀ k : ℕ, k < 4096 →
      ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
        (contour51OriginalAngularResidualIntegrand n (-Real.pi * u)).re ≤
          ((upper.getD k 0 : ℚ) : ℝ)) :
    (contour51ArbRecordedResidualLower n : ℝ) ≤
        (contour51ArbLowerPathResidualIntegral n).re ∧
      (contour51ArbLowerPathResidualIntegral n).re ≤
        (contour51ArbRecordedResidualUpper n : ℝ) := by
  have hLine : Continuous (fun u : ℝ => -Real.pi * u) := by fun_prop
  have hCont := (continuous_contour51OriginalAngularResidualIntegrand n).comp hLine
  have hIntegral := contour51_complex_intervalIntegral_real_bounds_of_uniform_list_partition
    (N := 4096) (by norm_num)
    (fun u => contour51OriginalAngularResidualIntegrand n (-Real.pi * u)) hCont
    lower upper hLowerLength hUpperLength hlo hhi
  have hLowerReal : (contour51ArbRecordedResidualLower n : ℝ) ≤
      (1 / 4096 : ℝ) * ((lower.sum : ℚ) : ℝ) := by
    calc
      (contour51ArbRecordedResidualLower n : ℝ) ≤
          (((1 / 4096 : ℚ) * lower.sum : ℚ) : ℝ) := by exact_mod_cast hLoData
      _ = (1 / 4096 : ℝ) * ((lower.sum : ℚ) : ℝ) :=
        rat_weighted_list_sum4096_cast lower
  have hUpperReal : (1 / 4096 : ℝ) * ((upper.sum : ℚ) : ℝ) ≤
      (contour51ArbRecordedResidualUpper n : ℝ) := by
    calc
      (1 / 4096 : ℝ) * ((upper.sum : ℚ) : ℝ) =
          (((1 / 4096 : ℚ) * upper.sum : ℚ) : ℝ) :=
        (rat_weighted_list_sum4096_cast upper).symm
      _ ≤ (contour51ArbRecordedResidualUpper n : ℝ) := by exact_mod_cast hHiData
  constructor
  · calc
      (contour51ArbRecordedResidualLower n : ℝ) ≤
          (1 / 4096 : ℝ) * ((lower.sum : ℚ) : ℝ) := hLowerReal
      _ ≤ (∫ u in (0 : ℝ)..1,
          contour51OriginalAngularResidualIntegrand n (-Real.pi * u)).re := hIntegral.1
      _ = (contour51ArbLowerPathResidualIntegral n).re := by
        rfl
  · calc
      (contour51ArbLowerPathResidualIntegral n).re =
          (∫ u in (0 : ℝ)..1,
            contour51OriginalAngularResidualIntegrand n (-Real.pi * u)).re := by
              rfl
      _ ≤ (1 / 4096 : ℝ) * ((upper.sum : ℚ) : ℝ) := hIntegral.2
      _ ≤ (contour51ArbRecordedResidualUpper n : ℝ) := hUpperReal

/-- Pointwise Arb-to-Lean inclusion for all six residual integrands on all 4096 closed arcs.
This is an explicit analytic obligation, including the validated Taylor/Cauchy remainder; finite
samples do not prove it. -/
def contour51Arb4096AllSixArcEvaluatorInclusion : Prop :=
  contour51Arb4096FirstThreeArcEvaluatorInclusion ∧
  (∀ k : ℕ, k < 4096 → ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    ((contour51Arb4096LowerArcEndpoint3 k : ℚ) : ℝ) ≤
        (contour51OriginalAngularResidualIntegrand 3 (-Real.pi * u)).re ∧
      (contour51OriginalAngularResidualIntegrand 3 (-Real.pi * u)).re ≤
        ((contour51Arb4096UpperArcEndpoint3 k : ℚ) : ℝ)) ∧
  (∀ k : ℕ, k < 4096 → ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    ((contour51Arb4096LowerArcEndpoint4 k : ℚ) : ℝ) ≤
        (contour51OriginalAngularResidualIntegrand 4 (-Real.pi * u)).re ∧
      (contour51OriginalAngularResidualIntegrand 4 (-Real.pi * u)).re ≤
        ((contour51Arb4096UpperArcEndpoint4 k : ℚ) : ℝ)) ∧
  (∀ k : ℕ, k < 4096 → ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    ((contour51Arb4096LowerArcEndpoint5 k : ℚ) : ℝ) ≤
        (contour51OriginalAngularResidualIntegrand 5 (-Real.pi * u)).re ∧
      (contour51OriginalAngularResidualIntegrand 5 (-Real.pi * u)).re ≤
        ((contour51Arb4096UpperArcEndpoint5 k : ℚ) : ℝ))

/-- Under the six all-arcs evaluator inclusions, the original lower-path integrals for
`e₀,…,e₅` lie in the exact recorded Arb intervals. This remains conditional until the analytic
pointwise inclusion proposition is proved. -/
theorem contour51ArbAllSixLowerPathResidualIntervalBounds_of_4096_arc_evaluator_inclusion
    (hArc : contour51Arb4096AllSixArcEvaluatorInclusion) :
    contour51ArbLowerPathResidualIntervalBounds := by
  have hFirst :=
    contour51ArbFirstThreeLowerPathResidualIntervalBounds_of_4096_arc_evaluator_inclusion hArc.1
  have hData := contour51Arb4096AllSixWeightedRecordedBounds
  rcases hData with
    ⟨hLo0, hHi0, hLo1, hHi1, hLo2, hHi2, hLo3, hHi3, hLo4, hHi4, hLo5, hHi5⟩
  have hRecLo3 : contour51ArbRecordedResidualLower 3 = contour51Arb4096RecordedLower3 := by
    norm_num [contour51ArbRecordedResidualLower, contour51Arb4096RecordedLower3]
  have hRecHi3 : contour51ArbRecordedResidualUpper 3 = contour51Arb4096RecordedUpper3 := by
    norm_num [contour51ArbRecordedResidualUpper, contour51Arb4096RecordedUpper3]
  have hRecLo4 : contour51ArbRecordedResidualLower 4 = contour51Arb4096RecordedLower4 := by
    norm_num [contour51ArbRecordedResidualLower, contour51Arb4096RecordedLower4]
  have hRecHi4 : contour51ArbRecordedResidualUpper 4 = contour51Arb4096RecordedUpper4 := by
    norm_num [contour51ArbRecordedResidualUpper, contour51Arb4096RecordedUpper4]
  have hRecLo5 : contour51ArbRecordedResidualLower 5 = contour51Arb4096RecordedLower5 := by
    norm_num [contour51ArbRecordedResidualLower, contour51Arb4096RecordedLower5]
  have hRecHi5 : contour51ArbRecordedResidualUpper 5 = contour51Arb4096RecordedUpper5 := by
    norm_num [contour51ArbRecordedResidualUpper, contour51Arb4096RecordedUpper5]
  have hLo3Q : contour51ArbRecordedResidualLower 3 ≤
      (1 / 4096 : ℚ) * contour51Arb4096LowerArcRanges3.sum := by
    rw [hRecLo3]
    simpa [contour51Arb4096WeightedLower3] using hLo3
  have hHi3Q : (1 / 4096 : ℚ) * contour51Arb4096UpperArcRanges3.sum ≤
      contour51ArbRecordedResidualUpper 3 := by
    rw [hRecHi3]
    simpa [contour51Arb4096WeightedUpper3] using hHi3
  have hLo4Q : contour51ArbRecordedResidualLower 4 ≤
      (1 / 4096 : ℚ) * contour51Arb4096LowerArcRanges4.sum := by
    rw [hRecLo4]
    simpa [contour51Arb4096WeightedLower4] using hLo4
  have hHi4Q : (1 / 4096 : ℚ) * contour51Arb4096UpperArcRanges4.sum ≤
      contour51ArbRecordedResidualUpper 4 := by
    rw [hRecHi4]
    simpa [contour51Arb4096WeightedUpper4] using hHi4
  have hLo5Q : contour51ArbRecordedResidualLower 5 ≤
      (1 / 4096 : ℚ) * contour51Arb4096LowerArcRanges5.sum := by
    rw [hRecLo5]
    simpa [contour51Arb4096WeightedLower5] using hLo5
  have hHi5Q : (1 / 4096 : ℚ) * contour51Arb4096UpperArcRanges5.sum ≤
      contour51ArbRecordedResidualUpper 5 := by
    rw [hRecHi5]
    simpa [contour51Arb4096WeightedUpper5] using hHi5
  have hPath3 := contour51Arb4096SingleResidualIntervalBounds_of_arc_inclusion
    3 contour51Arb4096LowerArcRanges3 contour51Arb4096UpperArcRanges3
    contour51Arb4096LowerArcRanges3_length contour51Arb4096UpperArcRanges3_length
    hLo3Q hHi3Q
    (by intro k hk u hu; exact (hArc.2.1 k hk u hu).1)
    (by intro k hk u hu; exact (hArc.2.1 k hk u hu).2)
  have hPath4 := contour51Arb4096SingleResidualIntervalBounds_of_arc_inclusion
    4 contour51Arb4096LowerArcRanges4 contour51Arb4096UpperArcRanges4
    contour51Arb4096LowerArcRanges4_length contour51Arb4096UpperArcRanges4_length
    hLo4Q hHi4Q
    (by intro k hk u hu; exact (hArc.2.2.1 k hk u hu).1)
    (by intro k hk u hu; exact (hArc.2.2.1 k hk u hu).2)
  have hPath5 := contour51Arb4096SingleResidualIntervalBounds_of_arc_inclusion
    5 contour51Arb4096LowerArcRanges5 contour51Arb4096UpperArcRanges5
    contour51Arb4096LowerArcRanges5_length contour51Arb4096UpperArcRanges5_length
    hLo5Q hHi5Q
    (by intro k hk u hu; exact (hArc.2.2.2 k hk u hu).1)
    (by intro k hk u hu; exact (hArc.2.2.2 k hk u hu).2)
  intro n hn
  interval_cases n
  · exact hFirst 0 (by norm_num)
  · exact hFirst 1 (by norm_num)
  · exact hFirst 2 (by norm_num)
  · exact hPath3
  · exact hPath4
  · exact hPath5

theorem contour51ArbResidualIntervalBounds_of_lower_path_bounds
    (hPath : contour51ArbLowerPathResidualIntervalBounds) :
    contour51ArbResidualIntervalBounds := by
  intro n hn
  rw [contour51OriginalResidualIntegral_eq_lower_path]
  simpa [contour51ArbLowerPathResidualIntegral] using hPath n hn

theorem contour51ArbFirstThreeResidualIntervalBounds_of_lower_path_bounds
    (hPath : contour51ArbFirstThreeLowerPathResidualIntervalBounds) :
    contour51ArbFirstThreeResidualIntervalBounds := by
  intro n hn
  rw [contour51OriginalResidualIntegral_eq_lower_path]
  simpa [contour51ArbLowerPathResidualIntegral] using hPath n hn

/-- Conditional first central-window result stated directly in the Arb path coordinates, with
its exact absolute rational determinant margin. The only remaining input here is the rigorous
inclusion of each complete Lean path integral in its external Arb interval. -/
theorem completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals
    (hPath : contour51ArbFirstThreeLowerPathResidualIntervalBounds) :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧
      1 / 1000000000 < CarrySigmaPade.sigmaPadeD 0 0 := by
  exact completedNative_sigmaPadeD_zero_pos_of_contour51_arb_intervals
    (contour51ArbFirstThreeResidualIntervalBounds_of_lower_path_bounds hPath)

#print axioms contour51OriginalResponse_odd
#print axioms contour51OriginalResponse_eq_sigmaXiLogDerivative
#print axioms contour51SigmaXiLogDerivative_eq_zeta_gamma_factors
#print axioms contour51GammaReal_logDeriv_eq_digamma
#print axioms contour51SigmaXiLogDerivative_eq_arb_formula
#print axioms contour51OriginalResponse_eq_arb_formula
#print axioms contour51OriginalResponse_eq_arb_formula_lower_path
#print axioms contour51_intervalIntegral_bounds_of_uniform_partition
#print axioms contour51_complex_intervalIntegral_real_bounds_of_uniform_partition
#print axioms contour51_complex_intervalIntegral_real_bounds_of_uniform_list_partition
#print axioms list_sum_eq_finset_range_getD
#print axioms contour51OriginalResidualQuotient_neg
#print axioms contour51OriginalAngularResidualIntegrand_periodic
#print axioms periodic_pi_integral_full_eq_lower_parameter
#print axioms contour51OriginalResidualIntegral_eq_lower_path
#print axioms contour51ArbResidualIntervalBounds_of_lower_path_bounds
#print axioms contour51ArbFirstThreeLowerPathResidualIntervalBounds_of_4096_arc_evaluator_inclusion
#print axioms contour51Arb4096SingleResidualIntervalBounds_of_arc_inclusion
#print axioms contour51ArbAllSixLowerPathResidualIntervalBounds_of_4096_arc_evaluator_inclusion
#print axioms completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals

end
end CarrySigmaObstruction
