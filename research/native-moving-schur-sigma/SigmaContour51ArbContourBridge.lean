import SigmaContour51ArbResidualGate
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
#print axioms contour51OriginalResidualQuotient_neg
#print axioms contour51OriginalAngularResidualIntegrand_periodic
#print axioms periodic_pi_integral_full_eq_lower_parameter
#print axioms contour51OriginalResidualIntegral_eq_lower_path
#print axioms contour51ArbResidualIntervalBounds_of_lower_path_bounds
#print axioms completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals

end
end CarrySigmaObstruction
