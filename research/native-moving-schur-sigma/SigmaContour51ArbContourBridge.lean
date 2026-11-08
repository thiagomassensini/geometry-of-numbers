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

open Complex MeasureTheory
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
#print axioms contour51OriginalResidualQuotient_neg
#print axioms contour51OriginalAngularResidualIntegrand_periodic
#print axioms periodic_pi_integral_full_eq_lower_parameter
#print axioms contour51OriginalResidualIntegral_eq_lower_path
#print axioms contour51ArbResidualIntervalBounds_of_lower_path_bounds
#print axioms completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals

end
end CarrySigmaObstruction
