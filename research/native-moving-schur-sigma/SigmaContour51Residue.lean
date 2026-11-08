import SigmaContour51DiskBridge
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Local residues of the original radius-51 continuation

This file records the exact simple-pole residue of the logarithmic derivative. The finite
analytic-removal/gluing argument and source-normalized global contour formula are completed in
`SigmaContour51FiniteContour.lean`; see `mission-central-contour51-20261108/C2_RESIDUE_REDUCTION.md`.
-/

namespace CarrySigmaObstruction

open Complex
open Filter Topology
open Set

set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The normalized contour integral of a regular function's Cauchy kernel is its Taylor
coefficient at the center. This isolates the library step needed after the finite poles have been
removed from the original logarithmic derivative. -/
theorem normalized_circle_integral_coefficient (G : ℂ → ℂ) (n : ℕ)
    (hG : DiffContOnCl ℂ G (Metric.ball (0 : ℂ) 51)) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(0, 51), G z / z ^ (n + 1) =
      iteratedDeriv n G 0 / (n.factorial : ℂ) := by
  have hformula :=
    DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul
      (f := G) (c := (0 : ℂ)) (R := 51) (by norm_num : (0 : ℝ) < 51) n hG
  have hkernel :
      (∮ z in C(0, 51), G z / z ^ (n + 1)) =
        ∮ z in C(0, 51), (1 / (z - 0) ^ (n + 1)) • G z := by
    apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 51)
    intro z hz
    simp [smul_eq_mul, div_eq_mul_inv, sub_zero, mul_comm]
  have hA : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := two_pi_I_ne_zero
  rw [hkernel, hformula]
  simp only [smul_eq_mul, div_eq_mul_inv]
  calc
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ((2 * Real.pi * Complex.I) * (n.factorial : ℂ)⁻¹ * iteratedDeriv n G 0) =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I)) *
        ((n.factorial : ℂ)⁻¹ * iteratedDeriv n G 0) := by ring
    _ = (n.factorial : ℂ)⁻¹ * iteratedDeriv n G 0 := by
      rw [inv_mul_cancel₀ hA]
      simp
    _ = iteratedDeriv n G 0 * (n.factorial : ℂ)⁻¹ := by ring

/-- At a simple zero of an analytic characteristic, its original logarithmic derivative
`-F'/(2F)` has residue `-1/2`, expressed as a punctured-neighborhood limit. -/
theorem analytic_simple_zero_log_derivative_residue
    {F : ℂ → ℂ} {a : ℂ} (hF : AnalyticAt ℂ F a)
    (horder : analyticOrderAt F a = 1) :
    Tendsto (fun z : ℂ => (z - a) * (-deriv F z / ((2 : ℂ) * F z)))
      (𝓝[≠] a) (𝓝 (-(1 / 2 : ℂ))) := by
  obtain ⟨g, hg, hgne, hfactor⟩ :=
    (hF.analyticOrderAt_eq_natCast (n := 1)).mp horder
  have hfactor' : F =ᶠ[𝓝 a] fun z : ℂ => (z - a) * g z := by
    filter_upwards [hfactor] with z hz
    simpa [pow_one, smul_eq_mul] using hz
  have hderiv_a : deriv F a = g a := by
    calc
      deriv F a = deriv (fun z : ℂ => (z - a) * g z) a := hfactor'.deriv_eq
      _ = g a := by
        rw [deriv_fun_mul (by fun_prop) hg.differentiableAt]
        simp
  have hgne_near : ∀ᶠ z : ℂ in 𝓝 a, g z ≠ 0 :=
    hg.continuousAt.eventually_ne hgne
  have hza : ∀ᶠ z : ℂ in 𝓝[≠] a, z ≠ a := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz
  have hfac_near : ∀ᶠ z : ℂ in 𝓝[≠] a, F z ≠ 0 := by
    filter_upwards [hfactor'.filter_mono nhdsWithin_le_nhds,
      hgne_near.filter_mono nhdsWithin_le_nhds, hza] with z hfac hgz hne
    rw [hfac]
    exact mul_ne_zero (sub_ne_zero.mpr hne) hgz
  have hquot_eq : (fun z : ℂ => F z / (z - a)) =ᶠ[𝓝[≠] a] g := by
    filter_upwards [hfactor'.filter_mono nhdsWithin_le_nhds, hza] with z hfac hne
    rw [hfac]
    field_simp [hne]
  have hquot_tendsto : Tendsto (fun z : ℂ => F z / (z - a)) (𝓝[≠] a) (𝓝 (g a)) :=
    Tendsto.congr' hquot_eq.symm
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hderiv_tendsto : Tendsto (deriv F) (𝓝[≠] a) (𝓝 (deriv F a)) :=
    hF.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hden_tendsto : Tendsto (fun z : ℂ => (2 : ℂ) * (F z / (z - a)))
      (𝓝[≠] a) (𝓝 ((2 : ℂ) * g a)) :=
    tendsto_const_nhds.mul hquot_tendsto
  have hratio_tendsto : Tendsto
      (fun z : ℂ => -deriv F z / ((2 : ℂ) * (F z / (z - a))))
      (𝓝[≠] a) (𝓝 (-deriv F a / ((2 : ℂ) * g a))) := by
    apply hderiv_tendsto.neg.div hden_tendsto
    exact mul_ne_zero (by norm_num) hgne
  have hratio_limit : -deriv F a / ((2 : ℂ) * g a) = -(1 / 2 : ℂ) := by
    rw [hderiv_a]
    field_simp [hgne]
  have hratio_tendsto' : Tendsto
      (fun z : ℂ => -deriv F z / ((2 : ℂ) * (F z / (z - a))))
      (𝓝[≠] a) (𝓝 (-(1 / 2 : ℂ))) := by
    rw [← hratio_limit]
    exact hratio_tendsto
  have hrewrite :
      (fun z : ℂ => (z - a) * (-deriv F z / ((2 : ℂ) * F z))) =ᶠ[𝓝[≠] a]
        fun z : ℂ => -deriv F z / ((2 : ℂ) * (F z / (z - a))) := by
    filter_upwards [hfac_near, hza] with z hFz hne
    field_simp [hFz, hne]
  exact Tendsto.congr' hrewrite.symm hratio_tendsto'

/-- A simple zero of an analytic characteristic admits an analytic extension after its
logarithmic-derivative pole is cancelled. The extension agrees with the cancelled expression
throughout a punctured neighborhood; its value at the zero is supplied by the local factor. -/
theorem analytic_simple_zero_log_derivative_pole_cancellation
    {F : ℂ → ℂ} {a : ℂ} (hF : AnalyticAt ℂ F a)
    (horder : analyticOrderAt F a = 1) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧
      H =ᶠ[𝓝[≠] a] fun z : ℂ =>
        -deriv F z / ((2 : ℂ) * F z) + 1 / ((2 : ℂ) * (z - a)) := by
  obtain ⟨g, hg, hgne, hfactor⟩ :=
    (hF.analyticOrderAt_eq_natCast (n := 1)).mp horder
  have hfactor' : F =ᶠ[𝓝 a] fun z : ℂ => (z - a) * g z := by
    filter_upwards [hfactor] with z hz
    simpa [pow_one, smul_eq_mul] using hz
  have hderiv' : deriv F =ᶠ[𝓝 a] deriv (fun z : ℂ => (z - a) * g z) :=
    hfactor'.deriv
  have hgNonzero : ∀ᶠ z : ℂ in 𝓝 a, g z ≠ 0 :=
    hg.continuousAt.eventually_ne hgne
  let L : ℂ → ℂ := fun z => -deriv g z / ((2 : ℂ) * g z)
  have hL : AnalyticAt ℂ L a := by
    dsimp [L]
    exact (hg.deriv.neg).div (analyticAt_const.mul hg) (mul_ne_zero (by norm_num) hgne)
  let H : ℂ → ℂ := fun z =>
    if z = a then L a else
      -deriv F z / ((2 : ℂ) * F z) + 1 / ((2 : ℂ) * (z - a))
  have hEq : H =ᶠ[𝓝 a] L := by
    filter_upwards [hfactor', hderiv', hg.eventually_analyticAt, hgNonzero]
      with z hFz hFderiv hzAnalytic hzNonzero
    by_cases hza : z = a
    · subst z
      simp [H]
    · have hprod : deriv (fun u : ℂ => (u - a) * g u) z =
          g z + (z - a) * deriv g z := by
        rw [deriv_fun_mul (by fun_prop) hzAnalytic.differentiableAt]
        simp
      have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
      dsimp [H, L]
      rw [if_neg hza, hFderiv, hprod, hFz]
      field_simp [hza', hzNonzero]
      ring
  let Hfun : ℂ → ℂ := H
  have hanalytic : AnalyticAt ℂ Hfun a := hL.congr hEq.symm
  have hpunctured : Hfun =ᶠ[𝓝[≠] a] fun z : ℂ =>
      -deriv F z / ((2 : ℂ) * F z) + 1 / ((2 : ℂ) * (z - a)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hza : z ≠ a := by simpa using hz
    simp [Hfun, H, hza]
  exact ⟨Hfun, hanalytic, hpunctured⟩

/-- Every zero of the original continuation in the radius-51 disk has the same local residue. -/
theorem sigmaContour51_original_characteristic_logDerivative_residue
    {z : ℂ} (hz : completedNativeCharacteristicContinuation z = 0)
    (hball : ‖z‖ ≤ 51) :
    Tendsto
      (fun w : ℂ => (w - z) *
        (-deriv completedNativeCharacteristicContinuation w /
          ((2 : ℂ) * completedNativeCharacteristicContinuation w)))
      (𝓝[≠] z) (𝓝 (-(1 / 2 : ℂ))) := by
  have hF := completedNativeCharacteristicContinuation_analyticAt z
  obtain ⟨_, _, _, _, _, _, _, hsimple⟩ :=
    sigmaContour51_original_characteristic_roots
  exact analytic_simple_zero_log_derivative_residue hF (hsimple z hz hball)

#print axioms analytic_simple_zero_log_derivative_residue
#print axioms analytic_simple_zero_log_derivative_pole_cancellation
#print axioms sigmaContour51_original_characteristic_logDerivative_residue
#print axioms normalized_circle_integral_coefficient

end CarrySigmaObstruction
