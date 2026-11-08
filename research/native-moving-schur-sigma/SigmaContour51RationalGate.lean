import SigmaCentralTenModeRationalGate
import SigmaPadeCorrespondence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# Exact C=40 finite gates and conditional radius-51 closure

The residual and ten scales remain explicit assumptions here. In particular this file does not
identify either one from the zeros; it only closes the rational/algebraic implication once the
analytic contour and finite-sign obligations are supplied.
-/

namespace CarrySigmaCentral

open CarrySigmaSource Complex Set
open Metric
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The shallow-window margin implied by the contour's `C=40` residual bound. -/
def contour40EarlyMargin (s : ℕ) : ℝ :=
  lowMoment s * lowMoment (s + 2) -
    (highMoment (s + 1) + 40 * eta ^ (s + 2)) ^ 2

/-- Radius `51` converts the direct circle estimate `(4/5)/51^(2n+1)` into the
`C=40`, `eta=1/2500` tail used by the rational gates. -/
theorem contour40_radius_conversion (n : ℕ) :
    (4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 1) ≤ 40 * eta ^ (n + 1) := by
  have hden : (50 : ℝ) ^ (2 * n + 1) ≤ (51 : ℝ) ^ (2 * n + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hdenPos : 0 < (50 : ℝ) ^ (2 * n + 1) := by positivity
  have hpow : (50 : ℝ) ^ (2 * n + 2) = (2500 : ℝ) ^ (n + 1) := by
    calc
      (50 : ℝ) ^ (2 * n + 2) = (50 : ℝ) ^ (2 * (n + 1)) := by congr 1
      _ = ((50 : ℝ) ^ 2) ^ (n + 1) := by rw [← pow_mul]
      _ = (2500 : ℝ) ^ (n + 1) := by norm_num
  calc
    (4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 1) ≤
        (4 / 5 : ℝ) / (50 : ℝ) ^ (2 * n + 1) :=
      div_le_div_of_nonneg_left (by norm_num) hdenPos hden
    _ = 40 / (50 : ℝ) ^ (2 * n + 2) := by
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
      field_simp [hdenPos.ne']
      ring
    _ = 40 / (2500 : ℝ) ^ (n + 1) := by rw [hpow]
    _ = 40 * eta ^ (n + 1) := by simp [eta, div_eq_mul_inv]

/-- A uniform `4/5` bound on the radius-51 circle gives the required estimate for the normalized
Cauchy integral of `R(z)/z^(2n+2)`. -/
theorem contour51_normalized_integral_bound (R : ℂ → ℂ) (n : ℕ)
    (hR : ∀ z ∈ sphere (0 : ℂ) 51, ‖R z‖ ≤ 4 / 5) :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, 51), R z / z ^ (2 * n + 2)‖ ≤
        (4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 1) := by
  have hkernel : ∀ z ∈ sphere (0 : ℂ) 51,
      ‖R z / z ^ (2 * n + 2)‖ ≤ (4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 2) := by
    intro z hz
    have hzNorm : ‖z‖ = 51 := by
      simpa using (mem_sphere_iff_norm.mp hz)
    have hpow : ‖z ^ (2 * n + 2)‖ = (51 : ℝ) ^ (2 * n + 2) := by
      rw [norm_pow, hzNorm]
    calc
      ‖R z / z ^ (2 * n + 2)‖ = ‖R z‖ / ‖z ^ (2 * n + 2)‖ := norm_div _ _
      _ = ‖R z‖ / (51 : ℝ) ^ (2 * n + 2) := by rw [hpow]
      _ ≤ (4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 2) :=
        div_le_div_of_nonneg_right (hR z hz) (by positivity)
  have hIntegral :=
    _root_.circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (by norm_num : (0 : ℝ) ≤ 51) hkernel
  have hscale : (51 : ℝ) * ((4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 2)) =
      (4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 1) := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
    field_simp
  calc
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(0, 51), R z / z ^ (2 * n + 2)‖ ≤
        51 * ((4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 2)) := hIntegral
    _ = (4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 1) := hscale

/-- A C2 contour identity plus the uniform circle estimate implies the `C=40` residual tail.
This isolates the analytic obligations from the radius conversion and rational gate. -/
theorem contour40_tail_of_circle_identity (R : ℂ → ℂ) (e : ℝ) (n : ℕ)
    (hR : ∀ z ∈ sphere (0 : ℂ) 51, ‖R z‖ ≤ 4 / 5)
    (hidentity : (e : ℂ) = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, 51), R z / z ^ (2 * n + 2)) :
    |e| ≤ 40 * eta ^ (n + 1) := by
  calc
    |e| = ‖(e : ℂ)‖ := by simp
    _ = ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(0, 51), R z / z ^ (2 * n + 2)‖ := by rw [hidentity]
    _ ≤ (4 / 5 : ℝ) / (51 : ℝ) ^ (2 * n + 1) :=
      contour51_normalized_integral_bound R n hR
    _ ≤ 40 * eta ^ (n + 1) := contour40_radius_conversion n

/-- The four shallow-window margins are strict exact-rational inequalities. -/
theorem contour40EarlyMargin_pos (s : ℕ) (hs : s < 4) :
    0 < contour40EarlyMargin s := by
  interval_cases s <;>
    norm_num [contour40EarlyMargin, lowMoment, highMoment, tenModeMoment,
      finitePowerMoment, eta, scaleLower, scaleUpper, ordinateLower, ordinateUpper,
      Fin.sum_univ_succ]

/-- The circle estimate `|e_n| ≤ 40*eta^(n+1)` is enough for the four shallow windows,
provided the six original residuals are nonnegative. -/
theorem hankel2_pos_small_of_contour40_tail
    (a : Fin 10 → ℝ) (e : ℕ → ℝ) (s : ℕ)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i)
    (htail : ∀ n, |e n| ≤ 40 * eta ^ (n + 1))
    (hnonneg : ∀ n, n ≤ 5 → 0 ≤ e n)
    (hs : s < 4) :
    0 < hankel2 (fun n => tenModeMoment a n + e n) s := by
  let H : ℕ → ℝ := fun n => tenModeMoment a n + e n
  have ha : ∀ i, 0 < a i := tenScale_pos_of_box_bounds a hbox
  have he0 : 0 ≤ e s := hnonneg s (by omega)
  have he2 : 0 ≤ e (s + 2) := hnonneg (s + 2) (by omega)
  have he1 : 0 ≤ e (s + 1) := hnonneg (s + 1) (by omega)
  have hRpos : 0 < lowMoment (s + 2) := by
    unfold lowMoment
    exact tenModeMoment_pos scaleLower (s + 2) (fun i => (scale_box_bounds i).1)
  have hPlo : lowMoment s ≤ H s := by
    dsimp [H]
    exact (lowMoment_le_of_box_bounds a hbox s).trans (le_add_of_nonneg_right he0)
  have hPro : lowMoment (s + 2) ≤ H (s + 2) := by
    dsimp [H]
    exact (lowMoment_le_of_box_bounds a hbox (s + 2)).trans
      (le_add_of_nonneg_right he2)
  have htailMid : e (s + 1) ≤ 40 * eta ^ (s + 2) := by
    have h := (abs_le.mp (htail (s + 1))).2
    simpa [Nat.add_assoc] using h
  have hmid : H (s + 1) ≤ highMoment (s + 1) + 40 * eta ^ (s + 2) := by
    dsimp [H]
    exact add_le_add (tenModeMoment_le_highMoment_of_box_bounds a hbox (s + 1))
      htailMid
  have hHpos : 0 ≤ H s := by
    dsimp [H]
    exact add_nonneg (le_of_lt (tenModeMoment_pos a s ha)) he0
  have hmidpos : 0 ≤ H (s + 1) := by
    dsimp [H]
    exact add_nonneg (le_of_lt (tenModeMoment_pos a (s + 1) ha)) he1
  have hmidUpperPos : 0 ≤ highMoment (s + 1) + 40 * eta ^ (s + 2) := by
    apply add_nonneg
    · unfold highMoment
      exact le_of_lt (tenModeMoment_pos scaleUpper (s + 1)
        (fun i => (scale_box_bounds i).2.2))
    · exact mul_nonneg (by norm_num) (pow_nonneg eta_pos.le _)
  have hprod : lowMoment s * lowMoment (s + 2) ≤ H s * H (s + 2) :=
    mul_le_mul hPlo hPro hRpos.le hHpos
  have hsquare : H (s + 1) ^ 2 ≤
      (highMoment (s + 1) + 40 * eta ^ (s + 2)) ^ 2 :=
    (sq_le_sq₀ hmidpos hmidUpperPos).2 hmid
  have hmargin : 0 < contour40EarlyMargin s := contour40EarlyMargin_pos s hs
  have hmargin_le : contour40EarlyMargin s ≤
      H s * H (s + 2) - H (s + 1) ^ 2 := by
    unfold contour40EarlyMargin
    nlinarith
  change 0 < H s * H (s + 2) - H (s + 1) ^ 2
  exact lt_of_lt_of_le hmargin hmargin_le

/-- The `C=40` tail is stronger than B1's `C=60` large-window premise. -/
theorem hankel2_pos_large_of_contour40_tail
    (a : Fin 10 → ℝ) (e : ℕ → ℝ) (s : ℕ)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i)
    (htail : ∀ n, |e n| ≤ 40 * eta ^ (n + 1))
    (hs : 4 ≤ s) :
    0 < hankel2 (fun n => tenModeMoment a n + e n) s := by
  have htail60 : ∀ n, |e n| ≤ 60 * eta ^ (n + 1) := by
    intro n
    calc
      |e n| ≤ 40 * eta ^ (n + 1) := htail n
      _ ≤ 60 * eta ^ (n + 1) := by
        have hpow : 0 ≤ eta ^ (n + 1) := pow_nonneg eta_pos.le _
        nlinarith
  exact hankel2_pos_large_of_ten_boxes_and_global_tail a e s hbox htail60 hs

/-- Conditional closure of the comparison Hankel minors from the `C=40` tail and six finite
signs. -/
theorem central_hankel2_pos_of_contour40_tail
    (H e : ℕ → ℝ) (a : Fin 10 → ℝ)
    (hdecomp : ∀ n, H n = tenModeMoment a n + e n)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i)
    (htail : ∀ n, |e n| ≤ 40 * eta ^ (n + 1))
    (hnonneg : ∀ n, n ≤ 5 → 0 ≤ e n) :
    ∀ s, 0 < hankel2 H s := by
  have hH : H = fun n => tenModeMoment a n + e n := funext hdecomp
  intro s
  rw [hH]
  by_cases hs : s < 4
  · exact hankel2_pos_small_of_contour40_tail a e s hbox htail hnonneg hs
  · have hslarge : 4 ≤ s := by omega
    exact hankel2_pos_large_of_contour40_tail a e s hbox htail hslarge

/-- Conditional closure for every original central `2×2` determinant. The hypotheses retain the
original jets, the ten comparison scales, the global contour tail, and all six finite signs. -/
theorem sigmaPadeD_pos_of_contour40_tail
    (a : Fin 10 → ℝ) (e : ℕ → ℝ)
    (hdecomp : ∀ n, completedSigmaLogJet 0 n = tenModeMoment a n + e n)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i)
    (htail : ∀ n, |e n| ≤ 40 * eta ^ (n + 1))
    (hnonneg : ∀ n, n ≤ 5 → 0 ≤ e n) :
    ∀ s, 0 < CarrySigmaPade.sigmaPadeD 0 s := by
  intro s
  have hpos := central_hankel2_pos_of_contour40_tail
    (H := completedSigmaLogJet 0) e a hdecomp hbox htail hnonneg s
  simpa [CarrySigmaPade.sigmaPadeD, CarrySigmaCentral.hankel2] using hpos

#print axioms contour40EarlyMargin_pos
#print axioms contour40_radius_conversion
#print axioms contour40_tail_of_circle_identity
#print axioms sigmaPadeD_pos_of_contour40_tail

end
end CarrySigmaCentral
