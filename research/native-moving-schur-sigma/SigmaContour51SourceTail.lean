import SigmaContour51FiniteContour
import SigmaContour51RationalGate
import Mathlib.Tactic

/-!
# Source-level C2 contour tail

This module composes the all-order contour identity for the original completed characteristic
with the conditional C=40 tail and the rational central Hankel gates. Only the circle bound and
the six initial residual signs remain as hypotheses.
-/

namespace CarrySigmaObstruction

open CarrySigmaCentral CarrySigmaSource Complex Set
open Metric
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

private theorem reciprocal_square_bounds {l t u : ℝ} (hl : 0 < l) (hlt : l < t)
    (htu : t < u) :
    1 / u ^ 2 ≤ (t ^ 2)⁻¹ ∧ (t ^ 2)⁻¹ ≤ 1 / l ^ 2 := by
  have ht : 0 < t := lt_trans hl hlt
  have hu : 0 < u := lt_trans ht htu
  have hltSq : l ^ 2 < t ^ 2 := by
    have hprod : 0 < (t - l) * (t + l) :=
      mul_pos (sub_pos.mpr hlt) (add_pos ht hl)
    nlinarith
  have htuSq : t ^ 2 < u ^ 2 := by
    have hprod : 0 < (u - t) * (u + t) :=
      mul_pos (sub_pos.mpr htu) (add_pos hu ht)
    nlinarith
  have hLower : 1 / u ^ 2 < 1 / t ^ 2 :=
    one_div_lt_one_div_of_lt (sq_pos_of_pos ht) htuSq
  have hUpper : 1 / t ^ 2 < 1 / l ^ 2 :=
    one_div_lt_one_div_of_lt (sq_pos_of_pos hl) hltSq
  exact ⟨le_of_lt (by simpa [one_div] using hLower),
    le_of_lt (by simpa [one_div] using hUpper)⟩

/-- The contour residual uses the same ten fixed heights as the all-order C2 contour theorem. -/
def completedNativeContour51Residual (ts : Fin 10 → ℝ) (n : ℕ) : ℝ :=
  completedSigmaLogJet 0 n -
    tenModeMoment (fun i => ((ts i) ^ 2)⁻¹) n

/-- The exact B2 height boxes imply the reciprocal-square scale boxes used by C6. -/
theorem contour51_scales_in_rational_boxes (ts : Fin 10 → ℝ)
    (hboxes : ∀ i : Fin 10,
      ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) :
    ∀ i : Fin 10,
      scaleLower i ≤ ((ts i) ^ 2)⁻¹ ∧ ((ts i) ^ 2)⁻¹ ≤ scaleUpper i := by
  intro i
  have hrecip := reciprocal_square_bounds (sigmaTenZeroLower_pos i)
    (hboxes i).1 (hboxes i).2
  have hUpper : CarrySigmaCentral.ordinateUpper = sigmaTenZeroBoxUpper := rfl
  have hLower : CarrySigmaCentral.ordinateLower = sigmaTenZeroBoxLower := rfl
  change 1 / (CarrySigmaCentral.ordinateUpper i) ^ 2 ≤ ((ts i) ^ 2)⁻¹ ∧
    ((ts i) ^ 2)⁻¹ ≤ 1 / (CarrySigmaCentral.ordinateLower i) ^ 2
  rw [hUpper, hLower]
  exact hrecip

/-- The fixed-root C2 identity supplies the exact decomposition of the original central jets into
the ten comparison modes and their contour residuals. -/
theorem completedNativeContour51_decomposition (ts : Fin 10 → ℝ) (n : ℕ) :
    completedSigmaLogJet 0 n =
      tenModeMoment (fun i => ((ts i) ^ 2)⁻¹) n +
        completedNativeContour51Residual ts n := by
  simp [completedNativeContour51Residual]

private theorem contour51_signed_modes_eq_tenModeMoment
    (ts : Fin 10 → ℝ) (n : ℕ) :
    (∑ i : Fin 10,
      (ts i : ℂ) ^ (-((2 * n + 2 : ℕ) : ℤ))) =
      (tenModeMoment (fun i => ((ts i) ^ 2)⁻¹) n : ℂ) := by
  let a : Fin 10 → ℝ := fun i => ((ts i) ^ 2)⁻¹
  have hmode (i : Fin 10) :
      (ts i : ℂ) ^ (-((2 * n + 2 : ℕ) : ℤ)) = (a i : ℂ) ^ (n + 1) := by
    have hexp : -((2 * n + 2 : ℕ) : ℤ) = (-2 : ℤ) * ((n + 1 : ℕ) : ℤ) := by
      omega
    rw [hexp, zpow_mul]
    have hneg : (ts i : ℂ) ^ (-2 : ℤ) = ((ts i : ℂ) ^ 2)⁻¹ := by
      rw [zpow_neg]
      rfl
    rw [hneg, zpow_natCast]
    simp [a]
  calc
    _ = ∑ i : Fin 10, (a i : ℂ) ^ (n + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hmode i
    _ = _ := by
      change (∑ i : Fin 10, (a i : ℂ) ^ (n + 1)) =
        ((∑ i : Fin 10, a i ^ (n + 1) : ℝ) : ℂ)
      simp

/-- The `s=0` gate needs only the signs of the outer residuals: the contour tail controls the
middle residual from below, while the exact scale boxes keep the middle moment positive. -/
theorem central_hankel2_zero_of_contour40_tail_and_outer_signs
    (a : Fin 10 → ℝ) (e : ℕ → ℝ)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i)
    (htail : ∀ n, |e n| ≤ 40 * CarrySigmaCentral.eta ^ (n + 1))
    (he0 : 0 ≤ e 0) (he2 : 0 ≤ e 2) :
    0 < hankel2 (fun n => tenModeMoment a n + e n) 0 := by
  let H : ℕ → ℝ := fun n => tenModeMoment a n + e n
  have ha : ∀ i, 0 < a i := tenScale_pos_of_box_bounds a hbox
  have hPlo0 : lowMoment 0 ≤ H 0 := by
    dsimp [H]
    exact (lowMoment_le_of_box_bounds a hbox 0).trans (le_add_of_nonneg_right he0)
  have hPlo2 : lowMoment 2 ≤ H 2 := by
    dsimp [H]
    exact (lowMoment_le_of_box_bounds a hbox 2).trans (le_add_of_nonneg_right he2)
  have htail1 := abs_le.mp (htail 1)
  have he1Lower : -(40 * CarrySigmaCentral.eta ^ 2) ≤ e 1 := by
    simpa using htail1.1
  have he1Upper : e 1 ≤ 40 * CarrySigmaCentral.eta ^ 2 := by
    simpa using htail1.2
  have hmidLower : lowMoment 1 - 40 * CarrySigmaCentral.eta ^ 2 ≤ H 1 := by
    dsimp [H]
    have hmode : lowMoment 1 ≤ tenModeMoment a 1 :=
      lowMoment_le_of_box_bounds a hbox 1
    linarith
  have hlowMid : 0 < lowMoment 1 - 40 * CarrySigmaCentral.eta ^ 2 := by
    norm_num [lowMoment, tenModeMoment, finitePowerMoment, CarrySigmaCentral.eta, scaleLower,
      scaleUpper, ordinateLower, ordinateUpper, Fin.sum_univ_succ]
  have hHmid : 0 ≤ H 1 := le_trans hlowMid.le hmidLower
  have hmidUpper : H 1 ≤ highMoment 1 + 40 * CarrySigmaCentral.eta ^ 2 := by
    dsimp [H]
    have hmode : tenModeMoment a 1 ≤ highMoment 1 :=
      tenModeMoment_le_highMoment_of_box_bounds a hbox 1
    linarith
  have hmidUpperPos : 0 ≤ highMoment 1 + 40 * CarrySigmaCentral.eta ^ 2 := by
    apply add_nonneg
    · unfold highMoment
      exact le_of_lt (tenModeMoment_pos scaleUpper 1
        (fun i => (scale_box_bounds i).2.2))
    · exact mul_nonneg (by norm_num) (pow_nonneg CarrySigmaCentral.eta_pos.le _)
  have hH0 : 0 ≤ H 0 := by
    dsimp [H]
    exact add_nonneg (le_of_lt (tenModeMoment_pos a 0 ha)) he0
  have hPlo0Pos : 0 < lowMoment 0 := by
    unfold lowMoment
    exact tenModeMoment_pos scaleLower 0 (fun i => (scale_box_bounds i).1)
  have hPlo2Pos : 0 < lowMoment 2 := by
    unfold lowMoment
    exact tenModeMoment_pos scaleLower 2 (fun i => (scale_box_bounds i).1)
  have hprod : lowMoment 0 * lowMoment 2 ≤ H 0 * H 2 :=
    mul_le_mul hPlo0 hPlo2 hPlo2Pos.le hH0
  have hsquare : H 1 ^ 2 ≤ (highMoment 1 + 40 * CarrySigmaCentral.eta ^ 2) ^ 2 :=
    (sq_le_sq₀ hHmid hmidUpperPos).2 hmidUpper
  have hmargin := contour40EarlyMargin_pos 0 (by norm_num)
  have hmarginLe : contour40EarlyMargin 0 ≤ H 0 * H 2 - H 1 ^ 2 := by
    change lowMoment 0 * lowMoment 2 -
        (highMoment 1 + 40 * CarrySigmaCentral.eta ^ 2) ^ 2 ≤
      H 0 * H 2 - H 1 ^ 2
    nlinarith [hprod, hsquare]
  change 0 < H 0 * H 2 - H 1 ^ 2
  exact lt_of_lt_of_le hmargin hmarginLe

/-- Conditional all-order closure for the original `sigmaPadeD`: the ten-mode decomposition and
scale boxes are discharged from the C2/C1 theorem. Only the C3 circle bound and six original-source
residual signs remain explicit. -/
theorem completedNative_sigmaPadeD_pos_of_contour51_bound
    (hR : ∀ z : ℂ, z ∈ sphere (0 : ℂ) 51 →
      ‖-deriv completedNativeCharacteristicContinuation z /
        ((2 : ℂ) * completedNativeCharacteristicContinuation z)‖ ≤ 4 / 5) :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧
      ((∀ n : ℕ, n ≤ 5 → 0 ≤ completedNativeContour51Residual ts n) →
        ∀ s : ℕ, 0 < CarrySigmaPade.sigmaPadeD 0 s) := by
  obtain ⟨ts, hmono, hbounds, hheightboxes, hforall⟩ :=
    completedNative_contour51_jet_residue_identity
  refine ⟨ts, hmono, hbounds, hheightboxes, ?_⟩
  intro hnonneg
  let a : Fin 10 → ℝ := fun i => ((ts i) ^ 2)⁻¹
  let e : ℕ → ℝ := completedNativeContour51Residual ts
  have hbox : ∀ i : Fin 10, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i :=
    contour51_scales_in_rational_boxes ts hheightboxes
  have hdecomp : ∀ n : ℕ,
      completedSigmaLogJet 0 n = tenModeMoment a n + e n := by
    intro n
    exact completedNativeContour51_decomposition ts n
  have htail : ∀ n : ℕ, |e n| ≤ 40 * CarrySigmaCentral.eta ^ (n + 1) := by
    intro n
    obtain ⟨G, hG, hcontour⟩ := hforall n
    have hsum := contour51_signed_modes_eq_tenModeMoment ts n
    have hidentity : (e n : ℂ) = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(0, 51),
          (-deriv completedNativeCharacteristicContinuation z /
            ((2 : ℂ) * completedNativeCharacteristicContinuation z)) /
              z ^ (2 * n + 2) := by
      rw [show e n = completedSigmaLogJet 0 n - tenModeMoment a n by
        rfl]
      push_cast
      rw [← hsum]
      exact hcontour.symm
    exact CarrySigmaCentral.contour40_tail_of_circle_identity
      (fun z => -deriv completedNativeCharacteristicContinuation z /
        ((2 : ℂ) * completedNativeCharacteristicContinuation z))
      (e n) n hR hidentity
  have hsigns : ∀ n : ℕ, n ≤ 5 → 0 ≤ e n := by
    intro n hn
    simpa [e] using hnonneg n hn
  exact CarrySigmaCentral.sigmaPadeD_pos_of_contour40_tail a e hdecomp hbox htail hsigns

/-- The first original central determinant is reduced to the circle bound and just the two outer
residual signs. In particular, the middle residual sign is not assumed; its absolute contour bound
keeps the middle moment positive. -/
theorem completedNative_sigmaPadeD_zero_pos_of_contour51_bound
    (hR : ∀ z : ℂ, z ∈ sphere (0 : ℂ) 51 →
      ‖-deriv completedNativeCharacteristicContinuation z /
        ((2 : ℂ) * completedNativeCharacteristicContinuation z)‖ ≤ 4 / 5) :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧
      ((0 ≤ completedNativeContour51Residual ts 0 ∧
        0 ≤ completedNativeContour51Residual ts 2) →
        0 < CarrySigmaPade.sigmaPadeD 0 0) := by
  obtain ⟨ts, hmono, hbounds, hheightboxes, hforall⟩ :=
    completedNative_contour51_jet_residue_identity
  refine ⟨ts, hmono, hbounds, hheightboxes, ?_⟩
  intro houter
  let a : Fin 10 → ℝ := fun i => ((ts i) ^ 2)⁻¹
  let e : ℕ → ℝ := completedNativeContour51Residual ts
  have hbox : ∀ i : Fin 10, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i :=
    contour51_scales_in_rational_boxes ts hheightboxes
  have htail : ∀ n : ℕ, |e n| ≤ 40 * CarrySigmaCentral.eta ^ (n + 1) := by
    intro n
    obtain ⟨G, hG, hcontour⟩ := hforall n
    have hsum := contour51_signed_modes_eq_tenModeMoment ts n
    have hidentity : (e n : ℂ) = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(0, 51),
          (-deriv completedNativeCharacteristicContinuation z /
            ((2 : ℂ) * completedNativeCharacteristicContinuation z)) /
              z ^ (2 * n + 2) := by
      rw [show e n = completedSigmaLogJet 0 n - tenModeMoment a n by rfl]
      push_cast
      rw [← hsum]
      exact hcontour.symm
    exact CarrySigmaCentral.contour40_tail_of_circle_identity
      (fun z => -deriv completedNativeCharacteristicContinuation z /
        ((2 : ℂ) * completedNativeCharacteristicContinuation z))
      (e n) n hR hidentity
  have hpos := central_hankel2_zero_of_contour40_tail_and_outer_signs
    a e hbox htail (by simpa [e] using houter.1) (by simpa [e] using houter.2)
  have hdecomp (n : ℕ) :
      completedSigmaLogJet 0 n = tenModeMoment a n + e n := by
    exact completedNativeContour51_decomposition ts n
  have hposJet : 0 < hankel2 (completedSigmaLogJet 0) 0 := by
    change 0 < completedSigmaLogJet 0 0 * completedSigmaLogJet 0 2 -
      (completedSigmaLogJet 0 1) ^ 2
    rw [hdecomp 0, hdecomp 2, hdecomp 1]
    exact hpos
  simpa [CarrySigmaPade.sigmaPadeD, CarrySigmaCentral.hankel2] using hposJet

#print axioms contour51_scales_in_rational_boxes
#print axioms completedNativeContour51_decomposition
#print axioms completedNative_sigmaPadeD_pos_of_contour51_bound
#print axioms central_hankel2_zero_of_contour40_tail_and_outer_signs
#print axioms completedNative_sigmaPadeD_zero_pos_of_contour51_bound

end
end CarrySigmaObstruction
