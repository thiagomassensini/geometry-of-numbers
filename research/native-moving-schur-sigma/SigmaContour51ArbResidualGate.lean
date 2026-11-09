import SigmaContour51SourceTail
import Mathlib.Tactic

/-!
# Lean adapter for the external Arb contour residual intervals

The accompanying 4096-arc Arb computation reports exact rational lower endpoints for the six
real parts of the normalized radius-51 Cauchy integrals. This module records those rational
endpoints and checks their simplified positive margins with Lean. The analytic inclusion of the
actual contour integrals in the Arb intervals is deliberately left as an explicit hypothesis;
the Arb computation has not yet been re-proved or imported as a Lean certificate.
-/

namespace CarrySigmaObstruction

open CarrySigmaCentral CarrySigmaSource Complex Set Metric
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The exact rational lower endpoints exported by the 4096-arc Arb residual certificate. -/
def contour51ArbRecordedResidualLower (n : ℕ) : ℚ :=
  if n = 0 then
    476792647355532758597273668614120507304465614510349 /
      50000000000000000000000000000000000000000000000000000
  else if n = 1 then
    367211841451181436632674095648190011100874075559569 /
      400000000000000000000000000000000000000000000000000000000
  else if n = 2 then
    23427536379992679585592246130438740913078394531619 /
      125000000000000000000000000000000000000000000000000000000000
  else if n = 3 then
    4542210478952835984180926208242685384833798801106539 /
      100000000000000000000000000000000000000000000000000000000000000000
  else if n = 4 then
    150739032571328976341694537115561602246710923023003 /
      12500000000000000000000000000000000000000000000000000000000000000000
  else
    559465369611797131690619084006358952596865833187001 /
      200000000000000000000000000000000000000000000000000000000000000000000000

/-- The exact rational upper endpoints exported by the 4096-arc Arb certificate. -/
def contour51ArbRecordedResidualUpper (n : ℕ) : ℚ :=
  if n = 0 then
    479281656543444264757436057892532372538840614510351 /
      50000000000000000000000000000000000000000000000000000
  else if n = 1 then
    9510079786587546241896818425944959856989625326489229 /
      10000000000000000000000000000000000000000000000000000000000
  else if n = 2 then
    1040749134831417582196926492902375220815547585463981 /
      5000000000000000000000000000000000000000000000000000000000000
  else if n = 3 then
    573630961901435851092136299750365383799731271486109 /
      10000000000000000000000000000000000000000000000000000000000000000
  else if n = 4 then
    1733697815335599238443830730105263254964457051502119 /
      100000000000000000000000000000000000000000000000000000000000000000000
  else
    243651791387510144344296366203733485830856847008057 /
      40000000000000000000000000000000000000000000000000000000000000000000000

/-- Coarse rational margins below the exact Arb lower endpoints, one for each `e_0,...,e_5`. -/
def contour51ArbResidualMargin (n : ℕ) : ℚ :=
  if n = 0 then 9 / 1000
  else if n = 1 then 9 / 10000000
  else if n = 2 then 9 / 50000000000
  else if n = 3 then 1 / 25000000000000
  else if n = 4 then 1 / 100000000000000000
  else 1 / 500000000000000000000

/-- Coarse rational upper bounds, useful for retaining both signs of each interval. -/
def contour51ArbResidualUpperMargin (n : ℕ) : ℚ :=
  if n = 0 then 1 / 100
  else if n = 1 then 1 / 1000000
  else if n = 2 then 1 / 4000000000
  else if n = 3 then 1 / 10000000000000
  else if n = 4 then 1 / 50000000000000000
  else 1 / 100000000000000000000

/-- Conservative first-window determinant lower bound using all three Arb residual intervals. -/
def contour51ArbZeroDetMargin : ℝ :=
  (lowMoment 0 + (contour51ArbResidualMargin 0 : ℝ)) *
      (lowMoment 2 + (contour51ArbResidualMargin 2 : ℝ)) -
    (highMoment 1 + (contour51ArbResidualUpperMargin 1 : ℝ)) ^ 2

theorem contour51ArbResidualMargin_pos_and_below_recorded (n : ℕ) (hn : n ≤ 5) :
    0 < contour51ArbResidualMargin n ∧
      contour51ArbResidualMargin n < contour51ArbRecordedResidualLower n := by
  interval_cases n <;>
    norm_num [contour51ArbResidualMargin, contour51ArbRecordedResidualLower]

theorem contour51ArbResidualUpperMargin_above_recorded (n : ℕ) (hn : n ≤ 5) :
    contour51ArbRecordedResidualUpper n < contour51ArbResidualUpperMargin n := by
  interval_cases n <;>
    norm_num [contour51ArbResidualUpperMargin, contour51ArbRecordedResidualUpper]

theorem contour51ArbZeroDetMargin_pos : 0 < contour51ArbZeroDetMargin := by
  norm_num [contour51ArbZeroDetMargin, contour51ArbResidualMargin,
    contour51ArbResidualUpperMargin, lowMoment, highMoment, tenModeMoment,
    finitePowerMoment, CarrySigmaCentral.scaleLower, CarrySigmaCentral.scaleUpper,
    CarrySigmaCentral.ordinateLower, CarrySigmaCentral.ordinateUpper,
    Fin.sum_univ_succ]

/-- The conservative first-window determinant margin exceeds one billionth in the original
determinant scale. -/
theorem contour51ArbZeroDetMargin_gt_rational :
    1 / 1000000000 < contour51ArbZeroDetMargin := by
  norm_num [contour51ArbZeroDetMargin, contour51ArbResidualMargin,
    contour51ArbResidualUpperMargin, lowMoment, highMoment, tenModeMoment,
    finitePowerMoment, CarrySigmaCentral.scaleLower, CarrySigmaCentral.scaleUpper,
    CarrySigmaCentral.ordinateLower, CarrySigmaCentral.ordinateUpper,
    Fin.sum_univ_succ]

/-- The normalized original-source contour integral whose real part is the C2 residual `e_n`. -/
def contour51OriginalResidualIntegral (n : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ z in C(0, 51),
      (-deriv completedNativeCharacteristicContinuation z /
        ((2 : ℂ) * completedNativeCharacteristicContinuation z)) /
          z ^ (2 * n + 2)

/-- Exact rational lower enclosures from Arb, phrased as a Lean proposition for reviewable
composition. Its proof from the arc data remains the outstanding certificate-to-Lean bridge. -/
def contour51ArbResidualIntervalBounds : Prop :=
  ∀ n : ℕ, n ≤ 5 →
    (contour51ArbRecordedResidualLower n : ℝ) ≤
        (contour51OriginalResidualIntegral n).re ∧
      (contour51OriginalResidualIntegral n).re ≤
        (contour51ArbRecordedResidualUpper n : ℝ)

/-- The first determinant only needs the residual intervals for orders zero through two. -/
def contour51ArbFirstThreeResidualIntervalBounds : Prop :=
  ∀ n : ℕ, n ≤ 2 →
    (contour51ArbRecordedResidualLower n : ℝ) ≤
        (contour51OriginalResidualIntegral n).re ∧
      (contour51OriginalResidualIntegral n).re ≤
        (contour51ArbRecordedResidualUpper n : ℝ)

private theorem contour51SignedModes_eq_tenModeMoment (ts : Fin 10 → ℝ) (n : ℕ) :
    (∑ i : Fin 10,
      (ts i : ℂ) ^ (-((2 * n + 2 : ℕ) : ℤ))) =
      (tenModeMoment (fun i => ((ts i) ^ 2)⁻¹) n : ℂ) := by
  let a : Fin 10 → ℝ := fun i => ((ts i) ^ 2)⁻¹
  have hmode (i : Fin 10) :
      (ts i : ℂ) ^ (-((2 * n + 2 : ℕ) : ℤ)) = (a i : ℂ) ^ (n + 1) := by
    have hexp : -((2 * n + 2 : ℕ) : ℤ) = (-2 : ℤ) * ((n + 1 : ℕ) : ℤ) := by omega
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

private theorem contour51Residual_eq_real_integral_of_c2
    (ts : Fin 10 → ℝ) (n : ℕ)
    (hforall : ∀ n : ℕ,
      ∃ G : ℂ → ℂ, DiffContOnCl ℂ G (Metric.ball (0 : ℂ) 51) ∧
        contour51OriginalResidualIntegral n =
          (completedSigmaLogJet 0 n : ℂ) -
            ∑ i : Fin 10, (ts i : ℂ) ^ (-((2 * n + 2 : ℕ) : ℤ))) :
    contour51OriginalResidualIntegral n =
      (completedNativeContour51Residual ts n : ℂ) := by
  obtain ⟨G, hG, hcontour⟩ := hforall n
  have hsum := contour51SignedModes_eq_tenModeMoment ts n
  have hidentity : (completedNativeContour51Residual ts n : ℂ) =
      contour51OriginalResidualIntegral n := by
    rw [show completedNativeContour51Residual ts n =
      completedSigmaLogJet 0 n - tenModeMoment (fun i => ((ts i) ^ 2)⁻¹) n by rfl]
    push_cast
    rw [← hsum]
    exact hcontour.symm
  exact hidentity.symm

/-- For the one fixed C1 root list, the exact C2 residue theorem transports lower bounds on the
real parts of the contour integrals to the original ten-mode residuals. -/
theorem completedNativeContour51Residual_pos_of_arb_intervals
    (hArb : contour51ArbResidualIntervalBounds) :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧
      (∀ n : ℕ, n ≤ 5 →
        (contour51ArbResidualMargin n : ℝ) < completedNativeContour51Residual ts n) := by
  obtain ⟨ts, hmono, hbounds, hboxes, hforall⟩ :=
    completedNative_contour51_jet_residue_identity
  refine ⟨ts, hmono, hbounds, hboxes, ?_⟩
  intro n hn
  have hmargin := contour51ArbResidualMargin_pos_and_below_recorded n hn
  have hmarginReal : (contour51ArbResidualMargin n : ℝ) <
      (contour51ArbRecordedResidualLower n : ℝ) := by exact_mod_cast hmargin.2
  have hlow := (hArb n hn).1
  rw [contour51Residual_eq_real_integral_of_c2 ts n hforall] at hlow
  exact lt_of_lt_of_le hmarginReal (by simpa using hlow)

theorem completedNativeContour51Residuals_nonneg_of_arb_intervals
    (hArb : contour51ArbResidualIntervalBounds) :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧
      (∀ n : ℕ, n ≤ 5 → 0 ≤ completedNativeContour51Residual ts n) := by
  obtain ⟨ts, hmono, hbounds, hboxes, hpos⟩ :=
    completedNativeContour51Residual_pos_of_arb_intervals hArb
  refine ⟨ts, hmono, hbounds, hboxes, ?_⟩
  intro n hn
  have hmarginPosReal : (0 : ℝ) < (contour51ArbResidualMargin n : ℝ) := by
    exact_mod_cast (contour51ArbResidualMargin_pos_and_below_recorded n hn).1
  exact le_of_lt (lt_trans hmarginPosReal (hpos n hn))

/-- The first central determinant can be closed from the original-source Arb intervals for only
`e_0,e_1,e_2`; no global contour-tail hypothesis is needed. The interval gate preserves all five
terms in `D(H)-D(P)` through its lower product and upper square bounds. -/
theorem completedNative_sigmaPadeD_zero_pos_of_contour51_arb_intervals
    (hArb : contour51ArbFirstThreeResidualIntervalBounds) :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧
      1 / 1000000000 < CarrySigmaPade.sigmaPadeD 0 0 := by
  obtain ⟨ts, hmono, hbounds, hheightboxes, hforall⟩ :=
    completedNative_contour51_jet_residue_identity
  refine ⟨ts, hmono, hbounds, hheightboxes, ?_⟩
  let a : Fin 10 → ℝ := fun i => ((ts i) ^ 2)⁻¹
  let e : ℕ → ℝ := completedNativeContour51Residual ts
  let H : ℕ → ℝ := fun n => tenModeMoment a n + e n
  have hbox : ∀ i : Fin 10, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i :=
    contour51_scales_in_rational_boxes ts hheightboxes
  have hdecomp : ∀ n : ℕ,
      completedSigmaLogJet 0 n = tenModeMoment a n + e n := by
    intro n
    exact completedNativeContour51_decomposition ts n
  have hE0 : (contour51ArbResidualMargin 0 : ℝ) ≤ e 0 := by
    have hmargin := contour51ArbResidualMargin_pos_and_below_recorded 0 (by norm_num)
    have hmarginReal : (contour51ArbResidualMargin 0 : ℝ) <
        (contour51ArbRecordedResidualLower 0 : ℝ) := by exact_mod_cast hmargin.2
    have hlow := (hArb 0 (by norm_num)).1
    rw [contour51Residual_eq_real_integral_of_c2 ts 0 hforall] at hlow
    exact le_of_lt (lt_of_lt_of_le hmarginReal (by simpa [e] using hlow))
  have hE2 : (contour51ArbResidualMargin 2 : ℝ) ≤ e 2 := by
    have hmargin := contour51ArbResidualMargin_pos_and_below_recorded 2 (by norm_num)
    have hmarginReal : (contour51ArbResidualMargin 2 : ℝ) <
        (contour51ArbRecordedResidualLower 2 : ℝ) := by exact_mod_cast hmargin.2
    have hlow := (hArb 2 (by norm_num)).1
    rw [contour51Residual_eq_real_integral_of_c2 ts 2 hforall] at hlow
    exact le_of_lt (lt_of_lt_of_le hmarginReal (by simpa [e] using hlow))
  have hE1 : (contour51ArbResidualMargin 1 : ℝ) ≤ e 1 := by
    have hmargin := contour51ArbResidualMargin_pos_and_below_recorded 1 (by norm_num)
    have hmarginReal : (contour51ArbResidualMargin 1 : ℝ) <
        (contour51ArbRecordedResidualLower 1 : ℝ) := by exact_mod_cast hmargin.2
    have hlow := (hArb 1 (by norm_num)).1
    rw [contour51Residual_eq_real_integral_of_c2 ts 1 hforall] at hlow
    exact le_of_lt (lt_of_lt_of_le hmarginReal (by simpa [e] using hlow))
  have hE1upper : e 1 ≤ (contour51ArbResidualUpperMargin 1 : ℝ) := by
    have hmargin := contour51ArbResidualUpperMargin_above_recorded 1 (by norm_num)
    have hmarginReal : (contour51ArbRecordedResidualUpper 1 : ℝ) <
        (contour51ArbResidualUpperMargin 1 : ℝ) := by exact_mod_cast hmargin
    have hupp := (hArb 1 (by norm_num)).2
    rw [contour51Residual_eq_real_integral_of_c2 ts 1 hforall] at hupp
    exact le_trans (by simpa [e] using hupp) (le_of_lt hmarginReal)
  have h0lower : lowMoment 0 + (contour51ArbResidualMargin 0 : ℝ) ≤ H 0 := by
    dsimp [H]
    have hmode := lowMoment_le_of_box_bounds a hbox 0
    linarith
  have h2lower : lowMoment 2 + (contour51ArbResidualMargin 2 : ℝ) ≤ H 2 := by
    dsimp [H]
    have hmode := lowMoment_le_of_box_bounds a hbox 2
    linarith
  have h1upper : H 1 ≤ highMoment 1 + (contour51ArbResidualUpperMargin 1 : ℝ) := by
    dsimp [H]
    have hmode := tenModeMoment_le_highMoment_of_box_bounds a hbox 1
    linarith
  have hlow0pos : 0 < lowMoment 0 + (contour51ArbResidualMargin 0 : ℝ) := by
    have hlow : 0 < lowMoment 0 := by
      unfold lowMoment
      exact tenModeMoment_pos scaleLower 0 (fun i => (scale_box_bounds i).1)
    have hmargin := (contour51ArbResidualMargin_pos_and_below_recorded 0 (by norm_num)).1
    exact add_pos hlow (by exact_mod_cast hmargin)
  have hlow2pos : 0 < lowMoment 2 + (contour51ArbResidualMargin 2 : ℝ) := by
    have hlow : 0 < lowMoment 2 := by
      unfold lowMoment
      exact tenModeMoment_pos scaleLower 2 (fun i => (scale_box_bounds i).1)
    have hmargin := (contour51ArbResidualMargin_pos_and_below_recorded 2 (by norm_num)).1
    exact add_pos hlow (by exact_mod_cast hmargin)
  have hH0pos : 0 < H 0 := lt_of_lt_of_le hlow0pos h0lower
  have hH1nonneg : 0 ≤ H 1 := by
    dsimp [H]
    have ha := tenScale_pos_of_box_bounds a hbox
    have hmode := tenModeMoment_pos a 1 ha
    have hmarginPos : 0 < (contour51ArbResidualMargin 1 : ℝ) := by
      exact_mod_cast (contour51ArbResidualMargin_pos_and_below_recorded 1 (by norm_num)).1
    exact add_nonneg hmode.le (le_trans hmarginPos.le hE1)
  have huppernonneg : 0 ≤ highMoment 1 + (contour51ArbResidualUpperMargin 1 : ℝ) := by
    apply add_nonneg
    · unfold highMoment
      exact le_of_lt (tenModeMoment_pos scaleUpper 1 (fun i => (scale_box_bounds i).2.2))
    · exact le_of_lt (by
        exact_mod_cast (by norm_num [contour51ArbResidualUpperMargin] :
          0 < contour51ArbResidualUpperMargin 1))
  have hprod :
      (lowMoment 0 + (contour51ArbResidualMargin 0 : ℝ)) *
        (lowMoment 2 + (contour51ArbResidualMargin 2 : ℝ)) ≤ H 0 * H 2 :=
    mul_le_mul h0lower h2lower hlow2pos.le hH0pos.le
  have hsquare : H 1 ^ 2 ≤
      (highMoment 1 + (contour51ArbResidualUpperMargin 1 : ℝ)) ^ 2 :=
    (sq_le_sq₀ hH1nonneg huppernonneg).2 h1upper
  have hmarginle : contour51ArbZeroDetMargin ≤ H 0 * H 2 - H 1 ^ 2 := by
    unfold contour51ArbZeroDetMargin
    nlinarith
  have hdet : 1 / 1000000000 < H 0 * H 2 - H 1 ^ 2 :=
    lt_of_lt_of_le contour51ArbZeroDetMargin_gt_rational hmarginle
  have hH : H = completedSigmaLogJet 0 := funext (fun n => (hdecomp n).symm)
  rw [hH] at hdet
  simpa [CarrySigmaPade.sigmaPadeD, CarrySigmaCentral.hankel2] using hdet

/-- Conditional all-window closure after the external Arb interval inclusions have been proved in
Lean. The circle norm bound remains an independent explicit premise; this theorem does not claim
unconditional positivity. -/
theorem completedNative_sigmaPadeD_pos_of_contour51_arb_intervals
    (hR : ∀ z : ℂ, z ∈ sphere (0 : ℂ) 51 →
      ‖-deriv completedNativeCharacteristicContinuation z /
        ((2 : ℂ) * completedNativeCharacteristicContinuation z)‖ ≤ 4 / 5)
    (hArb : contour51ArbResidualIntervalBounds) :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧
      ∀ s : ℕ, 0 < CarrySigmaPade.sigmaPadeD 0 s := by
  obtain ⟨ts, hmono, hbounds, hheightboxes, hforall⟩ :=
    completedNative_contour51_jet_residue_identity
  refine ⟨ts, hmono, hbounds, hheightboxes, ?_⟩
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
    have hsum := contour51SignedModes_eq_tenModeMoment ts n
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
  have hsigns : ∀ n : ℕ, n ≤ 5 → 0 ≤ e n := by
    intro n hn
    have hmargin := contour51ArbResidualMargin_pos_and_below_recorded n hn
    have hmarginReal : (contour51ArbResidualMargin n : ℝ) <
        (contour51ArbRecordedResidualLower n : ℝ) := by exact_mod_cast hmargin.2
    have hlow := (hArb n hn).1
    rw [contour51Residual_eq_real_integral_of_c2 ts n hforall] at hlow
    have hpos : (contour51ArbResidualMargin n : ℝ) < e n :=
      lt_of_lt_of_le hmarginReal (by simpa [e] using hlow)
    have hmarginPos : (0 : ℝ) < (contour51ArbResidualMargin n : ℝ) := by
      exact_mod_cast hmargin.1
    exact le_of_lt (lt_trans hmarginPos hpos)
  exact CarrySigmaCentral.sigmaPadeD_pos_of_contour40_tail a e hdecomp hbox htail hsigns

#print axioms contour51ArbResidualMargin_pos_and_below_recorded
#print axioms contour51ArbResidualUpperMargin_above_recorded
#print axioms contour51ArbZeroDetMargin_pos
#print axioms contour51ArbZeroDetMargin_gt_rational
#print axioms completedNativeContour51Residual_pos_of_arb_intervals
#print axioms completedNativeContour51Residuals_nonneg_of_arb_intervals
#print axioms completedNative_sigmaPadeD_zero_pos_of_contour51_arb_intervals
#print axioms completedNative_sigmaPadeD_pos_of_contour51_arb_intervals

end
end CarrySigmaObstruction
