import SigmaCentralTenModeAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Exact rational data for the ten-mode central C2 comparison

All values in this file are rational definitions interpreted in `ℝ`.  The boxes describe the ten
certified positive ordinates; they do not define the original moment sequence.
-/

namespace CarrySigmaCentral

open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 3000000

def ordinateLower : Fin 10 → ℝ :=
  ![1413 / 100, 2102 / 100, 2501 / 100, 3042 / 100, 3293 / 100,
    3758 / 100, 4091 / 100, 4332 / 100, 4800 / 100, 4977 / 100]

def ordinateUpper : Fin 10 → ℝ :=
  ![1414 / 100, 2103 / 100, 2502 / 100, 3043 / 100, 3294 / 100,
    3759 / 100, 4092 / 100, 4333 / 100, 4801 / 100, 4978 / 100]

/-- Lower and upper endpoints for `aᵢ = γᵢ⁻²`, with the order reversed. -/
def scaleLower (i : Fin 10) : ℝ := 1 / (ordinateUpper i) ^ 2
def scaleUpper (i : Fin 10) : ℝ := 1 / (ordinateLower i) ^ 2

def eta : ℝ := 1 / 2500
def scaleAUpper : ℝ := 1 / (1413 / 100 : ℝ) ^ 2
def scaleAMin : ℝ := 1 / (1414 / 100 : ℝ) ^ 2
def scaleBMin : ℝ := 1 / (2103 / 100 : ℝ) ^ 2
def scaleBMax : ℝ := 1 / (2102 / 100 : ℝ) ^ 2
def scaleGap : ℝ := scaleAMin - scaleBMax

/-- The refined Lehman tail majorant `T_n`, written with positive natural powers and rational
reciprocals so every fixed-index comparison reduces to exact rational arithmetic. -/
def refinedTail (n : ℕ) : ℝ :=
  let p : ℝ := (2 * (n + 1) : ℕ)
  let q : ℝ := (50 : ℝ) ^ (2 * (n + 1))
  (25 / 157) * (50 / q) * (4 / (p - 1) + 1 / (p - 1) ^ 2) +
    (16 + 2 / p) / q

def lowMoment (n : ℕ) : ℝ := tenModeMoment scaleLower n
def highMoment (n : ℕ) : ℝ := tenModeMoment scaleUpper n

def earlyMargin (s : ℕ) : ℝ :=
  lowMoment s * lowMoment (s + 2) - (highMoment (s + 1) + refinedTail (s + 1)) ^ 2

def alpha : ℝ := 600 * (scaleAUpper + eta) ^ 2 / scaleGap ^ 2
def beta : ℝ := 7200 * eta ^ 2 / scaleGap ^ 2
def rho : ℝ := scaleAUpper * eta / (scaleAMin * scaleBMin)
def rhoTwo : ℝ := eta ^ 2 / (scaleAMin * scaleBMin)
def mainLower (s : ℕ) : ℝ :=
  (scaleAMin * scaleBMin) ^ (s + 1) * scaleGap ^ 2

def determinantErrorBound (s : ℕ) : ℝ :=
  600 * (scaleAUpper * eta) ^ (s + 1) * (scaleAUpper + eta) ^ 2 +
    7200 * eta ^ (2 * s + 4)

theorem ordinate_boxes_ordered : ∀ i : Fin 10,
    0 < ordinateLower i ∧ ordinateLower i < ordinateUpper i ∧ ordinateUpper i < 50 := by
  intro i
  fin_cases i <;> norm_num [ordinateLower, ordinateUpper]

theorem scale_box_bounds (i : Fin 10) :
    0 < scaleLower i ∧ scaleLower i < scaleUpper i ∧ 0 < scaleUpper i := by
  fin_cases i <;> norm_num [scaleLower, scaleUpper, ordinateLower, ordinateUpper]

theorem scale_gap_pos : 0 < scaleGap := by
  norm_num [scaleGap, scaleAMin, scaleBMax]

theorem scale_upper_le_A (i : Fin 10) : scaleUpper i ≤ scaleAUpper := by
  fin_cases i <;> norm_num [scaleUpper, scaleAUpper, ordinateLower]

theorem scale_lower_zero_eq_Amin : scaleLower 0 = scaleAMin := by
  norm_num [scaleLower, scaleAMin, ordinateUpper]

theorem scale_lower_one_eq_Bmin : scaleLower 1 = scaleBMin := by
  norm_num [scaleLower, scaleBMin, ordinateUpper]

theorem scale_upper_one_eq_Bmax : scaleUpper 1 = scaleBMax := by
  norm_num [scaleUpper, scaleBMax, ordinateLower]

theorem eta_pos : 0 < eta := by norm_num [eta]

theorem eta_lt_one : eta < 1 := by norm_num [eta]

theorem refinedTail_pos (n : ℕ) : 0 < refinedTail n := by
  have hpNat : 1 < 2 * (n + 1) := by omega
  let p : ℝ := (2 * (n + 1) : ℕ)
  let q : ℝ := (50 : ℝ) ^ (2 * (n + 1))
  have hp : 1 < p := by
    dsimp [p]
    exact_mod_cast hpNat
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 0 < q := by positivity
  have hpden : 0 < p - 1 := by linarith
  change 0 < (25 / 157) * (50 / q) * (4 / (p - 1) + 1 / (p - 1) ^ 2) +
    (16 + 2 / p) / q
  positivity

theorem tenScale_pos_of_box_bounds (a : Fin 10 → ℝ)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i) :
    ∀ i, 0 < a i := by
  intro i
  exact lt_of_lt_of_le (scale_box_bounds i).1 (hbox i).1

theorem lowMoment_le_of_box_bounds (a : Fin 10 → ℝ)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i) (n : ℕ) :
    lowMoment n ≤ tenModeMoment a n := by
  unfold lowMoment
  apply tenModeMoment_mono
  · intro i
    exact (scale_box_bounds i).1.le
  · exact fun i => (hbox i).1

theorem tenModeMoment_le_highMoment_of_box_bounds (a : Fin 10 → ℝ)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i) (n : ℕ) :
    tenModeMoment a n ≤ highMoment n := by
  unfold highMoment
  apply tenModeMoment_mono
  · intro i
    exact (tenScale_pos_of_box_bounds a hbox i).le
  · exact fun i => (hbox i).2

theorem mainLower_le_tenMode_hankel2 (a : Fin 10 → ℝ) (s : ℕ)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i) :
    mainLower s ≤ hankel2 (tenModeMoment a) s := by
  have ha : ∀ i, 0 ≤ a i := fun i => (tenScale_pos_of_box_bounds a hbox i).le
  have hAlo : scaleAMin ≤ a 0 := by
    rw [← scale_lower_zero_eq_Amin]
    exact (hbox 0).1
  have hBlo : scaleBMin ≤ a 1 := by
    rw [← scale_lower_one_eq_Bmin]
    exact (hbox 1).1
  have hBhi : a 1 ≤ scaleBMax := by
    rw [← scale_upper_one_eq_Bmax]
    exact (hbox 1).2
  have hAminPos : 0 < scaleAMin := by norm_num [scaleAMin]
  have hBminPos : 0 < scaleBMin := by norm_num [scaleBMin]
  have ha0Pos : 0 < a 0 := lt_of_lt_of_le hAminPos hAlo
  have hgap : scaleGap ≤ a 0 - a 1 := by
    dsimp [scaleGap]
    linarith
  have hscales : scaleAMin * scaleBMin ≤ a 0 * a 1 :=
    mul_le_mul hAlo hBlo hBminPos.le ha0Pos.le
  have hpower : (scaleAMin * scaleBMin) ^ (s + 1) ≤
      (a 0 * a 1) ^ (s + 1) :=
    pow_le_pow_left₀ (by positivity) hscales _
  have hdiff_nonneg : 0 ≤ a 0 - a 1 := le_trans scale_gap_pos.le hgap
  have hsquare : scaleGap ^ 2 ≤ (a 0 - a 1) ^ 2 :=
    (sq_le_sq₀ scale_gap_pos.le hdiff_nonneg).2 hgap
  have hterm : mainLower s ≤ pairTerm (a 0) (a 1) s := by
    unfold mainLower pairTerm
    exact mul_le_mul hpower hsquare (sq_nonneg _)
      (pow_nonneg (mul_nonneg (ha 0) (ha 1)) _)
  have hterm_nonneg : ∀ i j, 0 ≤ pairTerm (a i) (a j) s := by
    intro i j
    unfold pairTerm
    exact mul_nonneg (pow_nonneg (mul_nonneg (ha i) (ha j)) _)
      (sq_nonneg (a i - a j))
  have hpair := pairTerm_01_le_pairMoment a s hterm_nonneg
  rw [tenModeMoment_hankel2_eq_pairMoment]
  exact hterm.trans hpair

theorem rho_bounds : 0 < rhoTwo ∧ rhoTwo < rho ∧ rho < 1 := by
  norm_num [rhoTwo, rho, eta, scaleAUpper, scaleAMin, scaleBMin]

theorem ratio_at_four_lt_one : alpha * rho ^ 5 + beta * rhoTwo ^ 5 < 1 := by
  norm_num [alpha, beta, rho, rhoTwo, eta, scaleAUpper, scaleAMin, scaleBMin, scaleGap,
    scaleBMax]

theorem alpha_nonneg : 0 ≤ alpha := by
  have hg := scale_gap_pos
  unfold alpha
  positivity

theorem beta_nonneg : 0 ≤ beta := by
  have hg := scale_gap_pos
  unfold beta
  positivity

theorem ratio_lt_one_of_four_le (s : ℕ) (hs : 4 ≤ s) :
    alpha * rho ^ (s + 1) + beta * rhoTwo ^ (s + 1) < 1 := by
  have hb := rho_bounds
  have hrho0 : 0 ≤ rho := le_of_lt (lt_trans hb.1 hb.2.1)
  have hrho1 : rho ≤ 1 := le_of_lt hb.2.2
  have hrhoTwo0 : 0 ≤ rhoTwo := le_of_lt hb.1
  have hrhoTwo1 : rhoTwo ≤ 1 := by linarith [hb.1, hb.2.1, hb.2.2]
  have hexp : 5 ≤ s + 1 := by omega
  have hp1 := pow_le_pow_of_le_one hrho0 hrho1 hexp
  have hp2 := pow_le_pow_of_le_one hrhoTwo0 hrhoTwo1 hexp
  calc
    alpha * rho ^ (s + 1) + beta * rhoTwo ^ (s + 1) ≤
        alpha * rho ^ 5 + beta * rhoTwo ^ 5 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp1 alpha_nonneg)
        (mul_le_mul_of_nonneg_left hp2 beta_nonneg)
    _ < 1 := ratio_at_four_lt_one

theorem determinantErrorBound_eq_main_times_ratio (s : ℕ) :
    determinantErrorBound s =
      mainLower s * (alpha * rho ^ (s + 1) + beta * rhoTwo ^ (s + 1)) := by
  have hg : scaleGap ≠ 0 := (scale_gap_pos).ne'
  have hden : scaleAMin * scaleBMin ≠ 0 := by
    apply ne_of_gt
    norm_num [scaleAMin, scaleBMin]
  unfold determinantErrorBound mainLower alpha beta rho rhoTwo
  rw [div_pow, div_pow]
  field_simp [hg, hden]
  rw [show 2 * s + 4 = 2 + 2 * (s + 1) by omega, pow_add]
  ring

theorem mainLower_pos (s : ℕ) : 0 < mainLower s := by
  have ha : 0 < scaleAMin := by norm_num [scaleAMin]
  have hb : 0 < scaleBMin := by norm_num [scaleBMin]
  have hg := scale_gap_pos
  unfold mainLower
  exact mul_pos (pow_pos (mul_pos ha hb) _) (sq_pos_of_pos hg)

theorem early_margin_pos (s : ℕ) (hs : s < 4) : 0 < earlyMargin s := by
  interval_cases s <;>
    norm_num [earlyMargin, lowMoment, highMoment, tenModeMoment, finitePowerMoment, refinedTail,
      eta, scaleLower, scaleUpper, ordinateLower, ordinateUpper, Fin.sum_univ_succ]

/-- The refined Lehman estimate handles the four shallow central windows. The full global tail
bound alone is deliberately not used for `s=0`. -/
theorem hankel2_pos_small_of_ten_boxes_and_tail
    (a : Fin 10 → ℝ) (e : ℕ → ℝ) (s : ℕ)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i)
    (hnonneg : ∀ n, n ≤ 5 → 0 ≤ e n)
    (htail : ∀ n, 1 ≤ n → n ≤ 4 → e n ≤ refinedTail n)
    (hs : s < 4) :
    0 < hankel2 (fun n => tenModeMoment a n + e n) s := by
  let H : ℕ → ℝ := fun n => tenModeMoment a n + e n
  have ha : ∀ i, 0 < a i := tenScale_pos_of_box_bounds a hbox
  have he0 : 0 ≤ e s := hnonneg s (by omega)
  have he2 : 0 ≤ e (s + 2) := hnonneg (s + 2) (by omega)
  have he1 : 0 ≤ e (s + 1) := hnonneg (s + 1) (by omega)
  have hLpos : 0 < lowMoment s := by
    unfold lowMoment
    exact tenModeMoment_pos scaleLower s (fun i => (scale_box_bounds i).1)
  have hRpos : 0 < lowMoment (s + 2) := by
    unfold lowMoment
    exact tenModeMoment_pos scaleLower (s + 2) (fun i => (scale_box_bounds i).1)
  have hPlo : lowMoment s ≤ H s := by
    dsimp [H]
    exact (lowMoment_le_of_box_bounds a hbox s).trans
      (le_add_of_nonneg_right he0)
  have hPro : lowMoment (s + 2) ≤ H (s + 2) := by
    dsimp [H]
    exact (lowMoment_le_of_box_bounds a hbox (s + 2)).trans
      (le_add_of_nonneg_right he2)
  have hmid : H (s + 1) ≤ highMoment (s + 1) + refinedTail (s + 1) := by
    dsimp [H]
    exact add_le_add (tenModeMoment_le_highMoment_of_box_bounds a hbox (s + 1))
      (htail (s + 1) (by omega) (by omega))
  have hHpos : 0 ≤ H s := by
    dsimp [H]
    exact add_nonneg (le_of_lt (tenModeMoment_pos a s ha)) he0
  have hmidpos : 0 ≤ H (s + 1) := by
    dsimp [H]
    exact add_nonneg (le_of_lt (tenModeMoment_pos a (s + 1) ha)) he1
  have hmidUpperPos : 0 ≤ highMoment (s + 1) + refinedTail (s + 1) := by
    apply add_nonneg
    · unfold highMoment
      exact le_of_lt (tenModeMoment_pos scaleUpper (s + 1)
        (fun i => (scale_box_bounds i).2.2))
    · exact (refinedTail_pos (s + 1)).le
  have hprod : lowMoment s * lowMoment (s + 2) ≤ H s * H (s + 2) :=
    mul_le_mul hPlo hPro hRpos.le hHpos
  have hsquare : H (s + 1) ^ 2 ≤
      (highMoment (s + 1) + refinedTail (s + 1)) ^ 2 :=
    (sq_le_sq₀ hmidpos hmidUpperPos).2 hmid
  have hmargin : 0 < earlyMargin s := early_margin_pos s hs
  have hmargin_le : earlyMargin s ≤
      H s * H (s + 2) - H (s + 1) ^ 2 := by
    unfold earlyMargin
    nlinarith
  change 0 < H s * H (s + 2) - H (s + 1) ^ 2
  exact lt_of_lt_of_le hmargin hmargin_le

/-- For every `s ≥ 4`, the first separated pair of boxes dominates the full five-term error.
The global tail estimate is sufficient in this range. -/
theorem hankel2_pos_large_of_ten_boxes_and_global_tail
    (a : Fin 10 → ℝ) (e : ℕ → ℝ) (s : ℕ)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i)
    (he : ∀ n, |e n| ≤ 60 * eta ^ (n + 1))
    (hs : 4 ≤ s) :
    0 < hankel2 (fun n => tenModeMoment a n + e n) s := by
  let P : ℕ → ℝ := tenModeMoment a
  let H : ℕ → ℝ := fun n => P n + e n
  have ha : ∀ i, 0 < a i := tenScale_pos_of_box_bounds a hbox
  have hPnonneg : ∀ n, 0 ≤ P n := by
    intro n
    dsimp [P]
    exact (tenModeMoment_pos a n ha).le
  have hPbound : ∀ n, P n ≤ 10 * scaleAUpper ^ (n + 1) := by
    intro n
    dsimp [P]
    apply tenModeMoment_le a n scaleAUpper (fun i => (ha i).le)
    intro i
    exact (hbox i).2.trans (scale_upper_le_A i)
  have herror : |hankel2 H s - hankel2 P s| ≤ determinantErrorBound s := by
    dsimp [H]
    exact hankel2_error_abs_bound P e s scaleAUpper eta
      (by norm_num [scaleAUpper]) eta_pos.le hPnonneg hPbound he
  have hratio : alpha * rho ^ (s + 1) + beta * rhoTwo ^ (s + 1) < 1 :=
    ratio_lt_one_of_four_le s hs
  have herror_strict : |hankel2 H s - hankel2 P s| < mainLower s := by
    rw [determinantErrorBound_eq_main_times_ratio] at herror
    apply lt_of_le_of_lt herror
    simpa only [mul_one] using mul_lt_mul_of_pos_left hratio (mainLower_pos s)
  have hmodel : mainLower s ≤ hankel2 P s := by
    dsimp [P]
    exact mainLower_le_tenMode_hankel2 a s hbox
  have hmodel_pos : 0 < hankel2 P s := lt_of_lt_of_le (mainLower_pos s) hmodel
  have hdiff_lower : -(mainLower s) < hankel2 H s - hankel2 P s :=
    (abs_lt.mp herror_strict).1
  change 0 < hankel2 H s
  nlinarith

/-- Conditional B1 theorem for an arbitrary sequence `H=P+e`; the original C2 sequence is
instantiated only after its analytic decomposition has been proved. -/
theorem central_hankel2_pos_of_ten_boxes_and_tail
    (H e : ℕ → ℝ) (a : Fin 10 → ℝ)
    (hdecomp : ∀ n, H n = tenModeMoment a n + e n)
    (hbox : ∀ i, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i)
    (he : ∀ n, |e n| ≤ 60 * eta ^ (n + 1))
    (hnonneg : ∀ n, n ≤ 5 → 0 ≤ e n)
    (htail : ∀ n, 1 ≤ n → n ≤ 4 → e n ≤ refinedTail n) :
    ∀ s, 0 < hankel2 H s := by
  have hH : H = fun n => tenModeMoment a n + e n := funext hdecomp
  intro s
  rw [hH]
  by_cases hs : s < 4
  · have hsmall := hankel2_pos_small_of_ten_boxes_and_tail a e s hbox hnonneg htail hs
    exact hsmall
  · have hslarge : 4 ≤ s := by omega
    have hlarge := hankel2_pos_large_of_ten_boxes_and_global_tail a e s hbox he hslarge
    exact hlarge

end
end CarrySigmaCentral
