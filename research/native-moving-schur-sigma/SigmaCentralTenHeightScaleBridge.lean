import SigmaHeight50Integration
import SigmaCentralTenModeRationalGate

/-!
# Reciprocal-square scales from the certified height-50 zeros

This bridge maps the actual ordered zeta-zero heights to the rational scale boxes used by the
central ten-mode comparison. The returned `a` remains explicitly tied to the same `ts` witnesses.
-/

namespace CarrySigmaObstruction

set_option autoImplicit false
set_option maxHeartbeats 3000000

private theorem reciprocal_square_bounds {l t u : ℝ} (hl : 0 < l) (hlt : l < t)
    (htu : t < u) :
    1 / u ^ 2 ≤ (t ^ 2)⁻¹ ∧ (t ^ 2)⁻¹ ≤ 1 / l ^ 2 := by
  have ht : 0 < t := lt_trans hl hlt
  have hu : 0 < u := lt_trans ht htu
  have hlt_sq : l ^ 2 < t ^ 2 := by
    have hprod : 0 < (t - l) * (t + l) :=
      mul_pos (sub_pos.mpr hlt) (add_pos ht hl)
    nlinarith
  have htu_sq : t ^ 2 < u ^ 2 := by
    have hprod : 0 < (u - t) * (u + t) :=
      mul_pos (sub_pos.mpr htu) (add_pos hu ht)
    nlinarith
  have h_lower : 1 / u ^ 2 < 1 / t ^ 2 :=
    one_div_lt_one_div_of_lt (sq_pos_of_pos ht) htu_sq
  have h_upper : 1 / t ^ 2 < 1 / l ^ 2 :=
    one_div_lt_one_div_of_lt (sq_pos_of_pos hl) hlt_sq
  constructor
  · exact le_of_lt (by simpa [one_div] using h_lower)
  · exact le_of_lt (by simpa [one_div] using h_upper)

private theorem scale_bounds_of_height_box {i : Fin 10} {t : ℝ}
    (ht : t ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) :
    CarrySigmaCentral.scaleLower i ≤ (t ^ 2)⁻¹ ∧
      (t ^ 2)⁻¹ ≤ CarrySigmaCentral.scaleUpper i := by
  have hrecip := reciprocal_square_bounds (sigmaTenZeroLower_pos i) ht.1 ht.2
  have hUpper : CarrySigmaCentral.ordinateUpper = sigmaTenZeroBoxUpper := rfl
  have hLower : CarrySigmaCentral.ordinateLower = sigmaTenZeroBoxLower := rfl
  change 1 / (CarrySigmaCentral.ordinateUpper i) ^ 2 ≤ (t ^ 2)⁻¹ ∧
    (t ^ 2)⁻¹ ≤ 1 / (CarrySigmaCentral.ordinateLower i) ^ 2
  rw [hUpper, hLower]
  exact hrecip

/-- The ten actual height witnesses yield reciprocal-square scales in B1's exact rational
boxes. The same theorem also records the strict separation between the first two scales and
returns a no-extra-hypothesis witness of B1's `hbox`. -/
theorem sigmaHeight50_ten_height_scales :
    ∃ γ : ℝ, ∃ ts : Fin 10 → ℝ,
      ts 0 = γ ∧ StrictMono ts ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i) ∧
          riemannZeta (1 / 2 + ts i * Complex.I) = 0) ∧
      ∃ a : Fin 10 → ℝ,
      a = (fun i => ((ts i) ^ 2)⁻¹) ∧
        (∀ i, 0 < a i) ∧
        (∀ i, CarrySigmaCentral.scaleLower i ≤ a i ∧
          a i ≤ CarrySigmaCentral.scaleUpper i) ∧
        a 0 > a 1 ∧ a 1 > 0 := by
  obtain ⟨_, _, γ, _, _, hboxes⟩ := sigmaHeight50_ten_zero_witnesses_and_count
  obtain ⟨ts, hts0, hmono, htsBoxes⟩ := hboxes
  let a : Fin 10 → ℝ := fun i => ((ts i) ^ 2)⁻¹
  have hpos (i : Fin 10) : 0 < ts i :=
    lt_trans (sigmaTenZeroLower_pos i) (htsBoxes i).1.1
  have hscale (i : Fin 10) :
      CarrySigmaCentral.scaleLower i ≤ a i ∧
        a i ≤ CarrySigmaCentral.scaleUpper i := by
    change CarrySigmaCentral.scaleLower i ≤ ((ts i) ^ 2)⁻¹ ∧
      ((ts i) ^ 2)⁻¹ ≤ CarrySigmaCentral.scaleUpper i
    exact scale_bounds_of_height_box (htsBoxes i).1
  have h01 : ts 0 < ts 1 := hmono (by decide)
  have hsq : (ts 0) ^ 2 < (ts 1) ^ 2 := by
    have hprod : 0 < (ts 1 - ts 0) * (ts 1 + ts 0) :=
      mul_pos (sub_pos.mpr h01) (add_pos (hpos 1) (hpos 0))
    nlinarith
  have hinv : 1 / (ts 1) ^ 2 < 1 / (ts 0) ^ 2 :=
    one_div_lt_one_div_of_lt (sq_pos_of_pos (hpos 0)) hsq
  have horder : a 0 > a 1 := by
    change ((ts 1) ^ 2)⁻¹ < ((ts 0) ^ 2)⁻¹
    simpa [one_div] using hinv
  have ha1 : 0 < a 1 := by
    change 0 < ((ts 1) ^ 2)⁻¹
    have hsqpos : 0 < (ts 1) ^ 2 := sq_pos_of_pos (hpos 1)
    exact inv_pos.mpr hsqpos
  refine ⟨γ, ts, hts0, hmono, htsBoxes, a, rfl, ?_, ?_, horder, ha1⟩
  · intro i
    change 0 < ((ts i) ^ 2)⁻¹
    have hsqpos : 0 < (ts i) ^ 2 := sq_pos_of_pos (hpos i)
    exact inv_pos.mpr hsqpos
  · intro i
    exact hscale i

/-- B1's `hbox` is witnessed directly by the certified ten heights. -/
theorem exists_sigmaHeight50_scale_hbox :
    ∃ a : Fin 10 → ℝ,
      ∀ i, CarrySigmaCentral.scaleLower i ≤ a i ∧
        a i ≤ CarrySigmaCentral.scaleUpper i := by
  obtain ⟨_, _, _, _, _, a, _, _, hbox, _, _⟩ :=
    sigmaHeight50_ten_height_scales
  exact ⟨a, hbox⟩

#print axioms sigmaHeight50_ten_height_scales
#print axioms exists_sigmaHeight50_scale_hbox

end CarrySigmaObstruction
