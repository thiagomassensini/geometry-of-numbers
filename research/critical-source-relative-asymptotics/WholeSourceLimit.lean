import SourceLeading

namespace CarryCriticalRelative
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000

/-- Observation scale for the exact original vectors, never a new metric. -/
def observationScale (k m : ℕ) : ℂ :=
  step k ^ m * ((Real.sqrt ((k:ℝ)+1) : ℝ) : ℂ)⁻¹

theorem observationScale_ne (k m : ℕ) : observationScale k m ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero _ (canonicalCompletedC3RadialSecondStep_ne_zero k))
  apply inv_ne_zero
  exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < (k:ℝ)+1)).ne'

theorem synthesis_scale (k m N : ℕ) (c : Fin N → ℂ) :
    observationScale k m • radialIncidentSynthesis k N c =
      radialIncidentSynthesis 0 N (fun r => step k ^ m * c r) := by
  have hs : (((Real.sqrt ((k:ℝ)+1) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < (k:ℝ)+1)).ne'
  simp only [radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    completedNativeRadialChiralCauchyState, Finset.smul_sum, smul_smul,
    Nat.cast_zero, zero_add, Real.sqrt_one, Complex.ofReal_one, mul_one]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  unfold observationScale
  field_simp

theorem scaled_incident_tendsto (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hx : ∀ a : Fin (2*n), m < a.val → x a = 0) :
    Tendsto (fun k => observationScale k m •
      (nativeSourceProjectiveBoundaryJetSynthesis n k x).1)
      atTop (nhds (leadingState n m x hm)) := by
  have hc : Continuous (radialIncidentSynthesis 0 (2*n)) :=
    LinearMap.continuous_of_finiteDimensional _
  have h := hc.continuousAt.tendsto.comp (scaled_input_tendsto n m x hm hx)
  simpa only [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,
    synthesis_scale, leadingState, Function.comp_def] using h

theorem scaled_returned_tendsto (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hx : ∀ a : Fin (2*n), m < a.val → x a = 0) :
    Tendsto (fun k => observationScale k m •
      (nativeSourceProjectiveBoundaryJetSynthesis n k x).2)
      atTop (nhds (-leadingState n m x hm)) := by
  have ht : Tendsto (fun k => fun r =>
      step k ^ m * nativeSourceChiralJetInput n k x r *
        completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k r))
      atTop (nhds (-leadingCoefficients n m x hm)) := by
    apply tendsto_pi_nhds.mpr
    intro r
    have h := ((tendsto_pi_nhds.mp (scaled_input_tendsto n m x hm hx)) r).mul
      (quotient_tendsto r)
    simpa only [mul_neg, mul_one, Pi.neg_apply] using h
  have hc : Continuous (radialIncidentSynthesis 0 (2*n)) :=
    LinearMap.continuous_of_finiteDimensional _
  have h := hc.continuousAt.tendsto.comp ht
  simpa only [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,
    radialReturnedSynthesis_eq_incident_multiply, synthesis_scale, mul_assoc,
    leadingState, map_neg, Function.comp_def] using h

/-- Joint physical state limit BEFORE a norm or signed readout is applied.
Both legs survive; their leading signed energy cancels exactly. -/
theorem scaled_whole_source_tendsto (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hx : ∀ a : Fin (2*n), m < a.val → x a = 0) :
    Tendsto (fun k => observationScale k m • nativeSourceProjectiveBoundaryJetSynthesis n k x)
      atTop (nhds (leadingState n m x hm, -leadingState n m x hm)) := by
  exact (scaled_incident_tendsto n m x hm hx).prodMk_nhds
    (scaled_returned_tendsto n m x hm hx)

theorem leading_signed_form_zero (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n) :
    canonicalCompletedNativeProjectiveChiralForm
      (leadingState n m x hm, -leadingState n m x hm)
      (leadingState n m x hm, -leadingState n m x hm) = 0 := by
  simp [canonicalCompletedNativeProjectiveChiralForm]

/-- Even though both original energies grow, their relative ratio tends to
one for every nonzero highest jet. This says nothing about the sign of the
small difference. -/
theorem returned_incident_energy_ratio_tendsto_one (n m : ℕ) (x : Fin (2*n) → ℂ)
    (hm : m < 2*n) (hx : ∀ a : Fin (2*n), m < a.val → x a = 0)
    (hxm : x ⟨m,hm⟩ ≠ 0) :
    Tendsto (fun k => ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2 /
      ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2) atTop (nhds 1) := by
  have hw := leadingState_ne_zero n m x hm hxm
  have hp := (scaled_incident_tendsto n m x hm hx).norm.pow 2
  have hn := (scaled_returned_tendsto n m x hm hx).norm.pow 2
  have h := hn.div hp (pow_ne_zero 2 (norm_ne_zero_iff.mpr hw))
  change Tendsto (fun k =>
    ‖observationScale k m • (nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2 /
    ‖observationScale k m • (nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2)
    atTop (nhds (‖-leadingState n m x hm‖^2 / ‖leadingState n m x hm‖^2)) at h
  have he (k : ℕ) :
      ‖observationScale k m • (nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2 /
      ‖observationScale k m • (nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2 =
      ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2 /
        ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2 := by
    simp only [norm_smul, mul_pow]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (observationScale_ne k m)))
  simpa only [he, norm_neg, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hw))] using h

theorem incident_eventually_ne_zero (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hx : ∀ a : Fin (2*n), m < a.val → x a = 0) (hxm : x ⟨m,hm⟩ ≠ 0) :
    ∀ᶠ k : ℕ in atTop, (nativeSourceProjectiveBoundaryJetSynthesis n k x).1 ≠ 0 := by
  have h := (scaled_incident_tendsto n m x hm hx).eventually_ne
    (leadingState_ne_zero n m x hm hxm)
  filter_upwards [h] with k hk hz
  exact hk (by simp [hz])

/-- Fixed relative loss is impossible even at one fixed order and one fixed
direction. This is about the actual completed source, not an affine probe. -/
theorem no_fixed_relative_contraction (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hx : ∀ a : Fin (2*n), m < a.val → x a = 0) (hxm : x ⟨m,hm⟩ ≠ 0)
    (rho : ℝ) (hrho : rho < 1) :
    ¬ (∀ᶠ k : ℕ in atTop, ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2 ≤
      rho * ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2) := by
  intro hb
  have hlim := returned_incident_energy_ratio_tendsto_one n m x hm hx hxm
  have he : ∀ᶠ k : ℕ in atTop,
      ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2 /
        ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2 ≤ rho := by
    filter_upwards [hb, incident_eventually_ne_zero n m x hm hx hxm] with k hk hne
    exact (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne))).mpr hk
  exact (not_le_of_gt hrho) (le_of_tendsto hlim he)

end
end CarryCriticalRelative
