import OddAsymptotics
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy

namespace CarryFirstOddGreen
open CarryRadialRefinement CarrySelfAdjointOperator Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- Conditional on the OLD h0 sign only, never on a new Schur pivot. -/
theorem odd_eventual_mixed_positive (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0) :
    ∀ᶠ k : ℕ in atTop, 0<(physicalForm (oddBulk η k) (oddResidual η k)).re := by
  have hc := mul_pos hh0 (odd_coefficient_pos η hη0 hη1)
  have h := (odd_mixed_scaled_limit η hη0 hη1).eventually (lt_mem_nhds hc)
  filter_upwards [h] with k hk
  have hp : 0<((k : ℝ)+1)^2 := by positivity
  simpa using (lt_div_iff₀ hp).mp hk

theorem odd_eventual_bulk_negative (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0) :
    ∀ᶠ k : ℕ in atTop, (physicalForm (oddBulk η k) (oddBulk η k)).re<0 := by
  have hc : -2*(canonicalCompletedNativeLogDerivativeMoment 0*oddCoefficient η)<0 :=
    mul_neg_of_neg_of_pos (by norm_num) (mul_pos hh0 (odd_coefficient_pos η hη0 hη1))
  have h := (odd_bulk_scaled_limit η hη0 hη1).eventually (gt_mem_nhds hc)
  filter_upwards [h] with k hk
  have hp : 0<((k : ℝ)+1)^2 := by positivity
  simpa using (div_lt_iff₀ hp).mp hk

/-- A NO-GO only for taking finite limits of the mixed piece separately. -/
theorem odd_mixed_no_finite_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0) :
    ¬∃ c : ℝ, Tendsto (fun (k : ℕ) => (physicalForm (oddBulk η k) (oddResidual η k)).re)
      atTop (nhds c) := by
  rintro ⟨c,hc⟩
  have hz := hc.mul (inverse_radial_mass_limit.pow 2)
  have hz' : Tendsto (fun (k : ℕ) => (physicalForm (oddBulk η k) (oddResidual η k)).re/
      ((k : ℝ)+1)^2) atTop (nhds 0) := by simpa [div_eq_mul_inv,inv_pow] using hz
  have he := tendsto_nhds_unique hz' (odd_mixed_scaled_limit η hη0 hη1)
  exact (ne_of_gt (mul_pos hh0 (odd_coefficient_pos η hη0 hη1))) he.symm

theorem odd_bulk_no_finite_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0) :
    ¬∃ c : ℝ, Tendsto (fun (k : ℕ) => (physicalForm (oddBulk η k) (oddBulk η k)).re)
      atTop (nhds c) := by
  rintro ⟨c,hc⟩
  have hz := hc.mul (inverse_radial_mass_limit.pow 2)
  have hz' : Tendsto (fun (k : ℕ) => (physicalForm (oddBulk η k) (oddBulk η k)).re/
      ((k : ℝ)+1)^2) atTop (nhds 0) := by simpa [div_eq_mul_inv,inv_pow] using hz
  have he := tendsto_nhds_unique hz' (odd_bulk_scaled_limit η hη0 hη1)
  have hp := mul_pos hh0 (odd_coefficient_pos η hη0 hη1)
  linarith

/-- The complete finite balance has its already independently known h1 sign.
This is a regression, not a proof of higher pivots. -/
theorem odd_eventual_compensation (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0)
    (hh1 : 0<canonicalCompletedNativeLogDerivativeMoment 1) :
    ∀ᶠ k : ℕ in atTop,
      (physicalForm (oddBulk η k) (oddBulk η k)).re<0 ∧
      0<(physicalForm (oddBulk η k) (oddResidual η k)).re ∧
      -(physicalForm (oddBulk η k) (oddBulk η k)).re<
        2*(physicalForm (oddBulk η k) (oddResidual η k)).re := by
  have hp := odd_source_limit.eventually (lt_mem_nhds hh1)
  filter_upwards [odd_eventual_bulk_negative η hη0 hη1 hh0,
    odd_eventual_mixed_positive η hη0 hη1 hh0,hp,node_regular_eventually] with k hb hm hs hr
  refine ⟨hb,hm,?_⟩
  rw [odd_energy_three_sectors η hη0 hη1 k hr] at hs
  linarith

theorem canonical_odd_channel_signs (η : ℝ) (hη0 : 0<η) (hη1 : η<1) :
    ∀ᶠ k : ℕ in atTop,
      (physicalForm (oddBulk η k) (oddBulk η k)).re<0 ∧
      0<(physicalForm (oddBulk η k) (oddResidual η k)).re :=
  (odd_eventual_bulk_negative η hη0 hη1 canonicalCompletedNativeLogDerivativeMoment_zero_pos).and
    (odd_eventual_mixed_positive η hη0 hη1 canonicalCompletedNativeLogDerivativeMoment_zero_pos)

end
end CarryFirstOddGreen
