import HighChartReciprocal17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets C3CofactorCorrelation
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- The chart quotient is boxed directly from the tight original amplitude
interval, avoiding the repeated inversion of unnormalized chart jets. -/
def tightChartRatioBox17 : Box :=
  chartAmplitudeReferenceTight.mul
    ((Box.point (1 : ℚ)).sub chartAmplitudeReferenceTight).inv

/-- Rational recurrence table for the reciprocal of the normalized chart
denominator, rounded outward at scale `10^40`. -/
def tightNormalizedChartReciprocalTable17 : Fin 17 → Box := ![
  ⟨10000000000000000000000000000000000000000/10^40,
    10000000000000000000000000000000000000000/10^40⟩,
  ⟨25993445838985105028724495142007621397705/10^40,
    25993445838985105028724495142007621397706/10^40⟩,
  ⟨53287563146656217610620021299789646813266/10^40,
    53287563146656217610620021299789646813269/10^40⟩,
  ⟨106627155931088406428583411297573335597827/10^40,
    106627155931088406428583411297573335597837/10^40⟩,
  ⟨213230154279823406094711224055440659385339/10^40,
    213230154279823406094711224055440659385371/10^40⟩,
  ⟨426458142220540457387489734468393647443850/10^40,
    426458142220540457387489734468393647443950/10^40⟩,
  ⟨852916904667935581604953600562034467506164/10^40,
    852916904667935581604953600562034467506476/10^40⟩,
  ⟨1705833892687701453510323040457514709242578/10^40,
    1705833892687701453510323040457514709243551/10^40⟩,
  ⟨3411667769368897444599351106492649918634707/10^40,
    3411667769368897444599351106492649918637740/10^40⟩,
  ⟨6823335535733667865887867596945434886070515/10^40,
    6823335535733667865887867596945434886079968/10^40⟩,
  ⟨13646671071859915443998619963284609378110636/10^40,
    13646671071859915443998619963284609378140097/10^40⟩,
  ⟨27293342143822797028827723478457989015655156/10^40,
    27293342143822797028827723478457989015746971/10^40⟩,
  ⟨54586684287636820536233600097276601926212963/10^40,
    54586684287636820536233600097276601926499102/10^40⟩,
  ⟨109173368575270251628841982465261613599253470/10^40,
    109173368575270251628841982465261613600145210/10^40⟩,
  ⟨218346737150540666517649023302392970962948861/10^40,
    218346737150540666517649023302392970965727926/10^40⟩,
  ⟨436693474301081440819300057422274259333173685/10^40,
    436693474301081440819300057422274259341834499/10^40⟩,
  ⟨873386948602162879956105982000560698420780531/10^40,
    873386948602162879956105982000560698447771498/10^40⟩]

def tightNormalizedChartDenominatorBox17 (n : ℕ) : Box :=
  if n = 0 then Box.point 1 else
    (tightChartRatioBox17.mul (Box.point ((-1 : ℚ)^(n+1)))).mul
      ((powBoxExact logThreeBoxTight n).mul (Box.point ((n.factorial : ℚ)⁻¹)))

def tightNormalizedChartReciprocalLookup17 (n : ℕ) : Box :=
  if hn : n < 17 then tightNormalizedChartReciprocalTable17 ⟨n, hn⟩
  else Box.point 0

def tightNormalizedChartReciprocalCalc17 (r : Fin 17) : Box :=
  if r.val = 0 then Box.point 1 else
    (exactRangeSumBox (fun j =>
      (tightNormalizedChartReciprocalLookup17 j).mul
        (tightNormalizedChartDenominatorBox17 (r.val-j))) (r.val-1)).neg

theorem tight_normalized_chart_reciprocal_table_bound17 (r : Fin 17) :
    (tightNormalizedChartReciprocalCalc17 r).Subset
      (tightNormalizedChartReciprocalTable17 r) := by
  fin_cases r <;> decide +kernel

theorem tight_chart_ratio_box17_contains :
    tightChartRatioBox17.Contains chartRatio := by
  have hscale : ((Box.point (1 : ℚ)).sub chartAmplitudeReferenceTight).Contains
      chartScale := by
    simpa [Box.point, Box.sub, Box.add, Box.neg, chartScale] using
      Box.sub_contains (Box.point_contains (1 : ℚ)) chart_amplitude_tight_contains
  have hscaleInv := Box.inv_contains hscale (Or.inr (by
    norm_num [Box.point, Box.sub, Box.add, Box.neg,
      chartAmplitudeReferenceTight]))
  have hratio := Box.mul_contains chart_amplitude_tight_contains hscaleInv
  simpa [tightChartRatioBox17, chartRatio, div_eq_mul_inv] using hratio

theorem tight_normalized_chart_denominator_box17_contains (n : ℕ) :
    (tightNormalizedChartDenominatorBox17 n).Contains
      (normalizedChartDenominator chartRatio (Real.log 3) n) := by
  by_cases hn : n = 0
  · subst n
    norm_num [tightNormalizedChartDenominatorBox17, normalizedChartDenominator,
      Box.point, Box.Contains]
  · have hq := tight_chart_ratio_box17_contains
    have hsign : (Box.point ((-1 : ℚ)^(n+1))).Contains
        ((-1 : ℝ)^(n+1)) := by
      exact_mod_cast (Box.point_contains ((-1 : ℚ)^(n+1)))
    have hell := powBoxExact_contains log_three_tight_contains n
    have hfact : (Box.point ((n.factorial : ℚ)⁻¹)).Contains
        ((n.factorial : ℝ)⁻¹) := by
      simpa only [Rat.cast_inv, Rat.cast_natCast] using
        (Box.point_contains ((n.factorial : ℚ)⁻¹))
    have hleft := Box.mul_contains hq hsign
    have hright := Box.mul_contains hell hfact
    have hmul := Box.mul_contains hleft hright
    simpa [tightNormalizedChartDenominatorBox17, normalizedChartDenominator,
      hn, div_eq_mul_inv, mul_assoc] using hmul

theorem tight_normalized_chart_reciprocal_calc17_contains (n : ℕ) (hn : n < 17) :
    (tightNormalizedChartReciprocalCalc17 ⟨n, hn⟩).Contains
      (normalizedChartReciprocal chartRatio (Real.log 3) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      norm_num [tightNormalizedChartReciprocalCalc17,
        normalizedChartReciprocal, reciprocalJet, normalizedChartDenominator,
        Box.point, Box.Contains]
    | succ n =>
      have hn' : n+1 < 17 := by omega
      have hterms : ∀ j < n+1,
          ((tightNormalizedChartReciprocalLookup17 j).mul
              (tightNormalizedChartDenominatorBox17 (n+1-j))).Contains
            (normalizedChartReciprocal chartRatio (Real.log 3) j *
              normalizedChartDenominator chartRatio (Real.log 3) (n+1-j)) := by
        intro j hj
        have hj17 : j < 17 := by omega
        have hlookup : tightNormalizedChartReciprocalLookup17 j =
            tightNormalizedChartReciprocalTable17 ⟨j, hj17⟩ := by
          simp [tightNormalizedChartReciprocalLookup17, hj17]
        have hrecip := ih j (by omega) (by omega)
        rw [hlookup]
        exact Box.mul_contains
          (Box.subset_contains (tight_normalized_chart_reciprocal_table_bound17
            ⟨j, hj17⟩) hrecip)
          (tight_normalized_chart_denominator_box17_contains (n+1-j))
      have hsum := exact_range_sum_box_contains
        (fun j => (tightNormalizedChartReciprocalLookup17 j).mul
          (tightNormalizedChartDenominatorBox17 (n+1-j)))
        (fun j => normalizedChartReciprocal chartRatio (Real.log 3) j *
          normalizedChartDenominator chartRatio (Real.log 3) (n+1-j))
        n hterms
      have hrec : normalizedChartReciprocal chartRatio (Real.log 3) (n+1) =
          -∑ j ∈ Finset.range (n+1),
            normalizedChartReciprocal chartRatio (Real.log 3) j *
              normalizedChartDenominator chartRatio (Real.log 3) (n+1-j) := by
        unfold normalizedChartReciprocal
        rw [reciprocalJet]
        have hsumFin : (∑ j : Fin (n+1),
            reciprocalJet (normalizedChartDenominator chartRatio (Real.log 3)) j.val *
              normalizedChartDenominator chartRatio (Real.log 3) (n+1-j.val)) =
            ∑ j ∈ Finset.range (n+1),
              reciprocalJet (normalizedChartDenominator chartRatio (Real.log 3)) j *
                normalizedChartDenominator chartRatio (Real.log 3) (n+1-j) := by
          exact Fin.sum_univ_eq_sum_range
            (fun j => reciprocalJet (normalizedChartDenominator chartRatio (Real.log 3)) j *
              normalizedChartDenominator chartRatio (Real.log 3) (n+1-j)) (n+1)
        rw [hsumFin]
        simp [normalizedChartDenominator]
      have hneg := Box.neg_contains hsum
      have hcalc : (tightNormalizedChartReciprocalCalc17 ⟨n+1, hn'⟩).Contains
          (normalizedChartReciprocal chartRatio (Real.log 3) (n+1)) := by
        simpa [tightNormalizedChartReciprocalCalc17, Nat.succ_ne_zero,
          hrec] using hneg
      simpa using hcalc

def normalizedChartReciprocalBoxVerified17 (n : ℕ) : Box :=
  if hn : n < 17 then tightNormalizedChartReciprocalTable17 ⟨n, hn⟩
  else Box.point 0

theorem normalized_chart_reciprocal_box_verified17_contains (n : ℕ) (hn : n < 17) :
    (normalizedChartReciprocalBoxVerified17 n).Contains
      (normalizedChartReciprocal chartRatio (Real.log 3) n) := by
  simp [normalizedChartReciprocalBoxVerified17, hn]
  exact Box.subset_contains
    (tight_normalized_chart_reciprocal_table_bound17 ⟨n, hn⟩)
    (tight_normalized_chart_reciprocal_calc17_contains n hn)

end
end C3ShiftedFourth
