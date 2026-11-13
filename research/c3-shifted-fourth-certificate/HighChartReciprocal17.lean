import ChartReciprocal

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma C3CofactorCorrelation
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

def chartJetBox17 (r : Fin 17) : Box :=
  if h : r.val < 13 then chartJetBoxTable ⟨r.val, h⟩ else
    chartJetBoxExact r.val

def normalizedChartReciprocalBoxTable17 (r : Fin 17) : Box :=
  if h : r.val < 13 then normalizedChartReciprocalBoxTable ⟨r.val, h⟩ else
    if r.val = 13 then
      ⟨10917336857527025162884198235648091 / 1000000000000000000000000000000,
        2729334214381756290721049564358359 / 250000000000000000000000000000⟩
    else if r.val = 14 then
      ⟨1364667107190879165735306393518169 / 62500000000000000000000000000,
        4366934743010813330352980472848567 / 200000000000000000000000000000⟩
    else if r.val = 15 then
      ⟨43669347430108144081930005636335077 / 1000000000000000000000000000000,
        43669347430108144081930005848222701 / 1000000000000000000000000000000⟩
    else
      ⟨87338694860216287995610597869865469 / 1000000000000000000000000000000,
        43669347430108143997805299265219281 / 500000000000000000000000000000⟩

def normalizedChartReciprocalBoxCalc17 (r : Fin 17) : Box :=
  if h : r.val = 0 then Box.point 1 else
    bmul (bneg (roundedSumBoxFin (fun j : Fin r.val =>
      bmul (normalizedChartReciprocalBoxTable17 ⟨j.val, by omega⟩)
        (chartJetBox17 ⟨r.val-j.val, by omega⟩))))
      (binv (chartJetBox17 ⟨0, by omega⟩))

theorem chart_jet_box17_contains (r : Fin 17) :
    (chartJetBox17 r).Contains (chartRealJet r.val) := by
  by_cases h : r.val < 13
  · simpa [chartJetBox17, h] using chart_jet_box_table_contains ⟨r.val, h⟩
  · simpa [chartJetBox17, h] using chart_jet_box_exact r.val

theorem normalized_chart_reciprocal_box17_table_bound (r : Fin 17) :
    (normalizedChartReciprocalBoxCalc17 r).Subset
      (normalizedChartReciprocalBoxTable17 r) := by
  fin_cases r <;> decide +kernel

theorem normalized_chart_reciprocal_box17_table_contains (n : ℕ) (hn : n < 17) :
    (normalizedChartReciprocalBoxTable17 ⟨n, hn⟩).Contains
      (chartScale * reciprocalJet chartRealJet n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have hscale : chartScale * (chartRealJet 0)⁻¹ = 1 := by
        rw [← chartScale_eq_chartRealJet_zero]
        exact mul_inv_cancel₀ chartScale_ne_zero
      rw [reciprocalJet, hscale]
      norm_num [normalizedChartReciprocalBoxTable17,
        normalizedChartReciprocalBoxTable, Box.point, Box.Contains]
    | succ n =>
      have hsum : (roundedSumBoxFin (fun j : Fin (n+1) =>
          bmul (normalizedChartReciprocalBoxTable17 ⟨j.val, by omega⟩)
            (chartJetBox17 ⟨n+1-j.val, by omega⟩))).Contains
          (∑ j : Fin (n+1),
            (chartScale * reciprocalJet chartRealJet j.val) *
              chartRealJet (n+1-j.val)) := by
        apply rounded_sum_box_fin_contains
        intro j
        exact bmul_contains
          (ih j.val (by omega) (by omega))
          (chart_jet_box17_contains ⟨n+1-j.val, by omega⟩)
      have hinv : (binv (chartJetBox17 ⟨0, by omega⟩)).Contains
          (chartRealJet 0)⁻¹ := by
        apply binv_contains (chart_jet_box17_contains ⟨0, by omega⟩)
        right
        norm_num [chartJetBox17, chartJetBoxTable]
      have hstep := bmul_contains (Box.neg_contains hsum) hinv
      have hrec : chartScale * reciprocalJet chartRealJet (n+1) =
          -(∑ j : Fin (n+1),
            (chartScale * reciprocalJet chartRealJet j.val) *
              chartRealJet (n+1-j.val)) * (chartRealJet 0)⁻¹ := by
        have hsumScale :
            (∑ j : Fin (n+1),
              (chartScale * reciprocalJet chartRealJet j.val) *
                chartRealJet (n+1-j.val)) =
              chartScale * (∑ j : Fin (n+1),
                reciprocalJet chartRealJet j.val * chartRealJet (n+1-j.val)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [reciprocalJet, div_eq_mul_inv,
          show chartRealJet 0 = chartScale from chartScale_eq_chartRealJet_zero.symm,
          hsumScale]
        field_simp [chartScale_ne_zero]
      rw [← hrec] at hstep
      have hn' : n+1 < 17 := by omega
      have hstep' : (normalizedChartReciprocalBoxCalc17 ⟨n+1, hn'⟩).Contains
          (chartScale * reciprocalJet chartRealJet (n+1)) := by
        simpa [normalizedChartReciprocalBoxCalc17, hn', bneg] using hstep
      exact Box.subset_contains
        (normalized_chart_reciprocal_box17_table_bound ⟨n+1, hn'⟩) hstep'

theorem normalized_chart_reciprocal_box17_contains (r : Fin 17) :
    (normalizedChartReciprocalBoxTable17 r).Contains
      (normalizedChartReciprocal chartRatio (Real.log 3) r.val) := by
  rw [normalizedChartReciprocal_eq_scale_mul]
  exact normalized_chart_reciprocal_box17_table_contains r.val r.isLt

end
end C3ShiftedFourth
