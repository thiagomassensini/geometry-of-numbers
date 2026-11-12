import CompletedCoefficient

namespace C3CofactorCorrelation
open CarryC3Boxes CarryC3Tail CarryC3Gamma
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

def leftJet48MagnitudeBound : Fin 13 → ℚ := ![
  7/50, 3/10, 3/200, 4/125, 21/5000, 7/10000, 3/10000, 1/25000,
  1/1000000, 1/1000000, 1/1000000, 1/1000000, 1/1000000
]

def normalizedLeftJet48CorrelationBox (r : Fin 13) : Box :=
  exactRangeSumBox (fun k =>
    (normalizedOuterBasePolynomialBox k).mul
      (head48ReferenceBox ⟨r.val-k, by omega⟩)) r.val

theorem normalized_left_jet48_correlation_box_contains (r : Fin 13) :
    (normalizedLeftJet48CorrelationBox r).Contains
      (normalizedLeftJet48 (Real.log Real.pi) chartRatio (Real.log 3) r.val) := by
  unfold normalizedLeftJet48CorrelationBox normalizedLeftJet48
  apply exact_range_sum_box_contains
  intro k hk
  exact Box.mul_contains
    (normalized_outer_base_box_contains ⟨k, by omega⟩)
    (head48_reference_contains ⟨r.val-k, by omega⟩)

def leftJet48ScaleBox : Box :=
  ((Box.point (-1/8:ℚ)).mul piAmplitudeReference).mul
    ((chartJetBoxTable 0).inv)

theorem left_jet48_scale_box_contains :
    leftJet48ScaleBox.Contains leftJet48Scale := by
  have hpi := pi_amplitude_reference_contains
  have hchart : (chartJetBoxTable 0).Contains chartScale := by
    rw [chartScale_eq_chartRealJet_zero]
    exact chart_jet_box_table_contains 0
  have hinv := Box.inv_contains hchart (Or.inr (by norm_num [chartJetBoxTable]))
  have hmul := Box.mul_contains (Box.point_contains (-1/8:ℚ)) hpi
  have hmul' := Box.mul_contains hmul hinv
  simpa [leftJet48ScaleBox, leftJet48Scale] using hmul'

def leftJet48CorrelatedBox (r : Fin 13) : Box :=
  leftJet48ScaleBox.mul (normalizedLeftJet48CorrelationBox r)

theorem left_jet48_correlated_box_contains (r : Fin 13) :
    (leftJet48CorrelatedBox r).Contains (leftRealJet48 r.val) := by
  have h := Box.mul_contains (left_jet48_scale_box_contains)
    (normalized_left_jet48_correlation_box_contains r)
  rw [leftRealJet48_eq_normalized r.val]
  simpa [leftJet48CorrelatedBox] using h

theorem left_jet48_correlated_box_abs_bound_low (r : Fin 7) :
    -leftJet48MagnitudeBound ⟨r.val, by omega⟩ ≤
        (leftJet48CorrelatedBox ⟨r.val, by omega⟩).lo ∧
      (leftJet48CorrelatedBox ⟨r.val, by omega⟩).hi ≤
        leftJet48MagnitudeBound ⟨r.val, by omega⟩ := by
  fin_cases r <;> decide +kernel

end
end C3CofactorCorrelation
