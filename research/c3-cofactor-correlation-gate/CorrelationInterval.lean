import CompletedCoefficient

namespace C3CofactorCorrelation

open CarryC3Boxes CarryC3Tail CarryC3Gamma C3Cofactor
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

def normalizedOuterCompletedPolynomialBoxCalc (n : ℕ) : Box :=
  exactRangeSumBox (fun e =>
    (normalizedOuterCompletedPolynomialCoefficientBox n e).mul
      (powBoxExact piLogReference e)) n

def normalizedOuterCompletedPolynomialBoxTable : Fin 13 → Box := ![
  ⟨1 / 1, 1000000000000000000000003 / 1000000000000000000000000⟩,
  ⟨-21686781428580572061301 / 250000000000000000000000, -17349425142864457648721 / 200000000000000000000000⟩,
  ⟨103888857967598467740053 / 1000000000000000000000000, 51944428983799233870877 / 500000000000000000000000⟩,
  ⟨-4680435544772893528893 / 125000000000000000000000, -4680435544772893528757 / 125000000000000000000000⟩,
  ⟨15592526459117079989677 / 1000000000000000000000000, 1559252645911707999019 / 100000000000000000000000⟩,
  ⟨-3122449126416526100601 / 500000000000000000000000, -3122449126416526100451 / 500000000000000000000000⟩,
  ⟨2534476304169264880939 / 1000000000000000000000000, 158404769010579055081 / 62500000000000000000000⟩,
  ⟨-101728005589974620663 / 100000000000000000000000, -508640027949873102987 / 500000000000000000000000⟩,
  ⟨81493064794139406909 / 200000000000000000000000, 81493064794139407171 / 200000000000000000000000⟩,
  ⟨-163204197487469759261 / 1000000000000000000000000, -40801049371867439159 / 250000000000000000000000⟩,
  ⟨65338471498348826947 / 1000000000000000000000000, 13067694299669766443 / 200000000000000000000000⟩,
  ⟨-13072327698316526997 / 500000000000000000000000, -13072327698316521719 / 500000000000000000000000⟩,
  ⟨2091959679161502653 / 200000000000000000000000, 5229899197903767201 / 500000000000000000000000⟩
]

def normalizedOuterCompletedPolynomialBox (n : ℕ) : Box :=
  if hn : n < 13 then normalizedOuterCompletedPolynomialBoxTable ⟨n, hn⟩
  else normalizedOuterCompletedPolynomialBoxCalc n

theorem normalized_outer_completed_polynomial_box_table_bound (n : Fin 13) :
    (normalizedOuterCompletedPolynomialBoxCalc n.val).Subset
      (normalizedOuterCompletedPolynomialBoxTable n) := by
  fin_cases n <;> decide +kernel

theorem normalized_outer_completed_polynomial_box_contains (n : Fin 13) :
    (normalizedOuterCompletedPolynomialBox n.val).Contains
      (normalizedOuterCompletedPolynomialHorner (Real.log Real.pi)
        chartRatio (Real.log 3) n.val) := by
  have hcalc : (normalizedOuterCompletedPolynomialBoxCalc n.val).Contains
      (normalizedOuterCompletedPolynomialHorner (Real.log Real.pi)
        chartRatio (Real.log 3) n.val) := by
    unfold normalizedOuterCompletedPolynomialBoxCalc
      normalizedOuterCompletedPolynomialHorner
    apply exact_range_sum_box_contains
    intro e he
    exact Box.mul_contains
      (normalized_outer_completed_polynomial_coefficient_box_contains n.val e)
      (powBoxExact_contains pi_log_reference_contains e)
  have hbound := normalized_outer_completed_polynomial_box_table_bound n
  have hout := Box.subset_contains hbound hcalc
  simpa [normalizedOuterCompletedPolynomialBox, n.isLt] using hout

theorem normalized_outer_completed_box_contains (n : Fin 13) :
    (normalizedOuterCompletedPolynomialBox n.val).Contains
      (normalizedOuterCompletedJet48 n.val) := by
  rw [normalized_outer_completed_jet_eq_polynomial n]
  exact normalized_outer_completed_polynomial_box_contains n

def head48CorrelationBox (r : ℕ) : Box :=
  if hr : r < 13 then head48ReferenceBox ⟨r, hr⟩ else Box.point 0

theorem head48_correlation_box_contains (r : Fin 13) :
    (head48CorrelationBox r.val).Contains (head48RealJet r.val) := by
  simp [head48CorrelationBox, r.isLt]
  exact head48_reference_contains r

def normalizedCompletedReferenceBox (n : ℕ) : Box :=
  exactRangeSumBox (fun k => (head48CorrelationBox k).mul
    (normalizedOuterCompletedPolynomialBox (n - k))) n

theorem normalized_completed_reference_box_contains (n : Fin 13) :
    (normalizedCompletedReferenceBox n.val).Contains
      (normalizedCompletedJet48 n.val) := by
  unfold normalizedCompletedReferenceBox normalizedCompletedJet48
    convolution
  apply exact_range_sum_box_contains
  intro k hk
  have hhead : k < 13 := by have hn := n.isLt; omega
  have houter : n.val - k < 13 := by have hn := n.isLt; omega
  have hh := head48_reference_contains ⟨k, hhead⟩
  have ho := normalized_outer_completed_box_contains ⟨n.val - k, houter⟩
  simpa [head48CorrelationBox, hhead] using Box.mul_contains hh ho

def completedJet48ScaleBox : Box :=
  (((Box.point (-1 / 8 : ℚ)).mul piAmplitudeReference).mul
    ((chartJetBoxTable 0).inv)).mul
    (Box.point (gammaRealReference13 ⟨0, by omega⟩))

theorem completed_jet48_scale_box_contains :
    completedJet48ScaleBox.Contains completedJet48Scale := by
  have hpi := pi_amplitude_reference_contains
  have hchart : (chartJetBoxTable 0).Contains chartScale := by
    rw [chartScale_eq_chartRealJet_zero]
    exact chart_jet_box_table_contains 0
  have hinv := Box.inv_contains hchart
    (Or.inr (by norm_num [chartJetBoxTable]))
  have hgamma : (Box.point (gammaRealReference13 ⟨0, by omega⟩)).Contains
      gammaReferenceScale := by
    simpa [gammaReferenceScale] using
      (Box.point_contains (gammaRealReference13 ⟨0, by omega⟩))
  have hmul₁ := Box.mul_contains (Box.point_contains (-1 / 8 : ℚ)) hpi
  have hmul₂ := Box.mul_contains hmul₁ hinv
  have hmul₃ := Box.mul_contains hmul₂ hgamma
  simpa [completedJet48ScaleBox, completedJet48Scale, leftJet48Scale] using hmul₃

def nativeEvenFiniteReferenceBox (j : Fin 7) : Box :=
  (Box.point ((-1 : ℚ) ^ j.val)).mul
    (completedJet48ScaleBox.mul (normalizedCompletedReferenceBox (2 * j.val)))

theorem native_even_finite_reference_box_contains (j : Fin 7) :
    (nativeEvenFiniteReferenceBox j).Contains
      (((-1 : ℝ) ^ j.val) * finiteCompletedRealJet48 ⟨2 * j.val, by omega⟩) := by
  have hsign : (Box.point ((-1 : ℚ) ^ j.val)).Contains ((-1 : ℝ) ^ j.val) := by
    fin_cases j <;> norm_num [Box.point, Box.Contains]
  have hscale := completed_jet48_scale_box_contains
  have hnorm := normalized_completed_reference_box_contains ⟨2 * j.val, by omega⟩
  have hmul := Box.mul_contains hscale hnorm
  have hmul' := Box.mul_contains hsign hmul
  rw [finiteCompletedRealJet48_eq_normalized ⟨2 * j.val, by omega⟩]
  simpa [nativeEvenFiniteReferenceBox, completedJet48Scale] using hmul'

end
end C3CofactorCorrelation
