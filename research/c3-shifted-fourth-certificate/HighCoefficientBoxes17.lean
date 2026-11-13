import HighChartReciprocal17
import CorrelatedJets17
import FastHeadEvaluation17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets C3CofactorCorrelation
open Set Filter Topology
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

def normalizedChartReciprocalBoxVerified17 (n : ℕ) : Box :=
  if h : n < 17 then normalizedChartReciprocalBoxTable17 ⟨n, h⟩ else Box.point 0

theorem normalized_chart_reciprocal_box_verified17_contains (n : ℕ) (hn : n < 17) :
    (normalizedChartReciprocalBoxVerified17 n).Contains
      (normalizedChartReciprocal chartRatio (Real.log 3) n) := by
  simp [normalizedChartReciprocalBoxVerified17, hn]
  exact normalized_chart_reciprocal_box17_contains ⟨n, hn⟩

def normalizedOuterBasePolynomialCoefficientBoxVerified17
    (n e : ℕ) : Box :=
  if e ≤ n then
    exactRangeSumBox (fun i =>
      if i + e ≤ n then
        (Box.point (normalizedPolynomialCoefficientQ i)).mul
          ((Box.point (normalizedExponentialCoefficientQ e)).mul
            (normalizedChartReciprocalBoxVerified17 (n-i-e)))
      else Box.point 0) n
  else Box.point 0

theorem normalized_outer_base_polynomial_coefficient_box_verified17_contains
    (n e : ℕ) (hn : n < 17) :
    (normalizedOuterBasePolynomialCoefficientBoxVerified17 n e).Contains
      (normalizedOuterBasePolynomialCoeff chartRatio (Real.log 3) n e) := by
  by_cases he : e ≤ n
  · simp only [normalizedOuterBasePolynomialCoefficientBoxVerified17, if_pos he]
    unfold normalizedOuterBasePolynomialCoeff
    simp only [if_pos he]
    apply exact_range_sum_box_contains
    intro i hi
    by_cases hie : i + e ≤ n
    · simp only [if_pos hie]
      have hindex : n-i-e < 17 := by omega
      have hrec := normalized_chart_reciprocal_box_verified17_contains (n-i-e) hindex
      have hinner := Box.mul_contains (normalized_exponential_coefficient_point e) hrec
      have houter := Box.mul_contains (normalized_polynomial_coefficient_point i) hinner
      simpa [hie, normalizedChartReciprocalBoxVerified17, hindex] using houter
    · simp [hie, Box.point, Box.Contains]
  · simp only [normalizedOuterBasePolynomialCoefficientBoxVerified17, if_neg he]
    unfold normalizedOuterBasePolynomialCoeff
    simp only [if_neg he]
    simp [Box.point, Box.Contains]

def normalizedOuterCompletedPolynomialCoefficientBoxVerified17
    (n e : ℕ) : Box :=
  if e ≤ n then
    exactRangeSumBox (fun j =>
      if e ≤ j then
        (normalizedOuterBasePolynomialCoefficientBoxVerified17 j e).mul
          (Box.point (normalizedGammaCoefficientQ17 (n-j)))
      else Box.point 0) n
  else Box.point 0

theorem normalized_outer_completed_polynomial_coefficient_box_verified17_contains
    (n e : ℕ) (hn : n < 17) :
    (normalizedOuterCompletedPolynomialCoefficientBoxVerified17 n e).Contains
      (normalizedOuterCompletedPolynomialCoefficient17 chartRatio (Real.log 3) n e) := by
  by_cases he : e ≤ n
  · simp only [normalizedOuterCompletedPolynomialCoefficientBoxVerified17, if_pos he]
    unfold normalizedOuterCompletedPolynomialCoefficient17
    simp only [if_pos he]
    apply exact_range_sum_box_contains
    intro j hj
    by_cases hje : e ≤ j
    · simp only [if_pos hje]
      have hbase := normalized_outer_base_polynomial_coefficient_box_verified17_contains
        j e (by omega)
      have hgamma := normalized_gamma_coefficient_point17 (n-j)
      have hmul := Box.mul_contains hbase hgamma
      simpa [hje] using hmul
    · simp [hje, Box.point, Box.Contains]
  · simp only [normalizedOuterCompletedPolynomialCoefficientBoxVerified17, if_neg he]
    unfold normalizedOuterCompletedPolynomialCoefficient17
    simp only [if_neg he]
    simp [Box.point, Box.Contains]

def normalizedOuterCompletedPolynomialBoxVerified17 (n : ℕ) : Box :=
  exactRangeSumBox (fun e =>
    (normalizedOuterCompletedPolynomialCoefficientBoxVerified17 n e).mul
      (powBoxExact piLogReference e)) n

theorem normalized_outer_completed_polynomial_box_verified17_contains (n : Fin 17) :
    (normalizedOuterCompletedPolynomialBoxVerified17 n.val).Contains
      (normalizedOuterCompletedPolynomialHorner17 (Real.log Real.pi)
        chartRatio (Real.log 3) n.val) := by
  unfold normalizedOuterCompletedPolynomialBoxVerified17
    normalizedOuterCompletedPolynomialHorner17
  apply exact_range_sum_box_contains
  intro e he
  exact Box.mul_contains
    (normalized_outer_completed_polynomial_coefficient_box_verified17_contains
      n.val e n.isLt)
    (powBoxExact_contains pi_log_reference_contains e)

theorem normalized_outer_completed_box_verified17_contains (r : Fin 17) :
    ((if r.val < 13 then normalizedOuterCompletedPolynomialBox r.val
      else normalizedOuterCompletedPolynomialBoxVerified17 r.val)).Contains
      (normalizedOuterCompletedJet17 r.val) := by
  by_cases hr : r.val < 13
  · simp [hr]
    rw [normalizedOuterCompletedJet17_eq_old ⟨r.val, hr⟩]
    exact C3CofactorCorrelation.normalized_outer_completed_box_contains ⟨r.val, hr⟩
  · simp [hr]
    rw [normalized_outer_completed_jet_eq_polynomial17 r]
    exact normalized_outer_completed_polynomial_box_verified17_contains r

def normalizedCompletedReferenceBoxVerified80 (n : ℕ) : Box :=
  exactRangeSumBox (fun k =>
    (tightHead80JetBoxCached k).mul
      (if n-k < 13 then normalizedOuterCompletedPolynomialBox (n-k)
        else normalizedOuterCompletedPolynomialBoxVerified17 (n-k))) n

theorem normalized_completed_reference_box_verified80_contains (r : Fin 17) :
    (normalizedCompletedReferenceBoxVerified80 r.val).Contains
      (normalizedCompletedReferenceJet80 r.val) := by
  unfold normalizedCompletedReferenceBoxVerified80 normalizedCompletedReferenceJet80
    convolution
  apply exact_range_sum_box_contains
  intro k hk
  have hhead := tight_head80_jet_box_cached k
  have hn : r.val-k < 17 := by
    have hr := r.isLt
    omega
  have houter := normalized_outer_completed_box_verified17_contains ⟨r.val-k, hn⟩
  by_cases hlow : r.val-k < 13
  · simpa [hlow] using Box.mul_contains hhead houter
  · simpa [hlow] using Box.mul_contains hhead houter

end
end C3ShiftedFourth
