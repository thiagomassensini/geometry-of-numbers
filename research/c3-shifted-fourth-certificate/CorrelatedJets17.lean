import M80CompletedSource
import CorrelationInterval

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets C3CofactorCorrelation
open Set Filter Topology
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

def normalizedGammaJetCrosswalk17 (r : ℕ) : ℝ :=
  if hr : r < 13 then
    C3CofactorCorrelation.normalizedGammaJet r
  else if hr : r < 17 then
    (((gammaRealReference17 ⟨r, hr⟩ : ℚ) /
      (gammaRealReference13 ⟨0, by omega⟩ : ℚ) : ℚ) : ℝ)
  else 0

def normalizedOuterCompletedJet17 (r : ℕ) : ℝ :=
  convolution (normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3))
    normalizedGammaJetCrosswalk17 r

def normalizedOuterCompletedPolynomialCoefficient17
    (q ell : ℝ) (n e : ℕ) : ℝ :=
  if e ≤ n then
    ∑ j ∈ Finset.range (n + 1),
      if e ≤ j then
        normalizedOuterBasePolynomialCoeff q ell j e * normalizedGammaJetCrosswalk17 (n-j)
      else 0
  else 0

def normalizedOuterCompletedPolynomialHorner17
    (p q ell : ℝ) (n : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (n + 1),
    normalizedOuterCompletedPolynomialCoefficient17 q ell n e * p ^ e

theorem normalizedOuterBaseJet_eq_horner17 (r : Fin 17) (p q ell : ℝ) :
    normalizedOuterBaseJet p q ell r.val =
      normalizedOuterBaseHorner p q ell r.val := by
  by_cases hlow : r.val < 13
  · exact normalizedOuterBaseJet_eq_horner ⟨r.val, hlow⟩ p q ell
  · have hcases : r.val = 13 ∨ r.val = 14 ∨ r.val = 15 ∨ r.val = 16 := by
      have hr := r.isLt
      omega
    rcases hcases with h | h | h | h
    · have he : r = ⟨13, by omega⟩ := Fin.ext h
      rw [he]
      simp [normalizedOuterBaseJet, normalizedOuterBaseHorner,
        normalizedOuterBasePolynomialCoeff, normalizedPolynomialJet,
        normalizedExponentialJet, normalizedChartReciprocal, convolution,
        reciprocalJet, Finset.sum_range_succ]
      ring
    · have he : r = ⟨14, by omega⟩ := Fin.ext h
      rw [he]
      simp [normalizedOuterBaseJet, normalizedOuterBaseHorner,
        normalizedOuterBasePolynomialCoeff, normalizedPolynomialJet,
        normalizedExponentialJet, normalizedChartReciprocal, convolution,
        reciprocalJet, Finset.sum_range_succ]
      ring
    · have he : r = ⟨15, by omega⟩ := Fin.ext h
      rw [he]
      simp [normalizedOuterBaseJet, normalizedOuterBaseHorner,
        normalizedOuterBasePolynomialCoeff, normalizedPolynomialJet,
        normalizedExponentialJet, normalizedChartReciprocal, convolution,
        reciprocalJet, Finset.sum_range_succ]
      ring
    · have he : r = ⟨16, by omega⟩ := Fin.ext h
      rw [he]
      simp [normalizedOuterBaseJet, normalizedOuterBaseHorner,
        normalizedOuterBasePolynomialCoeff, normalizedPolynomialJet,
        normalizedExponentialJet, normalizedChartReciprocal, convolution,
        reciprocalJet, Finset.sum_range_succ]
      ring

theorem normalizedOuterCompletedJet17_eq_old (r : Fin 13) :
    normalizedOuterCompletedJet17 r.val =
      C3CofactorCorrelation.normalizedOuterCompletedJet48 r.val := by
  unfold normalizedOuterCompletedJet17 C3CofactorCorrelation.normalizedOuterCompletedJet48
    convolution
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ r.val := by
    have hj' := Finset.mem_range.mp hj
    omega
  have hgj : r.val-j < 13 := by
    have hr := r.isLt
    omega
  simp [normalizedGammaJetCrosswalk17, hgj]

theorem normalizedOuterCompletedPolynomialHorner17_eq_old (r : Fin 13) :
    normalizedOuterCompletedPolynomialHorner17 (Real.log Real.pi)
      chartRatio (Real.log 3) r.val =
      C3CofactorCorrelation.normalizedOuterCompletedPolynomialHorner
        (Real.log Real.pi) chartRatio (Real.log 3) r.val := by
  unfold normalizedOuterCompletedPolynomialHorner17
    C3CofactorCorrelation.normalizedOuterCompletedPolynomialHorner
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  unfold normalizedOuterCompletedPolynomialCoefficient17
    C3CofactorCorrelation.normalizedOuterCompletedPolynomialCoefficient
  by_cases hen : e ≤ r.val
  · simp only [if_pos hen]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hej : e ≤ j
    · simp only [if_pos hej]
      have hjn : r.val-j < 13 := by
        have hmem := Finset.mem_range.mp hj
        have hr := r.isLt
        omega
      simp [normalizedGammaJetCrosswalk17, hjn]
    · simp [hej]
  · simp [hen]

theorem normalized_outer_completed_jet_eq_polynomial17 (r : Fin 17) :
    normalizedOuterCompletedJet17 r.val =
      normalizedOuterCompletedPolynomialHorner17 (Real.log Real.pi)
        chartRatio (Real.log 3) r.val := by
  by_cases hlow : r.val < 13
  · let q : Fin 13 := ⟨r.val, hlow⟩
    rw [normalizedOuterCompletedJet17_eq_old q,
      normalizedOuterCompletedPolynomialHorner17_eq_old q]
    exact C3CofactorCorrelation.normalized_outer_completed_jet_eq_polynomial q
  · have hcases : r.val = 13 ∨ r.val = 14 ∨ r.val = 15 ∨ r.val = 16 := by
      have hr := r.isLt
      omega
    rcases hcases with h | h | h | h
    · have he : r = ⟨13, by omega⟩ := Fin.ext h
      rw [he]
      have hbase (g : ℕ) (hg : g ∈ Finset.range (13 + 1)) :
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) g =
            normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3) g := by
        have hlt : g < 17 := by have hle := Finset.mem_range.mp hg; omega
        exact normalizedOuterBaseJet_eq_horner17 ⟨g, hlt⟩ _ _ _
      unfold normalizedOuterCompletedJet17 normalizedOuterCompletedPolynomialHorner17
        convolution
        normalizedOuterCompletedPolynomialCoefficient17
      rw [show (∑ g ∈ Finset.range (13 + 1),
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) g *
            normalizedGammaJetCrosswalk17 (13-g)) =
          ∑ g ∈ Finset.range (13 + 1),
            normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3) g *
              normalizedGammaJetCrosswalk17 (13-g) by
            apply Finset.sum_congr rfl
            intro g hg
            rw [hbase g hg]]
      simp [normalizedOuterBaseHorner,
        normalizedGammaJetCrosswalk17, Finset.sum_range_succ]
      ring
    · have he : r = ⟨14, by omega⟩ := Fin.ext h
      rw [he]
      have hbase (g : ℕ) (hg : g ∈ Finset.range (14 + 1)) :
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) g =
            normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3) g := by
        have hlt : g < 17 := by have hle := Finset.mem_range.mp hg; omega
        exact normalizedOuterBaseJet_eq_horner17 ⟨g, hlt⟩ _ _ _
      unfold normalizedOuterCompletedJet17 normalizedOuterCompletedPolynomialHorner17
        convolution
        normalizedOuterCompletedPolynomialCoefficient17
      rw [show (∑ g ∈ Finset.range (14 + 1),
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) g *
            normalizedGammaJetCrosswalk17 (14-g)) =
          ∑ g ∈ Finset.range (14 + 1),
            normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3) g *
              normalizedGammaJetCrosswalk17 (14-g) by
            apply Finset.sum_congr rfl
            intro g hg
            rw [hbase g hg]]
      simp [normalizedOuterBaseHorner,
        normalizedGammaJetCrosswalk17, Finset.sum_range_succ]
      ring
    · have he : r = ⟨15, by omega⟩ := Fin.ext h
      rw [he]
      have hbase (g : ℕ) (hg : g ∈ Finset.range (15 + 1)) :
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) g =
            normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3) g := by
        have hlt : g < 17 := by have hle := Finset.mem_range.mp hg; omega
        exact normalizedOuterBaseJet_eq_horner17 ⟨g, hlt⟩ _ _ _
      unfold normalizedOuterCompletedJet17 normalizedOuterCompletedPolynomialHorner17
        convolution
        normalizedOuterCompletedPolynomialCoefficient17
      rw [show (∑ g ∈ Finset.range (15 + 1),
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) g *
            normalizedGammaJetCrosswalk17 (15-g)) =
          ∑ g ∈ Finset.range (15 + 1),
            normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3) g *
              normalizedGammaJetCrosswalk17 (15-g) by
            apply Finset.sum_congr rfl
            intro g hg
            rw [hbase g hg]]
      simp [normalizedOuterBaseHorner,
        normalizedGammaJetCrosswalk17, Finset.sum_range_succ]
      ring
    · have he : r = ⟨16, by omega⟩ := Fin.ext h
      rw [he]
      have hbase (g : ℕ) (hg : g ∈ Finset.range (16 + 1)) :
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) g =
            normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3) g := by
        have hlt : g < 17 := by have hle := Finset.mem_range.mp hg; omega
        exact normalizedOuterBaseJet_eq_horner17 ⟨g, hlt⟩ _ _ _
      unfold normalizedOuterCompletedJet17 normalizedOuterCompletedPolynomialHorner17
        convolution
        normalizedOuterCompletedPolynomialCoefficient17
      rw [show (∑ g ∈ Finset.range (16 + 1),
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) g *
            normalizedGammaJetCrosswalk17 (16-g)) =
          ∑ g ∈ Finset.range (16 + 1),
            normalizedOuterBaseHorner (Real.log Real.pi) chartRatio (Real.log 3) g *
              normalizedGammaJetCrosswalk17 (16-g) by
            apply Finset.sum_congr rfl
            intro g hg
            rw [hbase g hg]]
      simp [normalizedOuterBaseHorner,
        normalizedGammaJetCrosswalk17, Finset.sum_range_succ]
      ring

def normalizedGammaCoefficientQ17 (r : ℕ) : ℚ :=
  if hr : r < 13 then C3CofactorCorrelation.normalizedGammaCoefficientQ r
  else if hr : r < 17 then
    gammaRealReference17 ⟨r, hr⟩ / gammaRealReference13 ⟨0, by omega⟩
  else 0

theorem normalized_gamma_coefficient_point17 (r : ℕ) :
    (Box.point (normalizedGammaCoefficientQ17 r)).Contains
      (normalizedGammaJetCrosswalk17 r) := by
  by_cases hr : r < 17
  · by_cases hl : r < 13
    · simpa [normalizedGammaCoefficientQ17, normalizedGammaJetCrosswalk17, hl] using
        C3CofactorCorrelation.normalized_gamma_coefficient_point r
    · have hcast : ((normalizedGammaCoefficientQ17 r : ℚ) : ℝ) =
          normalizedGammaJetCrosswalk17 r := by
        simp [normalizedGammaCoefficientQ17, normalizedGammaJetCrosswalk17, hr, hl]
      rw [← hcast]
      exact Box.point_contains _
  · have hl : ¬r < 13 := by omega
    simp [normalizedGammaCoefficientQ17, normalizedGammaJetCrosswalk17, hr, hl,
      Box.point, Box.Contains]

def normalizedOuterCompletedPolynomialCoefficientBox17
    (n e : ℕ) : Box :=
  if e ≤ n then
    exactRangeSumBox (fun j =>
      if e ≤ j then
        (normalizedOuterBasePolynomialCoefficientBox j e).mul
          (Box.point (normalizedGammaCoefficientQ17 (n-j)))
      else Box.point 0) n
  else Box.point 0

theorem normalized_outer_completed_polynomial_coefficient_box_contains17
    (n e : ℕ) :
    (normalizedOuterCompletedPolynomialCoefficientBox17 n e).Contains
      (normalizedOuterCompletedPolynomialCoefficient17 chartRatio (Real.log 3) n e) := by
  by_cases he : e ≤ n
  · simp only [normalizedOuterCompletedPolynomialCoefficientBox17, if_pos he]
    unfold normalizedOuterCompletedPolynomialCoefficient17
    simp only [if_pos he]
    apply exact_range_sum_box_contains
    intro j hj
    by_cases hj' : e ≤ j
    · have hterm := Box.mul_contains
        (normalized_outer_base_polynomial_coefficient_box_contains j e)
        (normalized_gamma_coefficient_point17 (n-j))
      simpa [hj'] using hterm
    · simp [hj', Box.point, Box.Contains]
  · simp only [normalizedOuterCompletedPolynomialCoefficientBox17, if_neg he]
    unfold normalizedOuterCompletedPolynomialCoefficient17
    simp only [if_neg he]
    simp [Box.point, Box.Contains]

def normalizedOuterCompletedPolynomialBoxCalc17 (n : ℕ) : Box :=
  exactRangeSumBox (fun e =>
    (normalizedOuterCompletedPolynomialCoefficientBox17 n e).mul
      (powBoxExact piLogReference e)) n

theorem normalized_outer_completed_polynomial_box_contains17 (n : ℕ) :
    (normalizedOuterCompletedPolynomialBoxCalc17 n).Contains
      (normalizedOuterCompletedPolynomialHorner17 (Real.log Real.pi)
        chartRatio (Real.log 3) n) := by
  unfold normalizedOuterCompletedPolynomialBoxCalc17
    normalizedOuterCompletedPolynomialHorner17
  apply exact_range_sum_box_contains
  intro e he
  exact Box.mul_contains
    (normalized_outer_completed_polynomial_coefficient_box_contains17 n e)
    (powBoxExact_contains pi_log_reference_contains e)

theorem normalized_outer_completed_box_contains17 (r : Fin 17) :
    ((if r.val < 13 then normalizedOuterCompletedPolynomialBox r.val
      else normalizedOuterCompletedPolynomialBoxCalc17 r.val)).Contains
      (normalizedOuterCompletedJet17 r.val) := by
  by_cases hr : r.val < 13
  · simp [hr]
    rw [normalizedOuterCompletedJet17_eq_old ⟨r.val, hr⟩]
    exact C3CofactorCorrelation.normalized_outer_completed_box_contains ⟨r.val, hr⟩
  · simp [hr]
    rw [normalized_outer_completed_jet_eq_polynomial17 r]
    exact normalized_outer_completed_polynomial_box_contains17 r.val

def normalizedCompletedReferenceJet80 (n : ℕ) : ℝ :=
  convolution head80RealJet normalizedOuterCompletedJet17 n

def normalizedCompletedReferenceBox80 (n : ℕ) : Box :=
  exactRangeSumBox (fun k =>
    (tightHead80JetBox k).mul
      (if n-k < 13 then normalizedOuterCompletedPolynomialBox (n-k)
        else normalizedOuterCompletedPolynomialBoxCalc17 (n-k))) n

theorem normalized_completed_reference_box_contains80 (r : Fin 17) :
    (normalizedCompletedReferenceBox80 r.val).Contains
      (normalizedCompletedReferenceJet80 r.val) := by
  unfold normalizedCompletedReferenceBox80 normalizedCompletedReferenceJet80
    convolution
  apply exact_range_sum_box_contains
  intro k hk
  have hhead := tight_head80_jet_box k
  have hn : r.val-k < 17 := by
    have hr := r.isLt
    omega
  have houter := normalized_outer_completed_box_contains17 ⟨r.val-k, hn⟩
  simpa using Box.mul_contains hhead houter


end
end C3ShiftedFourth
