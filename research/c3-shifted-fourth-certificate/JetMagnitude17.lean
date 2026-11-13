import HighCoefficientBoxes17
import SourceTransport17
import LeftJetMagnitude

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets C3CofactorCorrelation
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- The verified order-17 outer multiplier interval, assembled from the
coefficientwise polynomial boxes. -/
def normalizedOuterBaseBoxVerified17 (n : ℕ) : Box :=
  exactRangeSumBox (fun e =>
    (normalizedOuterBasePolynomialCoefficientBoxVerified17 n e).mul
      (powBoxExact piLogReference e)) n

theorem normalized_outer_base_box_verified17_contains (r : Fin 17) :
    (normalizedOuterBaseBoxVerified17 r.val).Contains
      (normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) r.val) := by
  rw [normalizedOuterBaseJet_eq_horner17 r]
  unfold normalizedOuterBaseBoxVerified17 normalizedOuterBaseHorner
  apply exact_range_sum_box_contains
  intro e he
  exact Box.mul_contains
    (normalized_outer_base_polynomial_coefficient_box_verified17_contains
      r.val e r.isLt)
    (powBoxExact_contains pi_log_reference_contains e)

def normalizedOuterBaseMagnitudeBound17 (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | 1 => 21/10
  | 2 => 1/100
  | 3 => 11/100
  | 4 => 1/100
  | 5 => 1/100
  | 6 => 1/1000
  | 7 => 1/1000
  | 8 => 1/10000
  | 9 => 1/100000
  | 10 => 1/100000
  | 11 => 1/1000000
  | 12 => 1/10000000
  | 13 => 1/100000000
  | 14 => 1/100000000
  | 15 => 1/1000000000
  | 16 => 1/10000000000
  | _ => 0

theorem normalized_outer_base_box_magnitude17 (r : Fin 17) :
    -(normalizedOuterBaseMagnitudeBound17 r.val) ≤
        (normalizedOuterBaseBoxVerified17 r.val).lo ∧
      (normalizedOuterBaseBoxVerified17 r.val).hi ≤
        normalizedOuterBaseMagnitudeBound17 r.val := by
  fin_cases r <;> decide +kernel

theorem normalized_outer_base_jet_abs_bound17 (r : Fin 17) :
    |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) r.val| ≤
      (normalizedOuterBaseMagnitudeBound17 r.val : ℝ) := by
  have hb := normalized_outer_base_box_magnitude17 r
  have hc := normalized_outer_base_box_verified17_contains r
  rw [abs_le]
  constructor
  · have hl : -(normalizedOuterBaseMagnitudeBound17 r.val : ℝ) ≤
      (normalizedOuterBaseBoxVerified17 r.val).lo := by exact_mod_cast hb.1
    linarith [hc.1]
  · have hu : (normalizedOuterBaseBoxVerified17 r.val).hi ≤
      (normalizedOuterBaseMagnitudeBound17 r.val : ℝ) := by exact_mod_cast hb.2
    linarith [hc.2]

theorem head80_jet_abs_bound17 (r : Fin 17) :
    |head80RealJet r.val| ≤ (11/10:ℝ) := by
  let headBox : Box := (gridM80HeadReference17 r).toBox
  have hb : -(11/10:ℚ) ≤ headBox.lo ∧ headBox.hi ≤ 11/10 := by
    dsimp [headBox]
    fin_cases r <;> decide +kernel
  have hc := grid_m80_head_box17_contains r
  rw [grid_m80_head_box17_eq_reference r] at hc
  rw [abs_le]
  constructor
  · have hl : (-(11/10:ℚ) : ℝ) ≤ (headBox.lo : ℝ) := by
      simpa using Rat.cast_mono (K := ℝ) hb.1
    linarith [hc.1, hl]
  · have hu : (headBox.hi : ℝ) ≤ ((11/10:ℚ) : ℝ) := by
      exact Rat.cast_mono (K := ℝ) hb.2
    linarith [hc.2, hu]

theorem normalized_outer_base_magnitude_sum17 :
    (∑ r : Fin 17, normalizedOuterBaseMagnitudeBound17 r.val) ≤ 4 := by
  norm_num [normalizedOuterBaseMagnitudeBound17, Fin.sum_univ_succ]

theorem convolution_abs_le_sum_abs (a b : ℕ → ℝ) (n : ℕ) :
    |convolution a b n| ≤
      ∑ j ∈ Finset.range (n+1), |a j| * |b (n-j)| := by
  unfold convolution
  calc
    |∑ j ∈ Finset.range (n+1), a j * b (n-j)| ≤
        ∑ j ∈ Finset.range (n+1), |a j * b (n-j)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (n+1), |a j| * |b (n-j)| := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [abs_mul]

theorem left_scale_abs_bound17 :
    |C3CofactorCorrelation.leftJet48Scale| ≤ (1/5:ℝ) := by
  let scaleBox : Box := C3CofactorCorrelation.leftJet48ScaleBox
  have hs := C3CofactorCorrelation.left_jet48_scale_box_contains
  have hb : -(1/5:ℚ) ≤ scaleBox.lo ∧ scaleBox.hi ≤ 1/5 := by
    dsimp [scaleBox, C3CofactorCorrelation.leftJet48ScaleBox]
    decide +kernel
  rw [abs_le]
  constructor
  · have hl : (-(1/5:ℚ) : ℝ) ≤ (scaleBox.lo : ℝ) := by
      simpa using Rat.cast_mono (K := ℝ) hb.1
    linarith [hs.1, hl]
  · have hu : (scaleBox.hi : ℝ) ≤ ((1/5:ℚ) : ℝ) := by
      exact Rat.cast_mono (K := ℝ) hb.2
    linarith [hs.2, hu]

theorem head80_jet_one_abs_bound17 : |head80RealJet 1| ≤ (1/10:ℝ) := by
  let headBox : Box := (gridM80HeadReference17 ⟨1, by omega⟩).toBox
  have hb : -(1/10:ℚ) ≤ headBox.lo ∧ headBox.hi ≤ 1/10 := by
    dsimp [headBox]
    decide +kernel
  have hc := grid_m80_head_box17_contains ⟨1, by omega⟩
  rw [grid_m80_head_box17_eq_reference ⟨1, by omega⟩] at hc
  rw [abs_le]
  constructor
  · have hl : (-(1/10:ℚ) : ℝ) ≤ (headBox.lo : ℝ) := by
      simpa using Rat.cast_mono (K := ℝ) hb.1
    linarith [hc.1, hl]
  · have hu : (headBox.hi : ℝ) ≤ ((1/10:ℚ) : ℝ) := by
      exact Rat.cast_mono (K := ℝ) hb.2
    linarith [hc.2, hu]

theorem normalized_outer_base_jet_zero_eq :
    normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 0 = 1 := by
  rw [normalizedOuterBaseJet_eq_horner17 ⟨0, by omega⟩]
  simp [normalizedOuterBaseHorner, normalizedOuterBasePolynomialCoeff,
    normalizedPolynomialJet, normalizedChartDenominator,
    normalizedChartReciprocal, reciprocalJet]

theorem normalized_left_jet80_zero_eq :
    normalizedLeftJet80 0 =
      normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 0 *
        head80RealJet 0 := by
  simp [normalizedLeftJet80, convolution]

theorem normalized_left_jet80_one_eq :
    normalizedLeftJet80 1 =
      normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 0 *
          head80RealJet 1 +
        normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 1 *
          head80RealJet 0 := by
  simp [normalizedLeftJet80, convolution, Finset.sum_range_succ]

theorem left_real_jet_zero_abs_bound17 : |leftRealJet80 0| ≤ (1/4:ℝ) := by
  rw [left_real_jet80_eq_normalized, normalized_left_jet80_zero_eq,
    normalized_outer_base_jet_zero_eq]
  simp only [one_mul, abs_mul]
  have hh := head80_jet_abs_bound17 ⟨0, by omega⟩
  calc
    |C3CofactorCorrelation.leftJet48Scale| * |head80RealJet 0| ≤
        |C3CofactorCorrelation.leftJet48Scale| * (11/10:ℝ) :=
      mul_le_mul_of_nonneg_left hh (abs_nonneg _)
    _ ≤ (1/5:ℝ) * (11/10:ℝ) :=
      mul_le_mul_of_nonneg_right left_scale_abs_bound17 (by norm_num)
    _ ≤ 1/4 := by norm_num

theorem left_real_jet_one_abs_bound17 : |leftRealJet80 1| ≤ (1/2:ℝ) := by
  rw [left_real_jet80_eq_normalized, normalized_left_jet80_one_eq,
    normalized_outer_base_jet_zero_eq]
  simp only [one_mul, abs_mul]
  have hh0 := head80_jet_abs_bound17 ⟨0, by omega⟩
  have hh1 := head80_jet_one_abs_bound17
  have ho1 := normalized_outer_base_jet_abs_bound17 ⟨1, by omega⟩
  have ho1' : |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 1| ≤
      (21/10:ℝ) := by
    simpa [normalizedOuterBaseMagnitudeBound17] using ho1
  have hterms : |head80RealJet 1| +
      |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 1| *
        |head80RealJet 0| ≤ (1/10:ℝ) + (21/10:ℝ) * (11/10:ℝ) := by
    exact add_le_add hh1 (mul_le_mul ho1' hh0 (abs_nonneg _) (by norm_num))
  have htriangle :
      |head80RealJet 1 +
        normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 1 *
          head80RealJet 0| ≤
        |head80RealJet 1| +
          |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 1| *
            |head80RealJet 0| := by
    calc
      _ ≤ |head80RealJet 1| +
          |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 1 *
            head80RealJet 0| := abs_add_le _ _
      _ = _ := by rw [abs_mul]
  calc
    |C3CofactorCorrelation.leftJet48Scale| *
        |head80RealJet 1 +
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 1 *
            head80RealJet 0| ≤
      |C3CofactorCorrelation.leftJet48Scale| *
        (|head80RealJet 1| +
          |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) 1| *
            |head80RealJet 0|) :=
        mul_le_mul_of_nonneg_left htriangle (abs_nonneg _)
    _ ≤ (1/5:ℝ) * ((1/10:ℝ) + (21/10:ℝ) * (11/10:ℝ)) :=
        mul_le_mul left_scale_abs_bound17 hterms (by positivity) (by norm_num)
    _ ≤ 1/2 := by norm_num

theorem left_real_jet_abs_bound17 (r : Fin 17) :
    |leftRealJet80 r.val| ≤ 1 := by
  have hcross := left_real_jet80_eq_normalized r.val
  have hconv := convolution_abs_le_sum_abs
    (normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3))
    head80RealJet r.val
  have hterms :
      (∑ j ∈ Finset.range (r.val+1),
        |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) j| *
          |head80RealJet (r.val-j)|) ≤ (11/10:ℝ) * 4 := by
    have hsum :
        (∑ j ∈ Finset.range (r.val+1),
          |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) j|) ≤ 4 := by
      have hpartial :
          (∑ j ∈ Finset.range (r.val+1),
            |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) j|) ≤
            ∑ j ∈ Finset.range 17,
              |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) j| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          apply Finset.mem_range.mpr
          have hr := r.isLt
          have hj' := Finset.mem_range.mp hj
          omega
        · intro j hj hnot
          exact abs_nonneg _
      have hfull :
          (∑ j ∈ Finset.range 17,
            |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) j|) ≤ 4 := by
        calc
          _ = ∑ j : Fin 17,
              |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) j.val| := by
                exact (Fin.sum_univ_eq_sum_range _ 17).symm
          _ ≤ ∑ j : Fin 17, (normalizedOuterBaseMagnitudeBound17 j.val : ℝ) := by
                apply Finset.sum_le_sum
                intro j hj
                exact normalized_outer_base_jet_abs_bound17 j
          _ ≤ 4 := by exact_mod_cast normalized_outer_base_magnitude_sum17
      exact hpartial.trans hfull
    calc
      _ ≤ ∑ j ∈ Finset.range (r.val+1),
          |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) j| * (11/10:ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (head80_jet_abs_bound17 ⟨r.val-j, by
              have hr := r.isLt
              have hj' := Finset.mem_range.mp hj
              omega⟩) (abs_nonneg _)
      _ = (∑ j ∈ Finset.range (r.val+1),
          |normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) j|) * (11/10:ℝ) := by
            rw [Finset.sum_mul]
      _ ≤ 4 * (11/10:ℝ) := mul_le_mul_of_nonneg_right hsum (by norm_num)
      _ = (11/10:ℝ) * 4 := by ring
  have hnorm : |normalizedLeftJet80 r.val| ≤ (11/10:ℝ) * 4 :=
    hconv.trans hterms
  have hscale' := mul_le_mul left_scale_abs_bound17 hnorm (abs_nonneg _)
    (by norm_num : (0:ℝ) ≤ (1/5:ℝ))
  have hglobal : |leftRealJet80 r.val| ≤ (1/5:ℝ) * ((11/10:ℝ) * 4) := by
    rw [hcross, abs_mul]
    nlinarith [hscale']
  by_cases h0 : r.val = 0
  · have hr : r = ⟨0, by omega⟩ := Fin.ext h0
    rw [hr]
    exact left_real_jet_zero_abs_bound17.trans (by norm_num)
  · by_cases h1 : r.val = 1
    · have hr : r = ⟨1, by omega⟩ := Fin.ext h1
      rw [hr]
      simpa using (left_real_jet_one_abs_bound17.trans (by norm_num : (1/2:ℝ) ≤ 1))
    · have hr : 2 ≤ r.val := by omega
      have hglobal' : (1/5:ℝ) * ((11/10:ℝ) * 4) ≤ 1 := by norm_num
      exact hglobal.trans hglobal'

#print axioms left_real_jet_abs_bound17

end
end C3ShiftedFourth
