import LeftJetMagnitudeHigh

namespace C3CofactorCorrelation
open CarryC3Boxes CarryC3Tail CarryC3Gamma
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

theorem left_jet48_correlated_box_abs_bound (r : Fin 13) :
    -leftJet48MagnitudeBound r ≤ (leftJet48CorrelatedBox r).lo ∧
      (leftJet48CorrelatedBox r).hi ≤ leftJet48MagnitudeBound r := by
  by_cases hlo : r.val < 7
  · have hb := left_jet48_correlated_box_abs_bound_low ⟨r.val, hlo⟩
    simpa using hb
  · have hb := left_jet48_correlated_box_abs_bound_high ⟨r.val-7, by omega⟩
    simpa [Nat.sub_add_cancel (Nat.le_of_not_gt hlo)] using hb

theorem left_real_jet48_abs_bound (r : Fin 13) :
    |leftRealJet48 r.val| ≤ (leftJet48MagnitudeBound r : ℝ) := by
  have hb := left_jet48_correlated_box_abs_bound r
  have hc := left_jet48_correlated_box_contains r
  have hl : (-(leftJet48MagnitudeBound r) : ℝ) ≤
      (leftJet48CorrelatedBox r).lo := by exact_mod_cast hb.1
  have hu : (leftJet48CorrelatedBox r).hi ≤
      (leftJet48MagnitudeBound r : ℝ) := by exact_mod_cast hb.2
  rw [abs_le]
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

theorem left_real_jet48_abs_sum_le_half :
    (∑ r : Fin 13, |leftRealJet48 r.val|) ≤ (1/2:ℝ) := by
  calc
    _ ≤ ∑ r : Fin 13, (leftJet48MagnitudeBound r : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact left_real_jet48_abs_bound r
    _ ≤ (1/2:ℝ) := by
      norm_num [leftJet48MagnitudeBound, Fin.sum_univ_succ]

theorem left_gamma_replacement_allowance_le_half (r : Fin 13) :
    (∑ j ∈ Finset.range (r.val+1),
      |leftRealJet48 j| * (1/10^24:ℝ)) ≤
        (1/2:ℝ) * (1/10^24:ℝ) := by
  have hsubset : Finset.range (r.val+1) ⊆ Finset.range 13 := by
    intro j hj
    apply Finset.mem_range.mpr
    have hr := r.isLt
    have hj' := Finset.mem_range.mp hj
    omega
  have hpartial :
      (∑ j ∈ Finset.range (r.val+1), |leftRealJet48 j|) ≤
        ∑ j ∈ Finset.range 13, |leftRealJet48 j| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j hj hnot
    exact abs_nonneg _
  have hfull : (∑ j ∈ Finset.range 13, |leftRealJet48 j|) ≤ (1/2:ℝ) := by
    calc
      _ = ∑ j : Fin 13, |leftRealJet48 j.val| := by
        simpa using (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
          |leftRealJet48 j|) 13).symm
      _ ≤ (1/2:ℝ) := left_real_jet48_abs_sum_le_half
  calc
    (∑ j ∈ Finset.range (r.val+1),
        |leftRealJet48 j| * (1/10^24:ℝ)) =
      (∑ j ∈ Finset.range (r.val+1), |leftRealJet48 j|) * (1/10^24:ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ j ∈ Finset.range 13, |leftRealJet48 j|) * (1/10^24:ℝ) :=
      mul_le_mul_of_nonneg_right hpartial (by positivity)
    _ ≤ (1/2:ℝ) * (1/10^24:ℝ) :=
      mul_le_mul_of_nonneg_right hfull (by positivity)

end
end C3CofactorCorrelation
