import GammaBounds

/-! A quantitative nonvanishing certificate for the complete native signal.
The complex continuation sums the original complete cells, never a cutoff. -/
namespace CarryReadoutBounds
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryFourthTail CarryMaterialParts
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def complexSignal (w : ℂ) : ℂ := 1+∑' k, complexCell k w

theorem reciprocal_cells_summable : Summable (fun k : ℕ => (1:ℝ)/((4*k+3:ℕ):ℝ)^2) :=
  (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ))).comp_injective
    (by intro i j h; dsimp at h; omega)

theorem reciprocal_cells_bound :
    ∑' k : ℕ, (1:ℝ)/((4*k+3:ℕ):ℝ)^2 ≤ 7/36 := by
  have ht := reciprocal_cell_tail 1 (by norm_num)
  have hs := reciprocal_cells_summable.sum_add_tsum_nat_add 1
  norm_num only [Finset.sum_range_one, mul_zero, zero_add] at hs
  rw [← hs]
  norm_num at ht ⊢
  linarith

theorem signal_deviation_bound (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖complexSignal w-1‖ ≤ 7/18 := by
  have hs := reciprocal_cells_summable.mul_left 2
  have hc : Summable (fun k => ‖complexCell k w‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      simpa only [mul_one_div] using complex_cell_bound k w hw) hs
  simp only [complexSignal, add_sub_cancel_left]
  apply (norm_tsum_le_tsum_norm hc).trans
  calc
    ∑' k, ‖complexCell k w‖ ≤ ∑' k, 2*((1:ℝ)/((4*k+3:ℕ):ℝ)^2) :=
      hc.tsum_le_tsum (fun k => by simpa only [mul_one_div] using complex_cell_bound k w hw) hs
    _ = 2*(∑' k, (1:ℝ)/((4*k+3:ℕ):ℝ)^2) := tsum_mul_left
    _ ≤ 7/18 := by linarith [reciprocal_cells_bound]

theorem signal_norm_lower (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    (1/2:ℝ) ≤ ‖complexSignal w‖ := by
  have h := signal_deviation_bound w hw
  have hn := norm_sub_le (complexSignal w) 1
  have ht := norm_sub_le (complexSignal w) (complexSignal w-1)
  norm_num at ht
  linarith

theorem signal_nonzero (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) : complexSignal w ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (signal_norm_lower w hw))

theorem inverse_signal_bound (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖(complexSignal w)⁻¹‖ ≤ 2 := by
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num) (signal_norm_lower w hw))).2
    (by linarith [signal_norm_lower w hw])

theorem complex_signal_differentiableOn :
    DifferentiableOn ℂ complexSignal (Metric.ball 0 (1/2:ℝ)) := by
  have hs := reciprocal_cells_summable.mul_left 2
  have hd := Complex.differentiableOn_tsum_of_summable_norm (U:=Metric.ball (0:ℂ) (1/2:ℝ)) hs
    (fun k => (complex_cell_entire k).differentiableOn) Metric.isOpen_ball
    (fun k w hw => by
      apply (complex_cell_bound k w ?_).trans_eq (mul_one_div _ _).symm
      exact (show ‖w‖ < (1/2:ℝ) by simpa only [Metric.mem_ball, dist_zero_right] using hw).le)
  exact (differentiable_const (1:ℂ)).differentiableOn.add hd

theorem complex_signal_real (t : ℝ) : complexSignal (t:ℂ) = baseTwoCriticalCompleteSignal t := by
  simp only [complexSignal, complex_cell_real, baseTwoCriticalCompleteSignal,
    criticalMaterialSample_one]

theorem normalized_cauchy {f : ℂ → ℂ} {r C : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (Metric.ball 0 r))
    (hb : ∀ w, ‖w‖ = r → ‖f w‖ ≤ C) (m : ℕ) :
    ‖complexJet m f‖ ≤ C/r^m := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c:=(0:ℂ)) (f:=f) m hr hf (fun w hw => hb w (by simpa only [Metric.mem_sphere, dist_zero_right] using hw))
  rw [complexJet, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < m.factorial)).2
  have he : C/r^m*(m.factorial:ℝ) = m.factorial*C/r^m := by ring
  rw [he]
  exact h

end
end CarryReadoutBounds
