import SourceBoxes
import SourceIntegral

/-! Finite quadrature plus three retained infinite tails and the infinite
mode remainder. No source component is replaced by its finite truncation. -/
namespace CarryIntegralCertificate
open CarrySelfAdjointOperator Real Set Filter MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
attribute [local irreducible] Box.Mem finiteModeBox tailModeBox fullModeBox fullThetaMomentBox

theorem mem_gridBox (j grid : ℕ) : (gridBox j grid).Mem ((j:ℝ)/(grid:ℝ)) := by
  simpa only [gridBox,Int.cast_natCast] using mem_rat j grid

theorem mem_finiteModeBox (m n p grid count : ℕ) (hn : n < 16) (hgrid : 0 < grid) :
    (finiteModeBox m n p grid count).Mem
      (∫ u in (0:ℝ)..((count:ℝ)/(grid:ℝ)), u^p*thetaMode m u) := by
  unfold finiteModeBox
  have hg : (0:ℝ) < (grid:ℝ) := by exact_mod_cast hgrid
  have h := mem_sum _ (fun j => ∫ u in ((j:ℝ)/(grid:ℝ))..(((j+1:ℕ):ℝ)/(grid:ℝ)),
    u^p*thetaMode m u) count (fun j _ =>
      mem_cellBox m n p hn (mem_gridBox j grid) (mem_gridBox (j+1) grid)
        (by positivity) (by push_cast; exact div_lt_div_of_pos_right (by linarith) hg))
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (f := fun u => u^p*thetaMode m u) (a := fun j : ℕ => (j:ℝ)/(grid:ℝ)) (n := count)
    (fun _ _ => ((continuous_id.pow p).mul ((contDiff_thetaMode m 1).continuous)).intervalIntegrable _ _)
  rw [he] at h
  simpa only [Nat.cast_zero,zero_div] using h

theorem mem_decayBox (m p : ℕ) {L : Box} {x : ℝ} (hx : L.Mem x) :
    (decayBox m p L).Mem (2*thetaArgument m x-1/2-(p:ℝ)/x) := by
  have h := mem_add (mem_add (mem_mul (mem_point 2) (mem_argumentBox m hx))
    (mem_neg (mem_rat 1 2))) (mem_neg (mem_div (mem_point p) hx))
  simpa only [decayBox,Int.cast_one,Int.cast_ofNat,Int.cast_natCast,sub_eq_add_neg] using h

theorem mem_tailModeBox (m p : ℕ) {L : Box} {x : ℝ} (hx : L.Mem x) (hx0 : 0 < x)
    (hd : 0 < 2*thetaArgument m x-1/2-(p:ℝ)/x) :
    (tailModeBox m p L).Mem (∫ u in Ioi x, u^p*thetaMode m u) := by
  unfold tailModeBox
  have hb := thetaMode_weighted_tail_bound m p hx0 hd
  have h := mem_div (mem_mul (mem_modeBox m hx) (mem_pow hx p)) (mem_decayBox m p hx)
  apply mem_outer (mem_point 0) h
  · simpa only [Int.cast_zero] using hb.1
  · exact hb.2

theorem mem_fullModeBox (m n p grid count : ℕ) (hn : n < 16) (hgrid : 0 < grid)
    (hc : 0 < (count:ℝ)/(grid:ℝ))
    (hd : 0 < 2*thetaArgument m ((count:ℝ)/(grid:ℝ))-1/2-(p:ℝ)/((count:ℝ)/(grid:ℝ))) :
    (fullModeBox m n p grid count).Mem (∫ u in Ioi 0, u^p*thetaMode m u) := by
  unfold fullModeBox
  have h := mem_add (mem_finiteModeBox m n p grid count hn hgrid)
    (mem_tailModeBox m p (mem_gridBox count grid) hc hd)
  have hi := integrableOn_weighted_thetaMode m p
  have ht := hi.mono_set (Ioi_subset_Ioi hc.le)
  have he := intervalIntegral.integral_interval_add_Ioi hi ht
  rw [he] at h
  exact h

/-- The same three cutoffs and order sixteen as the analytic certificate. -/
theorem thetaArgument_coarse_lower (m : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    3*((m+1:ℕ):ℝ)^2*(1+2*L) ≤ thetaArgument m L := by
  unfold thetaArgument
  gcongr
  · exact Real.pi_gt_three.le
  · linarith [Real.add_one_le_exp (2*L)]

theorem mem_fullThetaMomentBox (p : ℕ) (hp : p ≤ 18) :
    (fullThetaMomentBox p).Mem (completedNativeThetaTailMoment p) := by
  unfold fullThetaMomentBox
  have hpR : (p:ℝ) ≤ 18 := by exact_mod_cast hp
  have hd0 := thetaArgument_coarse_lower 0 (by norm_num : (0:ℝ) ≤ 96/64)
  have hd1 := thetaArgument_coarse_lower 1 (by norm_num : (0:ℝ) ≤ 64/64)
  have hd2 := thetaArgument_coarse_lower 2 (by norm_num : (0:ℝ) ≤ 48/64)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hd0 hd1 hd2
  have hm0 := mem_fullModeBox 0 15 p 64 96 (by omega) (by omega) (by norm_num) (by nlinarith only [hd0,hpR])
  have hm1 := mem_fullModeBox 1 15 p 64 64 (by omega) (by omega) (by norm_num) (by nlinarith only [hd1,hpR])
  have hm2 := mem_fullModeBox 2 15 p 64 48 (by omega) (by omega) (by norm_num) (by nlinarith only [hd2,hpR])
  have hb := integral_weightedOmittedModes_bounds p
  have hr := mem_outer (mem_point 0) (mem_rat p.factorial ((10:ℤ)^20*95^(p+1)))
    (by simpa only [Int.cast_zero] using hb.1) (by
      simpa only [Int.cast_natCast,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using hb.2)
  have h := mem_add (mem_add (mem_add hm0 hm1) hm2) hr
  rw [completedNativeThetaTailMoment_eq_three_and_remainder p]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    Nat.reduceAdd]
  exact h

end CarryIntegralCertificate
