import ExactSourceProgram
import FullSourceBoxes
import NodeCacheEquivalence

namespace CarryIntegralCertificate
open CarrySelfAdjointOperator Real Set Filter MeasureTheory
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
attribute [local irreducible] Box.Mem exactFiniteModeBox exactFullModeBox exactFullThetaMomentBox

theorem mem_cachedArgumentNode (m : Fin 3) (j : ℕ) (hj : j ≤ thetaCertificateCellCount m.val) :
    (cachedArgumentNode m.val j).Mem (thetaArgument m.val ((j:ℝ)/64)) := by
  have h := mem_argumentBox m.val (mem_gridBox j 64)
  rw [argumentBox_eq_cached m j hj] at h
  exact h

theorem mem_cachedModeNode (m : Fin 3) (j : ℕ) (hj : j ≤ thetaCertificateCellCount m.val) :
    (cachedModeNode m.val j).Mem (thetaMode m.val ((j:ℝ)/64)) := by
  have h := mem_modeBox m.val (mem_gridBox j 64)
  rw [modeBox_eq_cached m j hj] at h
  exact h

theorem mem_cachedMajorantBox (m : Fin 3) (n j : ℕ) (hj : j ≤ thetaCertificateCellCount m.val) :
    (cachedMajorantBox m.val n j).Mem (thetaCodeMajorant n (thetaArgument m.val ((j:ℝ)/64))) := by
  apply mem_sum
  intro r _
  have h := mem_mul (mem_ofRat |(thetaCoefficientCode n)[r]?.getD 0|)
    (mem_pow (mem_cachedArgumentNode m j hj) r)
  simpa only [Rat.cast_abs] using h

theorem mem_exactTaylorMassBox (m : Fin 3) (n p j : ℕ) (hn : n ≤ 16)
    (hj : j ≤ thetaCertificateCellCount m.val) :
    (exactTaylorMassBox m.val n p j).Mem
      (weightedTaylorMass m.val n p ((j:ℝ)/64) (((j+1:ℕ):ℝ)/64)) := by
  apply mem_sum
  intro r hr
  have hd := mem_mul (mem_polynomialBox r (by omega) (mem_cachedArgumentNode m j hj))
    (mem_cachedModeNode m j hj)
  have h := mem_mulNonnegRat (mem_div hd (mem_point (r.factorial:ℤ))) (rationalGridWeight_nonneg p r j)
  rw [rationalGridWeight_eq] at h
  simpa only [Int.cast_natCast,thetaModeDerivative] using h

theorem mem_exactCellBox (m : Fin 3) (n p j : ℕ) (hn : n < 16)
    (hj : j < thetaCertificateCellCount m.val) :
    (exactCellBox m.val n p j).Mem
      (∫ u in ((j:ℝ)/64)..(((j+1:ℕ):ℝ)/64), u^p*thetaMode m.val u) := by
  have hv := mem_exactTaylorMassBox m n p j (by omega) (by omega)
  have he := mem_mulNonnegRat (mem_div (mem_mul (mem_cachedMajorantBox m (n+1) (j+1) (by omega))
    (mem_cachedModeNode m j (by omega))) (mem_point (n.factorial:ℤ)))
    (rationalGridWeight_nonneg p (n+1) j)
  rw [rationalGridWeight_eq] at he
  simp only [Int.cast_natCast] at he
  have ha : (0:ℝ) ≤ (j:ℝ)/64 := by positivity
  have hab : (j:ℝ)/64 < ((j+1:ℕ):ℝ)/64 := by push_cast; linarith
  have hb := thetaMode_weighted_cell_bounds m.val n p _ _ _ ha hab
    (thetaCode_cell_bound m.val (n+1) (by omega) _ _ ha)
  apply mem_outer (mem_add hv (mem_neg he)) (mem_add hv he)
  · simpa only [sub_eq_add_neg] using hb.1
  · exact hb.2

theorem mem_exactFiniteModeBox (m : Fin 3) (n p : ℕ) (hn : n < 16) :
    (exactFiniteModeBox m.val n p).Mem
      (∫ u in (0:ℝ)..((thetaCertificateCellCount m.val:ℝ)/64), u^p*thetaMode m.val u) := by
  unfold exactFiniteModeBox
  have h := mem_sum _ (fun j => ∫ u in ((j:ℝ)/64)..(((j+1:ℕ):ℝ)/64), u^p*thetaMode m.val u)
    (thetaCertificateCellCount m.val) (fun j hj => mem_exactCellBox m n p j hn hj)
  have he := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun u => u^p*thetaMode m.val u) (a := fun j : ℕ => (j:ℝ)/64)
    (n := thetaCertificateCellCount m.val)
    (fun _ _ => ((continuous_id.pow p).mul ((contDiff_thetaMode m.val 1).continuous)).intervalIntegrable _ _)
  rw [he] at h
  simpa only [Nat.cast_zero,zero_div] using h

theorem mem_exactFullModeBox (m : Fin 3) (n p : ℕ) (hn : n < 16)
    (hL : 0 < (thetaCertificateCellCount m.val:ℝ)/64)
    (hd : 0 < 2*thetaArgument m.val ((thetaCertificateCellCount m.val:ℝ)/64)-1/2-
      (p:ℝ)/((thetaCertificateCellCount m.val:ℝ)/64)) :
    (exactFullModeBox m.val n p).Mem (∫ u in Ioi 0, u^p*thetaMode m.val u) := by
  unfold exactFullModeBox
  have ht := mem_tailModeBox m.val p (mem_gridBox (thetaCertificateCellCount m.val) 64) hL hd
  rw [tailModeBox_eq_cached m p _ le_rfl] at ht
  norm_num only [Nat.cast_ofNat] at ht
  have h := mem_add (mem_exactFiniteModeBox m n p hn) ht
  have hi := integrableOn_weighted_thetaMode m.val p
  rw [intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hL.le))] at h
  exact h

theorem mem_exactFullThetaMomentBox (p : ℕ) (hp : p ≤ 18) :
    (exactFullThetaMomentBox p).Mem (completedNativeThetaTailMoment p) := by
  unfold exactFullThetaMomentBox
  have hpR : (p:ℝ) ≤ 18 := by exact_mod_cast hp
  have hd0 := thetaArgument_coarse_lower 0 (by norm_num : (0:ℝ) ≤ 96/64)
  have hd1 := thetaArgument_coarse_lower 1 (by norm_num : (0:ℝ) ≤ 64/64)
  have hd2 := thetaArgument_coarse_lower 2 (by norm_num : (0:ℝ) ≤ 48/64)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hd0 hd1 hd2
  have hm0 := mem_exactFullModeBox (0:Fin 3) 15 p (by omega) (by norm_num [thetaCertificateCellCount]) (by
    norm_num only [Fin.val_zero,thetaCertificateCellCount] at hd0 ⊢
    nlinarith only [hd0,hpR])
  have hm1 := mem_exactFullModeBox (1:Fin 3) 15 p (by omega) (by norm_num [thetaCertificateCellCount]) (by
    norm_num [thetaCertificateCellCount] at hd1 ⊢
    nlinarith only [hd1,hpR])
  have hm2 := mem_exactFullModeBox (2:Fin 3) 15 p (by omega) (by norm_num [thetaCertificateCellCount]) (by
    norm_num [thetaCertificateCellCount] at hd2 ⊢
    nlinarith only [hd2,hpR])
  have hb := integral_weightedOmittedModes_bounds p
  have hr := mem_outer (mem_point 0) (mem_rat p.factorial ((10:ℤ)^20*95^(p+1)))
    (by simpa only [Int.cast_zero] using hb.1) (by
      simpa only [Int.cast_natCast,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using hb.2)
  have h := mem_add (mem_add (mem_add hm0 hm1) hm2) hr
  rw [completedNativeThetaTailMoment_eq_three_and_remainder p]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceAdd]
  exact h

end CarryIntegralCertificate
