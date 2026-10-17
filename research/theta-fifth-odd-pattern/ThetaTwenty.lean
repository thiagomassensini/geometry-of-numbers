import NextSourceGate
import TabledSourceEquivalence

/-! Extend the proof assembling the SAME cached source quadrature to order
20. All retained tails and the infinite omitted-mode remainder are kept. -/
namespace CarryThetaPattern
open CarryIntegralCertificate CarrySelfAdjointOperator Real Set Filter MeasureTheory
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem mem_tabledTheta_upto_twenty (p : ℕ) (hp : p ≤ 20) :
    (tabledFullThetaMomentBox p).Mem (completedNativeThetaTailMoment p) := by
  have hpR : (p:ℝ) ≤ 20 := by exact_mod_cast hp
  have hd0 := thetaArgument_coarse_lower 0 (by norm_num : (0:ℝ) ≤ 96/64)
  have hd1 := thetaArgument_coarse_lower 1 (by norm_num : (0:ℝ) ≤ 64/64)
  have hd2 := thetaArgument_coarse_lower 2 (by norm_num : (0:ℝ) ≤ 48/64)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hd0 hd1 hd2
  have hm0 := mem_exactFullModeBox (0:Fin 3) 15 p (by omega)
    (by norm_num [thetaCertificateCellCount]) (by
      norm_num only [Fin.val_zero,thetaCertificateCellCount] at hd0 ⊢
      nlinarith only [hd0,hpR])
  have hm1 := mem_exactFullModeBox (1:Fin 3) 15 p (by omega)
    (by norm_num [thetaCertificateCellCount]) (by
      norm_num [thetaCertificateCellCount] at hd1 ⊢
      nlinarith only [hd1,hpR])
  have hm2 := mem_exactFullModeBox (2:Fin 3) 15 p (by omega)
    (by norm_num [thetaCertificateCellCount]) (by
      norm_num [thetaCertificateCellCount] at hd2 ⊢
      nlinarith only [hd2,hpR])
  have hb := integral_weightedOmittedModes_bounds p
  have hr := mem_outer (mem_point 0)
    (mem_rat p.factorial ((10:ℤ)^20*95^(p+1)))
    (by simpa only [Int.cast_zero] using hb.1) (by
      simpa only [Int.cast_natCast,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using hb.2)
  have hx := mem_add (mem_add (mem_add hm0 hm1) hm2) hr
  rw [completedNativeThetaTailMoment_eq_three_and_remainder p]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceAdd]
  rw [← exactFullThetaMomentBox_eq_tabled]
  exact hx

/-- Enclosure witness only; its inclusion is checked by the Lean kernel. -/
def thetaTwentyBox : Box := .finite
  1847557118783259000000000000000000000000000000000000
  1847557118783263000000000000000000000000000000000000

theorem thetaTwenty_containment_check :
    (tabledFullThetaMomentBox 20).contained thetaTwentyBox = true := by
  decide +kernel

theorem mem_thetaTwentyBox : thetaTwentyBox.Mem (completedNativeThetaTailMoment 20) :=
  mem_of_contained (mem_tabledTheta_upto_twenty 20 (by omega)) thetaTwenty_containment_check

end CarryThetaPattern
