import SourceTwentySix

namespace CarrySeventhEven
open CarryIntegralCertificate CarrySelfAdjointOperator CarryCriticalSource CarrySixthEven CarrySixthOdd
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

def thirteenthCoefficientBox : Box :=
  (((Box.point 2600).mul thetaTwentyFourBox).add thetaTwentySixBox.neg).neg.div
    (Box.point (4*(Nat.factorial 26:ℤ)))

theorem source_c13_theta : completedNativeRealEvenCharacteristicCoefficient 13 =
    -(2600*completedNativeThetaTailMoment 24-completedNativeThetaTailMoment 26)/
      (4*(Nat.factorial 26:ℝ)) := by
  change completedNativeRealEvenCharacteristicCoefficient (12+1) = _
  rw [CarryThetaPattern.sourceCoefficient_theta,CarryThetaPattern.sourceThetaIntegral_moments]
  norm_num

theorem mem_thirteenthCoefficientBox :
    thirteenthCoefficientBox.Mem (completedNativeRealEvenCharacteristicCoefficient 13) := by
  rw [source_c13_theta]
  have hx := mem_div (mem_neg
    (mem_add (mem_mul (mem_point 2600) mem_thetaTwentyFourBox)
      (mem_neg mem_thetaTwentySixBox))) (mem_point (4*(Nat.factorial 26:ℤ)))
  simpa only [thirteenthCoefficientBox,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,
    Nat.reduceMul,sub_eq_add_neg] using hx

def coefficientBox (n : ℕ) : Box :=
  if n=13 then thirteenthCoefficientBox else if n=12 then twelfthCoefficientBox
  else sixthCharacteristicBox n

theorem mem_coefficientBox (n : ℕ) :
    (coefficientBox n).Mem (completedNativeRealEvenCharacteristicCoefficient n) := by
  unfold coefficientBox
  split_ifs with hn hm
  · subst n; exact mem_thirteenthCoefficientBox
  · subst n; exact mem_twelfthCoefficientBox
  · exact mem_sixthCharacteristicBox n

end CarrySeventhEven
