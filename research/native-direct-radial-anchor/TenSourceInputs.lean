import ThetaTwenty
import EightInputs

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryIntegralCertificate CarryCriticalSource CarryThetaPattern
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000
attribute [local irreducible] Box.Mem

/-- The tenth original characteristic coefficient and ninth log moment,
using the already certified complete theta moment including all tails. -/
def sourceTenthBox : Box :=
  (((Box.point 1520).mul (momentInputBox 9)).add thetaTwentyBox.neg).div
    (Box.point (4*(Nat.factorial 20 : ℤ)))

def sourceNinthBox : Box :=
  (((Box.point (-10)).mul sourceTenthBox).add
    (Box.sum (fun k => (logMomentBox k).mul (characteristicBox (9-k))) 9).neg).div
      (characteristicBox 0)

theorem source_tenth_box_mem : sourceTenthBox.Mem (completedNativeRealEvenCharacteristicCoefficient 10) := by
  rw [source_c10_theta]
  have hx := mem_div
    (mem_add (mem_mul (mem_point 1520) (material_theta_integral_input 9))
      (mem_neg mem_thetaTwentyBox)) (mem_point (4*(Nat.factorial 20 : ℤ)))
  simpa only [sourceTenthBox,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,
    Nat.reduceMul,sub_eq_add_neg] using hx

theorem source_ninth_box_mem : sourceNinthBox.Mem (canonicalCompletedNativeLogDerivativeMoment 9) := by
  have hs := mem_sum _ _ 9 (fun k _ => mem_mul
    (mem_logMomentBox material_theta_integral_input k)
    (mem_characteristicBox material_theta_integral_input (9-k)))
  have hx := mem_div (mem_add (mem_mul (mem_point (-10)) source_tenth_box_mem)
    (mem_neg hs)) (mem_characteristicBox material_theta_integral_input 0)
  have he := canonicalCompletedNativeLogDerivativeMoment_eq 9
  convert hx using 1
  · rfl
  · rw [he]
    norm_num only [Nat.reduceAdd,Nat.cast_ofNat,Int.cast_neg,Int.cast_ofNat]
    ring

def momentBox8 : Box := .finite 1973265057000000000000000000000000000000 1973265091000000000000000000000000000000
def momentBox9 : Box := .finite 9872164850000000000000000000000000000 9872165920000000000000000000000000000

theorem moment_box_8_mem : momentBox8.Mem (canonicalCompletedNativeLogDerivativeMoment 8) := by
  apply mem_of_contained (mem_logMomentBox material_theta_integral_input 8)
  exact (show (logMomentBox 8).contained momentBox8 = true by decide +kernel)

theorem moment_box_9_mem : momentBox9.Mem (canonicalCompletedNativeLogDerivativeMoment 9) := by
  apply mem_of_contained source_ninth_box_mem
  exact (show sourceNinthBox.contained momentBox9 = true by decide +kernel)

end
end CarryDirectAnchor
