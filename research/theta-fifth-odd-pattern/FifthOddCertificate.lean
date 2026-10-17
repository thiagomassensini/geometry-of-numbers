import ThetaTwenty

/-! The next shifted Hankel section is certified from the unchanged infinite
source. The interval recursion keeps every old-new coupling. -/
namespace CarryThetaPattern
open CarryIntegralCertificate CarrySelfAdjointOperator CarryCriticalSource
open GeometryOfNumbers.Analysis CarryMaterialSourceFactorComparison
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

def tenthCoefficientBox : Box :=
  (((Box.point 1520).mul (momentInputBox 9)).add thetaTwentyBox.neg).div
    (Box.point (4*(Nat.factorial 20 : ℤ)))

def ninthMomentBox : Box :=
  (((Box.point (-10)).mul tenthCoefficientBox).add
    (Box.sum (fun k => (logMomentBox k).mul (characteristicBox (9-k))) 9).neg).div
      (characteristicBox 0)

def sourceMomentBox (n : ℕ) : Box := if n=9 then ninthMomentBox else logMomentBox n

def oddRemainderBox : ℕ → ℕ → ℕ → Box
  | 0,i,j => sourceMomentBox (i+j+1)
  | r+1,i,j => (oddRemainderBox r i j).add
      (((oddRemainderBox r i r).mul (oddRemainderBox r r j)).div (oddRemainderBox r r r)).neg

theorem mem_tenthCoefficientBox :
    tenthCoefficientBox.Mem (completedNativeRealEvenCharacteristicCoefficient 10) := by
  rw [source_c10_theta]
  have hx := mem_div
    (mem_add (mem_mul (mem_point 1520) (material_theta_integral_input 9))
      (mem_neg mem_thetaTwentyBox)) (mem_point (4*(Nat.factorial 20 : ℤ)))
  simpa only [tenthCoefficientBox,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,
    Nat.reduceMul,sub_eq_add_neg] using hx

theorem mem_ninthMomentBox : ninthMomentBox.Mem (h 9) := by
  have hs := mem_sum _ _ 9 (fun k _ => mem_mul
    (mem_logMomentBox material_theta_integral_input k)
    (mem_characteristicBox material_theta_integral_input (9-k)))
  have hx := mem_div (mem_add (mem_mul (mem_point (-10)) mem_tenthCoefficientBox)
    (mem_neg hs)) (mem_characteristicBox material_theta_integral_input 0)
  have he := canonicalCompletedNativeLogDerivativeMoment_eq 9
  convert hx using 1
  · rfl
  · change canonicalCompletedNativeLogDerivativeMoment 9 = _
    rw [he]
    norm_num only [Nat.reduceAdd,Nat.cast_ofNat,Int.cast_neg,Int.cast_ofNat]
    ring

theorem mem_sourceMomentBox (n : ℕ) : (sourceMomentBox n).Mem (h n) := by
  unfold sourceMomentBox
  split_ifs with hn
  · subst n
    exact mem_ninthMomentBox
  · exact mem_logMomentBox material_theta_integral_input n

theorem mem_oddRemainderBox (r i j : ℕ) :
    (oddRemainderBox r i j).Mem (carryPairingRemainder carryMaterialOddPairing r i j) := by
  induction r generalizing i j with
  | zero =>
      change (oddRemainderBox 0 i j).Mem (carryMaterialOddPairing i j)
      rw [material_odd_pairing_source]
      exact mem_sourceMomentBox (i+j+1)
  | succ r ih =>
      exact mem_add (ih i j)
        (mem_neg (mem_div (mem_mul (ih i r) (ih r j)) (ih r r)))

theorem odd_five_rectangle_check :
    ∀ r : Fin 5, (oddRemainderBox r.val r.val r.val).positive = true := by
  decide +kernel


theorem odd_fifth_lower_check :
    ((oddRemainderBox 4 4 4).add (Box.rat 7 (10^30)).neg).positive = true := by
  decide +kernel

theorem odd_fifth_upper_check :
    ((Box.rat 10 (10^30)).add (oddRemainderBox 4 4 4).neg).positive = true := by
  decide +kernel

/-- Bounds on the ORIGINAL ordered-elimination pivot. The physical
critical margin below is transported through positive definiteness. -/
theorem fifth_ordered_odd_pivot_bounds :
    (7/10^30:ℝ) < carryPairingPivot carryMaterialOddPairing 4 ∧
      carryPairingPivot carryMaterialOddPairing 4 < (10/10^30:ℝ) := by
  have hm := mem_oddRemainderBox 4 4 4
  have hl := pos_of_mem (mem_add hm (mem_neg (mem_rat 7 (10^30)))) odd_fifth_lower_check
  have hu := pos_of_mem (mem_add (mem_rat 10 (10^30)) (mem_neg hm)) odd_fifth_upper_check
  norm_num only [Int.cast_ofNat,Int.cast_pow] at hl hu
  change (7/10^30:ℝ) < carryPairingRemainder carryMaterialOddPairing 4 4 4 ∧
    carryPairingRemainder carryMaterialOddPairing 4 4 4 < (10/10^30:ℝ)
  constructor <;> linarith only [hl,hu]

theorem odd_five_pivots_pos (r : ℕ) (hr : r < 5) :
    0 < carryPairingPivot carryMaterialOddPairing r :=
  pos_of_mem (mem_oddRemainderBox r r r) (odd_five_rectangle_check ⟨r,hr⟩)

theorem odd_source_five_posDef : (sourceMomentMatrix h 1 5).PosDef := by
  have hs (i j : ℕ) : carryMaterialOddPairing i j = carryMaterialOddPairing j i := by
    rw [material_odd_pairing_source,material_odd_pairing_source]
    congr 1
    omega
  have hp := carryPairingCholesky_posDef hs 5 odd_five_pivots_pos
  convert hp using 1
  ext i j
  exact (material_odd_pairing_source i.val j.val).symm

theorem fifth_odd_pivot_pos : 0 < sourceMomentSchur h 1 4 :=
  (sourceMomentMatrix_succ_posDef_iff h 1 4
    (sourceMatrices_through_four_posDef 1 4 (by omega))).mp odd_source_five_posDef

theorem fifth_odd_criticalMargin : HasCriticalMargin 1 4 :=
  (criticalMargin_iff_pivot 1 4 (sourceMatrices_through_four_posDef 1 4 (by omega))).mpr
    fifth_odd_pivot_pos

theorem fifth_odd_theta_integral_certificate :
    (∫ u in Set.Ioi (0:ℝ), (1520*u^18-u^20)*XiThetaCosine.thetaTail u) <
      4*(Nat.factorial 20 : ℝ)*fifthOddCeiling :=
  fifthOdd_margin_iff_thetaIntegral.mp fifth_odd_criticalMargin

end
end CarryThetaPattern
