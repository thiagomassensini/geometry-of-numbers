import SourceIntegral
import FixedInterval

/-! Back-substitution from source integral enclosures to the original
ordered material pivot. No moment matrix is redefined. -/
namespace CarryIntegralCertificate
open CarrySelfAdjointOperator GeometryOfNumbers.Analysis
open CarryMaterialSourceFactorComparison CarryMaterialFourthPivotComparison
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 32768

/-- A deliberately wider rational rectangle than PR #22, suitable for a
fully executable integral check. These are bounds, not changed source data. -/
def momentInputTable : Fin 10 → Box := ![Box.finite (11516887246743560330000000000000000000000000000000000000000) (11516887246743560360000000000000000000000000000000000000000),
  Box.finite (247320713366732640000000000000000000000000000000000000000) (247320713366732670000000000000000000000000000000000000000),
  Box.finite (20000506852638540000000000000000000000000000000000000000) (20000506852638570000000000000000000000000000000000000000),
  Box.finite (2877035926308030000000000000000000000000000000000000000) (2877035926308060000000000000000000000000000000000000000),
  Box.finite (589749292219170000000000000000000000000000000000000000) (589749292219200000000000000000000000000000000000000000),
  Box.finite (155208085744360000000000000000000000000000000000000000) (155208085744390000000000000000000000000000000000000000),
  Box.finite (49408429981950000000000000000000000000000000000000000) (49408429981980000000000000000000000000000000000000000),
  Box.finite (18313453794880000000000000000000000000000000000000000) (18313453794910000000000000000000000000000000000000000),
  Box.finite (7698639471690000000000000000000000000000000000000000) (7698639471720000000000000000000000000000000000000000),
  Box.finite (3601179054900000000000000000000000000000000000000000) (3601179054930000000000000000000000000000000000000000)]

def momentInputBox (n : ℕ) : Box := if h : n < 10 then momentInputTable ⟨n,h⟩ else .all

def characteristicBox (n : ℕ) : Box :=
  if n=0 then (Box.rat 1 2).add ((momentInputBox 0).div (.point 4)).neg else
    (Box.point ((-1:ℤ)^n)).mul
      (((momentInputBox (n-1)).div (.point ((2*n-2).factorial:ℤ))).add
        ((momentInputBox n).div (.point ((4*(2*n).factorial:ℕ):ℤ))).neg)

def logMomentBox (n : ℕ) : Box :=
  (((Box.point (-((n+1:ℕ):ℤ))).mul (characteristicBox (n+1))).add
    (Box.sum (fun k => if _h : k < n then (logMomentBox k).mul (characteristicBox (n-k))
      else .all) n).neg).div (characteristicBox 0)
termination_by n

def remainderBox : ℕ → ℕ → ℕ → Box
  | 0,i,j => (logMomentBox (i+j+2)).add
      (((logMomentBox (i+1)).mul (logMomentBox (j+1))).div (logMomentBox 0)).neg
  | r+1,i,j => (remainderBox r i j).add
      (((remainderBox r i r).mul (remainderBox r r j)).div (remainderBox r r r)).neg

theorem mem_characteristicBox
    (hb : ∀ n, (momentInputBox n).Mem (completedNativeThetaTailMoment (2*n))) (n : ℕ) :
    (characteristicBox n).Mem (completedNativeRealEvenCharacteristicCoefficient n) := by
  cases n with
  | zero =>
    have he : completedNativeRealEvenCharacteristicCoefficient 0 =
        (1/2:ℝ)-completedNativeThetaTailMoment 0/4 := by
      rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder,
        completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
      norm_num
      ring
    rw [he,characteristicBox,if_pos rfl]
    have h := mem_add (mem_rat 1 2) (mem_neg (mem_div (hb 0) (mem_point 4)))
    simpa only [Int.cast_one,Int.cast_ofNat,Nat.reduceMul,sub_eq_add_neg] using h
  | succ n =>
    have hf : ((2*(n+1)).factorial:ℝ) =
        (2*n+2:ℝ)*(2*n+1:ℝ)*((2*n).factorial:ℝ) := by
      rw [show 2*(n+1)=2*n+2 by omega,Nat.factorial_succ,Nat.factorial_succ]
      push_cast
      ring
    have he : completedNativeRealEvenCharacteristicCoefficient (n+1) =
        (-1:ℝ)^(n+1)*(completedNativeThetaTailMoment (2*n)/((2*n).factorial:ℝ)-
          completedNativeThetaTailMoment (2*(n+1))/(4*((2*(n+1)).factorial:ℝ))) := by
      rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder,
        completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
      rw [hf,show 2*(n+1)=2*n+2 by omega]
      push_cast
      field_simp
    rw [he]
    have h := mem_mul (mem_point ((-1:ℤ)^(n+1)))
      (mem_add (mem_div (hb n) (mem_point ((2*(n+1)-2).factorial:ℤ)))
        (mem_neg (mem_div (hb (n+1)) (mem_point ((4*(2*(n+1)).factorial:ℕ):ℤ)))))
    have he' : 2*(n+1)-2=2*n := by omega
    simpa only [characteristicBox,Nat.succ_ne_zero,if_false,Nat.succ_sub_one,he',
      Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast,Int.cast_mul,Int.cast_ofNat,
      Nat.cast_mul,Nat.cast_ofNat,
      sub_eq_add_neg] using h

theorem mem_logMomentBox
    (hb : ∀ n, (momentInputBox n).Mem (completedNativeThetaTailMoment (2*n))) (n : ℕ) :
    (logMomentBox n).Mem (canonicalCompletedNativeLogDerivativeMoment n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hs := mem_sum
      (fun k => if _h : k < n then (logMomentBox k).mul (characteristicBox (n-k)) else .all)
      (fun k => canonicalCompletedNativeLogDerivativeMoment k*
        completedNativeRealEvenCharacteristicCoefficient (n-k)) n (by
          intro k hk
          simp only [dif_pos hk]
          exact mem_mul (ih k hk) (mem_characteristicBox hb (n-k)))
    have h := mem_div (mem_add
      (mem_mul (mem_point (-((n+1:ℕ):ℤ))) (mem_characteristicBox hb (n+1)))
      (mem_neg hs)) (mem_characteristicBox hb 0)
    rw [logMomentBox]
    have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence n
    have heq : canonicalCompletedNativeLogDerivativeMoment n =
      (-((n+1:ℕ):ℝ)*completedNativeRealEvenCharacteristicCoefficient (n+1)-
        (∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k*
          completedNativeRealEvenCharacteristicCoefficient (n-k)))/
        completedNativeRealEvenCharacteristicCoefficient 0 := by
      apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
      norm_num only [Nat.cast_add,Nat.cast_one] at he ⊢
      linarith only [he]
    rw [heq]
    simpa only [Int.cast_neg,Int.cast_natCast,sub_eq_add_neg] using h

theorem mem_remainderBox
    (hb : ∀ n, (momentInputBox n).Mem (completedNativeThetaTailMoment (2*n)))
    (r i j : ℕ) : (remainderBox r i j).Mem
      (carryPairingRemainder carryMaterialEvenPairing r i j) := by
  induction r generalizing i j with
  | zero =>
    change (remainderBox 0 i j).Mem (carryMaterialEvenPairing i j)
    rw [material_even_pairing_source]
    exact mem_add (mem_logMomentBox hb (i+j+2))
      (mem_neg (mem_div (mem_mul (mem_logMomentBox hb (i+1)) (mem_logMomentBox hb (j+1)))
        (mem_logMomentBox hb 0)))
  | succ r ih =>
    exact mem_add (ih i j) (mem_neg (mem_div (mem_mul (ih i r) (ih r j)) (ih r r)))

end CarryIntegralCertificate
