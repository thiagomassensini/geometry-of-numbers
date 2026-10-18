import ThetaInputs

/-! SAME original characteristic and SAME logarithmic derivative recurrence.
Only tighter enclosures are used; no numerical checkpoint enters Lean. -/
namespace CarrySixthEven
open CarryIntegralCertificate CarrySelfAdjointOperator CarryCriticalSource CarryThetaPattern
open GeometryOfNumbers.Analysis CarryMaterialSourceFactorComparison
open scoped BigOperators Matrix
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option maxRecDepth 65536

def sixthCharacteristicBox (n : ℕ) : Box :=
  if n=0 then (Box.rat 1 2).add ((thetaInputBox 0).div (.point 4)).neg else
    (Box.point ((-1:ℤ)^n)).mul
      (((thetaInputBox (n-1)).div (.point ((2*n-2).factorial:ℤ))).add
        ((thetaInputBox n).div (.point ((4*(2*n).factorial:ℕ):ℤ))).neg)

def sixthLogMomentBox (n : ℕ) : Box :=
  (((Box.point (-((n+1:ℕ):ℤ))).mul (sixthCharacteristicBox (n+1))).add
    (Box.sum (fun k => if _h : k < n then (sixthLogMomentBox k).mul (sixthCharacteristicBox (n-k))
      else .all) n).neg).div (sixthCharacteristicBox 0)
termination_by n

theorem mem_sixthCharacteristicBox
    (n : ℕ) :
    (sixthCharacteristicBox n).Mem (completedNativeRealEvenCharacteristicCoefficient n) := by
  cases n with
  | zero =>
    have he : completedNativeRealEvenCharacteristicCoefficient 0 =
        (1/2:ℝ)-completedNativeThetaTailMoment 0/4 := by
      rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder,
        completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
      norm_num
      ring
    rw [he,sixthCharacteristicBox,if_pos rfl]
    have h := mem_add (mem_rat 1 2) (mem_neg (mem_div (mem_thetaInputBox 0) (mem_point 4)))
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
      (mem_add (mem_div (mem_thetaInputBox n) (mem_point ((2*(n+1)-2).factorial:ℤ)))
        (mem_neg (mem_div (mem_thetaInputBox (n+1)) (mem_point ((4*(2*(n+1)).factorial:ℕ):ℤ)))))
    have he' : 2*(n+1)-2=2*n := by omega
    simpa only [sixthCharacteristicBox,Nat.succ_ne_zero,if_false,Nat.succ_sub_one,he',
      Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast,Int.cast_mul,Int.cast_ofNat,
      Nat.cast_mul,Nat.cast_ofNat,
      sub_eq_add_neg] using h

theorem mem_sixthLogMomentBox
    (n : ℕ) :
    (sixthLogMomentBox n).Mem (canonicalCompletedNativeLogDerivativeMoment n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hs := mem_sum
      (fun k => if _h : k < n then (sixthLogMomentBox k).mul (sixthCharacteristicBox (n-k)) else .all)
      (fun k => canonicalCompletedNativeLogDerivativeMoment k*
        completedNativeRealEvenCharacteristicCoefficient (n-k)) n (by
          intro k hk
          simp only [dif_pos hk]
          exact mem_mul (ih k hk) (mem_sixthCharacteristicBox (n-k)))
    have h := mem_div (mem_add
      (mem_mul (mem_point (-((n+1:ℕ):ℤ))) (mem_sixthCharacteristicBox (n+1)))
      (mem_neg hs)) (mem_sixthCharacteristicBox 0)
    rw [sixthLogMomentBox]
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


def sixthEvenRemainderBox : ℕ → ℕ → ℕ → Box
  | 0,i,j => sixthLogMomentBox (i+j)
  | r+1,i,j => (sixthEvenRemainderBox r i j).add
      (((sixthEvenRemainderBox r i r).mul (sixthEvenRemainderBox r r j)).div
        (sixthEvenRemainderBox r r r)).neg

theorem mem_sixthEvenRemainderBox (r i j : ℕ) :
    (sixthEvenRemainderBox r i j).Mem
      (carryPairingRemainder (fun a b : ℕ => h (a+b)) r i j) := by
  induction r generalizing i j with
  | zero =>
      change (sixthLogMomentBox (i+j)).Mem (h (i+j))
      exact mem_sixthLogMomentBox (i+j)
  | succ r ih =>
      exact mem_add (ih i j)
        (mem_neg (mem_div (mem_mul (ih i r) (ih r j)) (ih r r)))

end CarrySixthEven
