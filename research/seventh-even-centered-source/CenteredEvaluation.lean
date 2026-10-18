import CenteredReferenceData

namespace CarrySeventhEven
open CarryIntegralCertificate CarrySelfAdjointOperator CarryCriticalSource
open CarryCenteredRecurrence
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

def coefficientError (j : ℕ) : ℝ :=
  completedNativeRealEvenCharacteristicCoefficient j-(refC j:ℝ)

def linearVariation (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 14, (derivC n j:ℝ)*coefficientError j

theorem indicator_evaluation (i : ℕ) (hi : i < 14) :
    (∑ j ∈ Finset.range 14, (indicator j i:ℝ)*coefficientError j) = coefficientError i := by
  rw [Finset.sum_eq_single i]
  · simp [indicator]
  · intro j _ hj
    simp [indicator,hj]
  · intro hi'
    exact (hi' (Finset.mem_range.mpr hi)).elim

theorem reference_recurrence_real (n : ℕ) (hn : n < 13) :
    (refC 0:ℝ)*(refH n:ℝ) = -((n+1:ℕ):ℝ)*(refC (n+1):ℝ)-
      ∑ k ∈ Finset.range n, (refH k:ℝ)*(refC (n-k):ℝ) := by
  exact_mod_cast reference_recurrence_check ⟨n,hn⟩

theorem derivative_recurrence_real (n j : ℕ) (hn : n < 13) (hj : j < 14) :
    (refC 0:ℝ)*(derivC n j:ℝ) = -((n+1:ℕ):ℝ)*(indicator j (n+1):ℝ)-
      (∑ k ∈ Finset.range n, (derivC k j:ℝ)*(refC (n-k):ℝ))-
      ∑ k ∈ Finset.range (n+1), (refH k:ℝ)*(indicator j (n-k):ℝ) := by
  exact_mod_cast derivative_recurrence_check ⟨n,hn⟩ ⟨j,hj⟩

theorem linearVariation_recurrence (n : ℕ) (hn : n < 13) :
    (refC 0:ℝ)*linearVariation n = -((n+1:ℕ):ℝ)*coefficientError (n+1)-
      (∑ k ∈ Finset.range n, linearVariation k*(refC (n-k):ℝ))-
      ∑ k ∈ Finset.range (n+1), (refH k:ℝ)*coefficientError (n-k) := by
  have h0 : ((n+1:ℕ):ℝ)*coefficientError (n+1) =
      ∑ j ∈ Finset.range 14, (((n+1:ℕ):ℝ)*(indicator j (n+1):ℝ))*coefficientError j := by
    rw [← indicator_evaluation (n+1) (by omega),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h1 : (∑ k ∈ Finset.range n, linearVariation k*(refC (n-k):ℝ)) =
      ∑ j ∈ Finset.range 14,
        (∑ k ∈ Finset.range n, (derivC k j:ℝ)*(refC (n-k):ℝ))*coefficientError j := by
    simp only [linearVariation,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h2 : (∑ k ∈ Finset.range (n+1), (refH k:ℝ)*coefficientError (n-k)) =
      ∑ j ∈ Finset.range 14,
        (∑ k ∈ Finset.range (n+1), (refH k:ℝ)*(indicator j (n-k):ℝ))*coefficientError j := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← indicator_evaluation (n-k) (by omega),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [neg_mul,h0,h1,h2]
  simp only [linearVariation,Finset.mul_sum]
  rw [← Finset.sum_neg_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc,derivative_recurrence_real n j hn (Finset.mem_range.mp hj)]
  ring

def coefficientErrorBox (j : ℕ) : Box :=
  (coefficientBox j).add (Box.ofRat (refC j)).neg

theorem mem_coefficientErrorBox (j : ℕ) :
    (coefficientErrorBox j).Mem (coefficientError j) :=
  mem_add (mem_coefficientBox j) (mem_neg (mem_ofRat _))

def linearVariationBox (n : ℕ) : Box :=
  Box.sum (fun j => (Box.ofRat (derivC n j)).mul (coefficientErrorBox j)) 14

theorem mem_linearVariationBox (n : ℕ) :
    (linearVariationBox n).Mem (linearVariation n) :=
  mem_sum _ _ 14 (fun j _ => mem_mul (mem_ofRat _) (mem_coefficientErrorBox j))

def nonlinearRemainderTable : Fin 13 → Box := ![Box.finite (-36242883596789623) (36242883596789623),
  Box.finite (-153514843841203990) (153514843841203990),
  Box.finite (-35192828911032461) (35192828911032461),
  Box.finite (-4158561821163233) (4158561821163233),
  Box.finite (-325507892558897) (325507892558897),
  Box.finite (-19095588984209) (19095588984209),
  Box.finite (-904715741839) (904715741839),
  Box.finite (-36697519727) (36697519727),
  Box.finite (-1342216327) (1342216327),
  Box.finite (-47076338) (47076338),
  Box.finite (-2533348) (2533348),
  Box.finite (-1050348) (1050348),
  Box.finite (-1001686) (1001686)]

def nonlinearRemainderBox (n : ℕ) : Box :=
  if h : n < 13 then nonlinearRemainderTable ⟨n,h⟩ else .all

def rawNonlinearRemainderBox (n : ℕ) : Box :=
  (((Box.sum (fun k => (nonlinearRemainderBox k).mul (coefficientBox (n-k))) n).add
    (Box.sum (fun k => (linearVariationBox k).mul (coefficientErrorBox (n-k))) (n+1))).neg).div
      (coefficientBox 0)

theorem nonlinear_cache_checks : ∀ n : Fin 13,
    (rawNonlinearRemainderBox n.val).contained (nonlinearRemainderBox n.val) = true := by
  decide +kernel

theorem nonlinearRemainder_recurrence (n : ℕ) (hn : n < 13) :
    h n-(refH n:ℝ)-linearVariation n =
      (-(∑ k ∈ Finset.range n,
        (h k-(refH k:ℝ)-linearVariation k)*completedNativeRealEvenCharacteristicCoefficient (n-k))-
        ∑ k ∈ Finset.range (n+1), linearVariation k*coefficientError (n-k))/
          completedNativeRealEvenCharacteristicCoefficient 0 := by
  have hm : completedNativeRealEvenCharacteristicCoefficient 0*h n =
      -((n+1:ℕ):ℝ)*completedNativeRealEvenCharacteristicCoefficient (n+1)-
        ∑ k ∈ Finset.range n, h k*completedNativeRealEvenCharacteristicCoefficient (n-k) := by
    have hr := canonicalCompletedNativeLogDerivativeMoment_real_recurrence n
    norm_num only [Nat.cast_add,Nat.cast_one] at hr ⊢
    linarith only [hr]
  have he := centered_recurrence_identity
    completedNativeRealEvenCharacteristicCoefficient (fun k => (refC k:ℝ))
    h (fun k => (refH k:ℝ)) linearVariation n hm
    (reference_recurrence_real n hn) (linearVariation_recurrence n hn)
  apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).mpr
  rw [mul_comm]
  exact he

theorem mem_nonlinearRemainderBox (n : ℕ) (hn : n < 13) :
    (nonlinearRemainderBox n).Mem (h n-(refH n:ℝ)-linearVariation n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hs := mem_sum
        (fun k => (nonlinearRemainderBox k).mul (coefficientBox (n-k)))
        (fun k => (h k-(refH k:ℝ)-linearVariation k)*completedNativeRealEvenCharacteristicCoefficient (n-k))
        n (by
          intro k hk
          exact mem_mul (ih k hk (by omega)) (mem_coefficientBox (n-k)))
      have ht := mem_sum _ _ (n+1) (fun k _ =>
        mem_mul (mem_linearVariationBox k) (mem_coefficientErrorBox (n-k)))
      have hx := mem_div (mem_neg (mem_add hs ht)) (mem_coefficientBox 0)
      have hc : (rawNonlinearRemainderBox n).Mem (h n-(refH n:ℝ)-linearVariation n) := by
        rw [nonlinearRemainder_recurrence n hn]
        simpa only [rawNonlinearRemainderBox,neg_add,sub_eq_add_neg] using hx
      exact mem_of_contained hc (nonlinear_cache_checks ⟨n,hn⟩)

def centeredMomentBox (n : ℕ) : Box :=
  ((Box.ofRat (refH n)).add (linearVariationBox n)).add (nonlinearRemainderBox n)

theorem mem_centeredMomentBox (n : ℕ) (hn : n < 13) :
    (centeredMomentBox n).Mem (h n) := by
  have hx := mem_add (mem_add (mem_ofRat (refH n)) (mem_linearVariationBox n))
    (mem_nonlinearRemainderBox n hn)
  have he : (refH n:ℝ)+linearVariation n+(h n-(refH n:ℝ)-linearVariation n) = h n := by ring
  rw [he] at hx
  exact hx

end
end CarrySeventhEven
