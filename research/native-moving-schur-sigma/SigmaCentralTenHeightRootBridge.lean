import SigmaHeight50Integration

/-!
# Ten height-50 zeros in the original completed characteristic

The positive roots are transported through `operatorHeightParameter` and the original
`completedNativeCharacteristicContinuation`. The distinct-point count enumerates the positive
heights; the RH certificate is used separately for reality and order one.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator
open CPFormal.Analytic.Cp

set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- A positive critical-line zero through height 50 must be one of the ten supplied box
witnesses. This uses the exact distinct-point count and does not use zero multiplicity. -/
private theorem sigmaLineZero_eq_ten_height
    (hcount : sigmaZeroCount50) (ts : Fin 10 → ℝ) (hmono : StrictMono ts)
    (htsBoxes : ∀ i : Fin 10,
      ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i) ∧
        riemannZeta (1 / 2 + ts i * Complex.I) = 0)
    {t : ℝ} (ht : 0 < t) (ht50 : t ≤ 50)
    (hzero : riemannZeta (sigmaLineZero t) = 0) :
    ∃ i : Fin 10, t = ts i := by
  let K : Set ℂ := (fun i : Fin 10 => sigmaLineZero (ts i)) '' Set.univ
  have htsInCount (i : Fin 10) :
      sigmaLineZero (ts i) ∈ sigmaRHStripZerosUpTo 50 := by
    apply sigmaLineZero_mem_stripZeros50
    · exact lt_trans (sigmaTenZeroLower_pos i) (htsBoxes i).1.1
    · exact le_of_lt (lt_trans (htsBoxes i).1.2 (sigmaTenZeroUpper_lt_fifty i))
    · simpa [sigmaLineZero] using (htsBoxes i).2
  have hKSub : K ⊆ sigmaRHStripZerosUpTo 50 := by
    rintro ρ ⟨i, -, rfl⟩
    exact htsInCount i
  have hmapInj : Function.Injective (fun i : Fin 10 => sigmaLineZero (ts i)) := by
    intro i j hij
    apply hmono.injective
    have him := congrArg Complex.im hij
    simpa [sigmaLineZero] using him
  have hKCard : K.ncard = 10 := by
    dsimp [K]
    rw [Set.ncard_image_of_injective Set.univ hmapInj]
    simp
  have hZFinite : (sigmaRHStripZerosUpTo 50).Finite := by
    apply Set.finite_of_ncard_pos
    rw [hcount]
    norm_num
  have hnewInCount : sigmaLineZero t ∈ sigmaRHStripZerosUpTo 50 :=
    sigmaLineZero_mem_stripZeros50 ht ht50 hzero
  have hKFinite : K.Finite := Set.Finite.image _ Set.finite_univ
  have hnewMemK : sigmaLineZero t ∈ K := by
    by_contra hnot
    have hins : insert (sigmaLineZero t) K ⊆ sigmaRHStripZerosUpTo 50 := by
      intro ρ hρ
      rcases hρ with rfl | hρ
      · exact hnewInCount
      · exact hKSub hρ
    have hcardIns : (insert (sigmaLineZero t) K).ncard = 11 := by
      rw [Set.ncard_insert_of_notMem hnot hKFinite, hKCard]
    have hle := Set.ncard_le_ncard hins hZFinite
    rw [hcount] at hle
    omega
  rcases hnewMemK with ⟨i, -, hi⟩
  refine ⟨i, ?_⟩
  have him := congrArg Complex.im hi
  simpa [sigmaLineZero] using him.symm

/-- The ten certified positive heights are simple roots of the original completed
characteristic. Evenness supplies the negative roots and preserves order one. Every completed
zero with `|Re w| ≤ 50` is one of these signed roots; the count and simplicity inputs remain
separate. -/
theorem sigmaHeight50_original_characteristic_roots :
    ∃ γ : ℝ, ∃ ts : Fin 10 → ℝ,
      ts 0 = γ ∧ StrictMono ts ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i) ∧
          riemannZeta (1 / 2 + ts i * Complex.I) = 0) ∧
      (∀ i : Fin 10,
        completedNativeCharacteristicContinuation (ts i : ℂ) = 0 ∧
          analyticOrderAt completedNativeCharacteristicContinuation (ts i : ℂ) = 1 ∧
          completedNativeCharacteristicContinuation (-(ts i : ℂ)) = 0 ∧
          analyticOrderAt completedNativeCharacteristicContinuation (-(ts i : ℂ)) = 1) ∧
      (∀ w : ℂ, completedNativeCharacteristicContinuation w = 0 → |w.re| ≤ 50 →
        w.im = 0 ∧ w.re ≠ 0 ∧
          ∃ i : Fin 10, w.re = ts i ∨ w.re = -(ts i)) := by
  obtain ⟨hRH, hcount, γ, _, _, hboxes⟩ :=
    sigmaHeight50_ten_zero_witnesses_and_count
  obtain ⟨ts, hts0, hmono, htsBoxes⟩ := hboxes
  have htPos (i : Fin 10) : 0 < ts i :=
    lt_trans (sigmaTenZeroLower_pos i) (htsBoxes i).1.1
  have ht50 (i : Fin 10) : ts i ≤ 50 :=
    le_of_lt (lt_trans (htsBoxes i).1.2 (sigmaTenZeroUpper_lt_fifty i))
  have hroots (i : Fin 10) :
      completedNativeCharacteristicContinuation (ts i : ℂ) = 0 ∧
        analyticOrderAt completedNativeCharacteristicContinuation (ts i : ℂ) = 1 ∧
        completedNativeCharacteristicContinuation (-(ts i : ℂ)) = 0 ∧
        analyticOrderAt completedNativeCharacteristicContinuation (-(ts i : ℂ)) = 1 := by
    have hstrip : operatorHeightParameter (ts i : ℂ) ∈ genuineCriticalStrip := by
      norm_num [genuineCriticalStrip, CarrySelfAdjointOperator.operatorHeightParameter]
    have hζ : riemannZeta (operatorHeightParameter (ts i : ℂ)) = 0 := by
      rw [operatorHeightParameter_eq_sigmaLineZero_of_im_zero (by simp)]
      simpa [sigmaLineZero] using (htsBoxes i).2
    have hrootPos : completedNativeCharacteristicContinuation (ts i : ℂ) = 0 :=
      (completedNativeCharacteristicContinuation_zero_iff_zeta hstrip).2 hζ
    have hbound : |((ts i : ℂ).re)| ≤ 50 := by
      have hre : ((ts i : ℂ).re) = ts i := by simp
      rw [hre, abs_of_pos (htPos i)]
      exact ht50 i
    have horderPos := sigmaContinuation_zero_order_one_of_height50 hRH hrootPos hbound
    have hrootNeg : completedNativeCharacteristicContinuation (-(ts i : ℂ)) = 0 := by
      rw [completedNativeCharacteristicContinuation_even]
      exact hrootPos
    have hboundNeg : |(-(ts i : ℂ)).re| ≤ 50 := by
      simpa using hbound
    have horderNeg := sigmaContinuation_zero_order_one_of_height50 hRH hrootNeg hboundNeg
    exact ⟨hrootPos, horderPos, hrootNeg, horderNeg⟩
  have hclassify (w : ℂ) (hzero : completedNativeCharacteristicContinuation w = 0)
      (hbound : |w.re| ≤ 50) :
      w.im = 0 ∧ w.re ≠ 0 ∧
        ∃ i : Fin 10, w.re = ts i ∨ w.re = -(ts i) := by
    have him := sigmaContinuation_zero_im_eq_zero_of_height50 hRH hzero hbound
    have hne := sigmaContinuation_zero_re_ne_zero_of_height50 hzero
    refine ⟨him, hne, ?_⟩
    by_cases hpos : 0 < w.re
    · have hs := completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip hzero
      have hζ := (completedNativeCharacteristicContinuation_zero_iff_zeta hs).mp hzero
      have hline : riemannZeta (sigmaLineZero w.re) = 0 := by
        rw [← operatorHeightParameter_eq_sigmaLineZero_of_im_zero him]
        exact hζ
      have hidx := sigmaLineZero_eq_ten_height hcount ts hmono htsBoxes hpos
        ((abs_le.mp hbound).2) hline
      rcases hidx with ⟨i, hi⟩
      exact ⟨i, Or.inl hi⟩
    · have hneg : w.re < 0 := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact h
        · exact (hpos h).elim
      have hzeroNeg : completedNativeCharacteristicContinuation (-w) = 0 := by
        rw [completedNativeCharacteristicContinuation_even]
        exact hzero
      have hsNeg :=
        completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip hzeroNeg
      have hζNeg :=
        (completedNativeCharacteristicContinuation_zero_iff_zeta hsNeg).mp hzeroNeg
      have himNeg : (-w).im = 0 := by simpa using him
      have hline' : riemannZeta (sigmaLineZero ((-w).re)) = 0 := by
        rw [← operatorHeightParameter_eq_sigmaLineZero_of_im_zero himNeg]
        exact hζNeg
      have hline : riemannZeta (sigmaLineZero (-w.re)) = 0 := by simpa using hline'
      have hidx := sigmaLineZero_eq_ten_height hcount ts hmono htsBoxes
        (by linarith) (by linarith [(abs_le.mp hbound).1]) hline
      rcases hidx with ⟨i, hi⟩
      exact ⟨i, Or.inr (by linarith)⟩
  exact ⟨γ, ts, hts0, hmono, htsBoxes, hroots, hclassify⟩

#print axioms sigmaHeight50_original_characteristic_roots

end CarrySigmaObstruction
