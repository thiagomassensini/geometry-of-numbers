import SigmaCentralTenHeightRootBridge
import RHHeight.Main

/-!
# Exact zeros of the original completed characteristic in the radius-51 disk

The ten heights still come from B2. The height-52 RH and multiplicity-count certificate
classifies every further zero in the disk; no source function or moment is defined from zeros.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator Complex Set
open CPFormal.Analytic.Cp
open Zeta23
open Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 6000000

private lemma sigmaContour51_ten_box_lower_gt_three (i : Fin 10) :
    3 < sigmaTenZeroBoxLower i := by
  fin_cases i <;> norm_num [sigmaTenZeroBoxLower]

/-- Height-52 RH with simplicity applies on either side of the height axis of the original
continuation. Evenness transports the order at a negative root from its positive reflection. -/
private theorem sigmaContour51_zero_order_one_of_height52 {w : ℂ}
    (hzero : completedNativeCharacteristicContinuation w = 0)
    (hbound : |w.re| ≤ 51) :
    analyticOrderAt completedNativeCharacteristicContinuation w = 1 := by
  have hne := sigmaContinuation_zero_re_ne_zero_of_height50 hzero
  by_cases hpos : 0 < w.re
  · have hs := completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip hzero
    have hζ := (completedNativeCharacteristicContinuation_zero_iff_zeta hs).mp hzero
    have hle : w.re ≤ 52 := by linarith [(abs_le.mp hbound).2]
    have hres := RHHeight.rh_up_to_height_fiftytwo (operatorHeightParameter w)
      hζ hs.1 hs.2
      (by rw [operatorHeightParameter_im]; exact hpos)
      (by rw [operatorHeightParameter_im]; exact hle)
    rw [completedNativeCharacteristicContinuation_order_eq_zeta hs]
    exact hres.2
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
    have hleNeg : -w.re ≤ 52 := by linarith [(abs_le.mp hbound).1]
    have hres := RHHeight.rh_up_to_height_fiftytwo (operatorHeightParameter (-w))
      hζNeg hsNeg.1 hsNeg.2
      (by rw [operatorHeightParameter_im]; simp; exact hneg)
      (by rw [operatorHeightParameter_im]; simp; exact hleNeg)
    have horderNeg :
        analyticOrderAt completedNativeCharacteristicContinuation (-w) = 1 := by
      rw [completedNativeCharacteristicContinuation_order_eq_zeta hsNeg]
      exact hres.2
    have hnegAnalytic : AnalyticAt ℂ (fun u : ℂ => -u) w := by fun_prop
    have hcompOrder :
        analyticOrderAt (completedNativeCharacteristicContinuation ∘ (fun u : ℂ => -u)) w =
          analyticOrderAt completedNativeCharacteristicContinuation (-w) :=
      analyticOrderAt_comp_of_deriv_ne_zero hnegAnalytic (by simp)
    have heven : (completedNativeCharacteristicContinuation ∘ (fun u : ℂ => -u)) =ᶠ[𝓝 w]
        completedNativeCharacteristicContinuation := by
      filter_upwards [] with u
      exact completedNativeCharacteristicContinuation_even u
    calc
      analyticOrderAt completedNativeCharacteristicContinuation w =
          analyticOrderAt (completedNativeCharacteristicContinuation ∘ (fun u : ℂ => -u)) w :=
        (analyticOrderAt_congr heven).symm
      _ = analyticOrderAt completedNativeCharacteristicContinuation (-w) := hcompOrder
      _ = 1 := horderNeg

/-- The height-52 multiplicity count exhausts the ten distinct B2 line zeros and forces every
zero in `3 < Im ρ ≤ 52` to be one of them with multiplicity one. -/
theorem sigmaHeight52_count_exhausts_ten_zeros_with_multiplicity :
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
      ∀ ρ : ℂ, ρ ∈ Zeta23.zerosIn 3 52 →
        (∃ i : Fin 10, ρ = (1 / 2 : ℂ) + ts i * Complex.I) ∧
          Zeta23.zeroMult ρ = 1 := by
  classical
  obtain ⟨γ, ts, hts0, hmono, htsBoxes, hroots, _⟩ :=
    sigmaHeight50_original_characteristic_roots
  let f : Fin 10 → ℂ := fun i => (1 / 2 : ℂ) + ts i * Complex.I
  let S : Finset ℂ := Finset.univ.image f
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply hmono.injective
    have him := congrArg Complex.im hij
    simpa [f] using him
  have hcard : S.card = 10 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hf_inj]
    simp
  have hS : ∀ ρ ∈ S, ρ ∈ Zeta23.zerosIn 3 52 := by
    intro ρ hρ
    rcases Finset.mem_image.mp hρ with ⟨i, -, rfl⟩
    have hlow : 3 < ts i :=
      lt_trans (sigmaContour51_ten_box_lower_gt_three i) (htsBoxes i).1.1
    have hhigh : ts i ≤ 52 :=
      (htsBoxes i).1.2.le.trans (sigmaTenZeroUpper_lt_fifty i).le |>.trans (by norm_num)
    simp only [Zeta23.zerosIn, Zeta23.IsNontrivialZero, Set.mem_setOf_eq]
    refine ⟨⟨(htsBoxes i).2, ?_, ?_⟩, ?_, ?_⟩
    · norm_num [f]
    · norm_num [f]
    · simpa [f] using hlow
    · simpa [f] using hhigh
  have hN : Zeta23.Ncount 3 52 ≤ 10 := by
    simpa only [RHHeight.ncount_three_fiftytwo] using (le_rfl : (10 : ℕ) ≤ 10)
  have hcount := RHHeight.mem_and_simple_of_Ncount_le S hS hcard hN
  have hcover (ρ : ℂ) (hρ : ρ ∈ Zeta23.zerosIn 3 52) :
      (∃ i : Fin 10, ρ = f i) ∧ Zeta23.zeroMult ρ = 1 := by
    obtain ⟨hρS, hmult⟩ := hcount ρ hρ
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hρS
    exact ⟨⟨i, hi.symm⟩, hmult⟩
  refine ⟨γ, ts, hts0, hmono, htsBoxes, hroots, ?_⟩
  intro ρ hρ
  obtain ⟨⟨i, hi⟩, hmult⟩ := hcover ρ hρ
  exact ⟨⟨i, hi⟩, hmult⟩

/-- The original completed characteristic has exactly the twenty signed B2 roots in
`|z| ≤ 51`; all are simple and the radius-51 contour is zero-free. The positive-root list is
exhausted using the height-52 count with multiplicity, not by extrapolating B2's distinct count
at height 50. -/
theorem sigmaContour51_original_characteristic_roots :
    ∃ γ : ℝ, ∃ ts : Fin 10 → ℝ,
      ts 0 = γ ∧ StrictMono ts ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i) ∧
          riemannZeta (1 / 2 + ts i * Complex.I) = 0) ∧
      (∀ z : ℂ, ‖z‖ ≤ 51 →
        (completedNativeCharacteristicContinuation z = 0 ↔
          ∃ i : Fin 10, z = (ts i : ℂ) ∨ z = -(ts i : ℂ))) ∧
      (∀ z : ℂ, ‖z‖ = 51 → completedNativeCharacteristicContinuation z ≠ 0) ∧
      (∀ z : ℂ, completedNativeCharacteristicContinuation z = 0 → ‖z‖ ≤ 51 →
        analyticOrderAt completedNativeCharacteristicContinuation z = 1) := by
  classical
  obtain ⟨γ, ts, hts0, hmono, htsBoxes, hroots, hcover⟩ :=
    sigmaHeight52_count_exhausts_ten_zeros_with_multiplicity
  let f : Fin 10 → ℂ := fun i => (1 / 2 : ℂ) + ts i * Complex.I
  have htpos (i : Fin 10) : 0 < ts i :=
    lt_trans (sigmaTenZeroLower_pos i) (htsBoxes i).1.1
  have htlt50 (i : Fin 10) : ts i < 50 :=
    lt_trans (htsBoxes i).1.2 (sigmaTenZeroUpper_lt_fifty i)
  have hclassify (z : ℂ) (hz : completedNativeCharacteristicContinuation z = 0)
      (hball : ‖z‖ ≤ 51) : ∃ i : Fin 10, z = (ts i : ℂ) ∨ z = -(ts i : ℂ) := by
    have hne := sigmaContinuation_zero_re_ne_zero_of_height50 hz
    have hpositive (w : ℂ) (hw : completedNativeCharacteristicContinuation w = 0)
        (hwpos : 0 < w.re) (hwball : ‖w‖ ≤ 51) :
        ∃ i : Fin 10, w = (ts i : ℂ) := by
      have hsw :=
        completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip hw
      have hζw := (completedNativeCharacteristicContinuation_zero_iff_zeta hsw).mp hw
      have hnormw : ‖w‖ ≤ 51 := hwball
      have hrew : |w.re| ≤ 51 := (Complex.abs_re_le_norm w).trans hnormw
      have himPos : 0 < (operatorHeightParameter w).im := by
        rw [operatorHeightParameter_im]
        exact hwpos
      have himLe52 : (operatorHeightParameter w).im ≤ 52 := by
        rw [operatorHeightParameter_im]
        linarith [(abs_le.mp hrew).2]
      have hRH := RHHeight.rh_up_to_height_fiftytwo (operatorHeightParameter w)
        hζw hsw.1 hsw.2 himPos himLe52
      have hzeroAxis : w.im = 0 := by
        have hRe := operatorHeightParameter_re w
        rw [← hRH.1] at hRe
        linarith
      have hlow := RHHeight.low_height (operatorHeightParameter w) hζw hsw.1 hsw.2 himPos
      have himGt3 : 3 < (operatorHeightParameter w).im := by
        by_contra hnot
        exact hlow (le_of_not_gt hnot)
      have hwindow :
          operatorHeightParameter w ∈ Zeta23.zerosIn 3 52 := by
        simp only [Zeta23.zerosIn, Zeta23.IsNontrivialZero, Set.mem_setOf_eq]
        exact ⟨⟨hζw, hsw.1, hsw.2⟩, himGt3, himLe52⟩
      obtain ⟨⟨i, hρ⟩, _hmult⟩ := hcover (operatorHeightParameter w) hwindow
      have hparam : operatorHeightParameter w = f i := by
        simpa [f] using hρ
      have hImParam := congrArg Complex.im hparam
      have hwRe : w.re = ts i := by
        simpa [f, operatorHeightParameter_im] using hImParam
      have hwEq : w = (ts i : ℂ) := by
        apply Complex.ext
        · simpa using hwRe
        · simp [hzeroAxis]
      exact ⟨i, hwEq⟩
    by_cases hpos : 0 < z.re
    · obtain ⟨i, hi⟩ := hpositive z hz hpos hball
      exact ⟨i, Or.inl hi⟩
    · have hneg : z.re < 0 := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact h
        · exact (hpos h).elim
      have hzNeg : completedNativeCharacteristicContinuation (-z) = 0 := by
        rw [completedNativeCharacteristicContinuation_even]
        exact hz
      have hballNeg : ‖-z‖ ≤ 51 := by simpa using hball
      have hposNeg : 0 < (-z).re := by simpa using neg_pos.mpr hneg
      obtain ⟨i, hi⟩ := hpositive (-z) hzNeg hposNeg hballNeg
      have hEq := congrArg (fun w : ℂ => -w) hi
      exact ⟨i, Or.inr (by simpa using hEq)⟩
  have hrootIff (z : ℂ) (hball : ‖z‖ ≤ 51) :
      completedNativeCharacteristicContinuation z = 0 ↔
        ∃ i : Fin 10, z = (ts i : ℂ) ∨ z = -(ts i : ℂ) := by
    constructor
    · exact fun hz => hclassify z hz hball
    · rintro ⟨i, hi | hi⟩
      · simpa [hi] using (hroots i).1
      · simpa [hi] using (hroots i).2.2.1
  have hboundary (z : ℂ) (habs : ‖z‖ = 51) :
      completedNativeCharacteristicContinuation z ≠ 0 := by
    intro hz
    obtain ⟨i, hi | hi⟩ := hclassify z hz (by rw [habs])
    · have hnorm : ‖z‖ = 51 := by simpa using habs
      rw [hi, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (htpos i)] at hnorm
      linarith [htlt50 i]
    · have hnorm : ‖z‖ = 51 := by simpa using habs
      rw [hi, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (htpos i)] at hnorm
      linarith [htlt50 i]
  have hsimple (z : ℂ) (hz : completedNativeCharacteristicContinuation z = 0)
      (hball : ‖z‖ ≤ 51) :
      analyticOrderAt completedNativeCharacteristicContinuation z = 1 := by
    have hnorm : ‖z‖ ≤ 51 := hball
    have hrealBound : |z.re| ≤ 51 := (Complex.abs_re_le_norm z).trans hnorm
    exact sigmaContour51_zero_order_one_of_height52 hz hrealBound
  exact ⟨γ, ts, hts0, hmono, htsBoxes, hrootIff, hboundary, hsimple⟩

#print axioms sigmaHeight52_count_exhausts_ten_zeros_with_multiplicity
#print axioms sigmaContour51_original_characteristic_roots

end CarrySigmaObstruction
