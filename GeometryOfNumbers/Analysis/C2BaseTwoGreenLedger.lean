import GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
import GreenFrame.Concrete.Finite.L2CoordinateMask

/-!
# Base-two ledger on the provenance-correct global C2 source

The two-generation energy is isolated before considering any cancellation
between cameras. No metric normalization is used.
-/

noncomputable section
open scoped BigOperators ENNReal lp InnerProductSpace

namespace GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
open GreenFrame.Concrete GeometryOfNumbers.Analysis
open C2GlobalGreenBridge C2GreenPreStencilCanary

@[simp] theorem baseTwo_code : baseNat 0 = 2 := rfl
@[simp] theorem baseTwo_positive_code : basePNat 0 = (2 : PNat) := by
  apply PNat.eq
  rfl
@[simp] theorem baseTwo_real_code : baseReal 0 = 2 := rfl

def baseTwoGreenProjection : ℓ²(GreenEvent, ℂ) →L[ℂ] ℓ²(GreenEvent, ℂ) :=
  l2CoordinateMaskCLM (fun e : GreenEvent => e.1 = 0)

def nonBaseTwoGreenProjection : ℓ²(GreenEvent, ℂ) →L[ℂ] ℓ²(GreenEvent, ℂ) :=
  l2CoordinateMaskCLM (fun e : GreenEvent => e.1 ≠ 0)

@[simp] theorem baseTwoGreenProjection_apply (x : ℓ²(GreenEvent, ℂ)) (e : GreenEvent) :
    baseTwoGreenProjection x e = if e.1 = 0 then x e else 0 := rfl

@[simp] theorem nonBaseTwoGreenProjection_apply (x : ℓ²(GreenEvent, ℂ)) (e : GreenEvent) :
    nonBaseTwoGreenProjection x e = if e.1 ≠ 0 then x e else 0 := rfl

theorem baseTwoGreenProjection_idempotent :
    baseTwoGreenProjection.comp baseTwoGreenProjection = baseTwoGreenProjection :=
  l2CoordinateMask_idempotent _

theorem baseTwoGreenProjection_isSelfAdjoint : IsSelfAdjoint baseTwoGreenProjection :=
  l2CoordinateMask_isSelfAdjoint _

theorem nonBaseTwoGreenProjection_idempotent :
    nonBaseTwoGreenProjection.comp nonBaseTwoGreenProjection = nonBaseTwoGreenProjection :=
  l2CoordinateMask_idempotent _

theorem nonBaseTwoGreenProjection_isSelfAdjoint : IsSelfAdjoint nonBaseTwoGreenProjection :=
  l2CoordinateMask_isSelfAdjoint _

theorem c2GlobalGreenInput_even_eq_zero (t : ℝ) (V : CoreState) (p : PNat) :
    c2GlobalGreenInputIsometry t V (2 * p) = 0 := by
  apply c2GlobalGreenInput_even
  change Even (2 * (p : ℕ))
  exact ⟨(p : ℕ), by omega⟩

theorem directGreenCoordinate_baseTwo_c2Source_eq_zero (t : ℝ) (V : CoreState) (p : PNat) :
    directGreenCoordinate canonicalCarryInfinitePartition (0, p)
      (c2GlobalGreenInputIsometry t V) = 0 := by
  simp [directGreenCoordinate, c2GlobalGreenInput_even_eq_zero]

theorem baseTwo_directGreenAnalysis_c2Source_eq_zero (t : ℝ) (V : CoreState) :
    baseTwoGreenProjection (directGreenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V)) = 0 := by
  apply lp.ext
  funext e
  by_cases h : e.1 = 0
  · rcases e with ⟨r,p⟩
    change r = 0 at h
    subst r
    simp [directGreenCoordinate_baseTwo_c2Source_eq_zero]
  · simp [h]

/-- The normalized carry ratio of the physical base-two camera. -/
theorem carryRatio_baseTwo_sq : carryRatio 0 ^ 2 = (1 / 2 : ℝ) := by
  simpa only [baseTwo_real_code] using carryRatio_sq_eq_one_div 0

private theorem odd_not_two_dvd (p : PNat) (hp : Odd (p : ℕ)) : ¬2 ∣ (p : ℕ) := by
  rintro ⟨a, ha⟩
  apply (Nat.not_even_iff_odd.mpr hp)
  exact ⟨a, by omega⟩

theorem verticalGreenStencil_baseTwo_oddParent (t : ℝ) (V : CoreState)
    (p : PNat) (hp : Odd (p : ℕ)) :
    verticalGreenStencil (0, p) (c2GlobalGreenInputIsometry t V) =
      -((2 * carryRatio 0 : ℝ) : ℂ) * c2GlobalGreenInputIsometry t V p := by
  have hg : ¬HasGrandparent (0, p) := odd_not_two_dvd p hp
  simp [verticalGreenStencil, currentTerm, parentTerm, grandparentTerm,
    hg, c2GlobalGreenInput_even_eq_zero, neg_mul]

theorem grandparentIndex_baseTwo_twice (p : PNat) :
    grandparentIndex (0, 2 * p) = p := by
  simpa only [grandparentIndex, baseTwo_positive_code] using divExact_base_mul 0 p

/-- This formula also holds when the second ancestor is even. -/
theorem verticalGreenStencil_baseTwo_twiceParent (t : ℝ) (V : CoreState) (p : PNat) :
    verticalGreenStencil (0, 2 * p) (c2GlobalGreenInputIsometry t V) =
      ((carryRatio 0 ^ 2 : ℝ) : ℂ) * c2GlobalGreenInputIsometry t V p := by
  have hg : HasGrandparent (0, 2 * p) := by
    change 2 ∣ 2 * (p : ℕ)
    exact dvd_mul_right _ _
  simp [verticalGreenStencil, currentTerm, parentTerm, grandparentTerm,
    hg, c2GlobalGreenInput_even_eq_zero, grandparentIndex_baseTwo_twice]

theorem verticalGreenStencil_baseTwo_twiceOddParent (t : ℝ) (V : CoreState)
    (p : PNat) (_hp : Odd (p : ℕ)) :
    verticalGreenStencil (0, 2 * p) (c2GlobalGreenInputIsometry t V) =
      (1 / 2 : ℂ) * c2GlobalGreenInputIsometry t V p := by
  rw [verticalGreenStencil_baseTwo_twiceParent, carryRatio_baseTwo_sq]
  norm_num

theorem verticalGreenStencil_baseTwo_parent_four_dvd_eq_zero (t : ℝ) (V : CoreState)
    (p : PNat) (hp : 4 ∣ (p : ℕ)) :
    verticalGreenStencil (0, p) (c2GlobalGreenInputIsometry t V) = 0 := by
  obtain ⟨a, ha⟩ := hp
  have hapos : 0 < a := by
    by_contra h
    have haz : a = 0 := Nat.eq_zero_of_not_pos h
    simp only [haz, mul_zero] at ha
    exact PNat.ne_zero p ha
  let q : PNat := ⟨a, hapos⟩
  have he : p = 2 * (2 * q) := by apply PNat.eq; change (p : ℕ) = 2 * (2 * a); omega
  rw [he, verticalGreenStencil_baseTwo_twiceParent, c2GlobalGreenInput_even_eq_zero]
  simp

theorem positionalDepth_two_two_mul_odd (p : PNat) (hp : Odd (p : ℕ)) :
    positionalDepth 2 (2 * (p : ℕ)) = 1 := by
  have hz : padicValNat 2 (p : ℕ) = 0 :=
    positionalDepth_eq_zero_of_not_dvd (b := 2) (by norm_num) p.property (odd_not_two_dvd p hp)
  change padicValNat 2 (2 * (p : ℕ)) = 1
  rw [padicValNat.mul (by norm_num) (PNat.ne_zero p), padicValNat_self]
  rw [hz]

theorem positionalDepth_two_four_mul_odd (p : PNat) (hp : Odd (p : ℕ)) :
    positionalDepth 2 (4 * (p : ℕ)) = 2 := by
  have hz : padicValNat 2 (p : ℕ) = 0 :=
    positionalDepth_eq_zero_of_not_dvd (b := 2) (by norm_num) p.property (odd_not_two_dvd p hp)
  change padicValNat 2 (4 * (p : ℕ)) = 2
  rw [padicValNat.mul (by norm_num) (PNat.ne_zero p)]
  change positionalDepth 2 4 + padicValNat 2 (p : ℕ) = 2
  rw [positionalDepth_two_four, hz]

theorem allBaseActivity_two_two_mul_odd (p : PNat) (hp : Odd (p : ℕ)) :
    allBaseActivity 2 (2 * (p : ℕ)) = Real.log 2 := by
  rw [allBaseActivity, positionalDepth_two_two_mul_odd p hp]
  simp

theorem carryCameraWeight_two_pos_of_dvd (n : ℕ) (hn : 0 < n) (hd : 2 ∣ n) :
    0 < carryCameraWeight 2 n := by
  have hn2 := Nat.le_of_dvd hn hd
  rw [carryCameraWeight, if_pos (show 1 < n ∧ 2 ≤ 2 ∧ 2 ≤ n by omega)]
  apply div_pos _ (allBaseNormalizer_pos (by omega))
  apply mul_pos (Nat.cast_pos.mpr ((positionalDepth_pos_iff_dvd (by norm_num) hn).mpr hd))
    (Real.log_pos (by norm_num))

theorem carryCameraWeight_two_two_mul_odd_pos (p : PNat) (_hp : Odd (p : ℕ)) :
    0 < carryCameraWeight 2 (2 * (p : ℕ)) :=
  carryCameraWeight_two_pos_of_dvd _ (Nat.mul_pos (by norm_num) p.property) (dvd_mul_right _ _)

theorem carryCameraWeight_two_four_mul_odd_pos (p : PNat) (_hp : Odd (p : ℕ)) :
    0 < carryCameraWeight 2 (4 * (p : ℕ)) := by
  exact carryCameraWeight_two_pos_of_dvd (4 * (p : ℕ))
    (Nat.mul_pos (by norm_num) p.property)
    (dvd_trans (by norm_num : 2 ∣ 4) (dvd_mul_right 4 (p : ℕ)))

theorem baseTwo_firstGeneration_greenCoordinate_normSq (t : ℝ) (V : CoreState)
    (p : PNat) (hp : Odd (p : ℕ)) :
    Complex.normSq (greenCoordinate canonicalCarryInfinitePartition (0, p)
      (c2GlobalGreenInputIsometry t V)) =
      carryCameraWeight 2 (2 * (p : ℕ)) * Complex.normSq (c2GlobalGreenInputIsometry t V p) := by
  rw [greenCoordinate_normSq_eq, verticalGreenStencil_baseTwo_oddParent t V p hp]
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal]
  have hmass : greenEventMass canonicalCarryInfinitePartition (0, p) =
      carryCameraWeight 2 (2 * (p : ℕ)) / 2 := by
    simp [greenEventMass]
  rw [hmass]
  have hq : (2 * carryRatio 0) * (2 * carryRatio 0) = 2 := by
    nlinarith [carryRatio_baseTwo_sq]
  rw [hq]
  ring

theorem baseTwo_secondGeneration_greenCoordinate_normSq (t : ℝ) (V : CoreState)
    (p : PNat) (_hp : Odd (p : ℕ)) :
    Complex.normSq (greenCoordinate canonicalCarryInfinitePartition (0, 2 * p)
      (c2GlobalGreenInputIsometry t V)) =
      (carryCameraWeight 2 (4 * (p : ℕ)) / 8) * Complex.normSq (c2GlobalGreenInputIsometry t V p) := by
  rw [greenCoordinate_normSq_eq, verticalGreenStencil_baseTwo_twiceParent,
    Complex.normSq_mul, Complex.normSq_ofReal, carryRatio_baseTwo_sq]
  have hmass : greenEventMass canonicalCarryInfinitePartition (0, 2 * p) =
      carryCameraWeight 2 (4 * (p : ℕ)) / 2 := by
    norm_num [greenEventMass, ← mul_assoc]
  rw [hmass]
  ring


/-- Disjoint labels for the only two generations supported by an odd material input. -/
def baseTwoGenerationEvent : OddMaterialIndex ⊕ OddMaterialIndex → GreenEvent
  | .inl p => (0, p.val)
  | .inr p => (0, 2 * p.val)

theorem baseTwoGenerationEvent_injective : Function.Injective baseTwoGenerationEvent := by
  intro i j h
  cases i with
  | inl p =>
    cases j with
    | inl q => exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd h))
    | inr q =>
      have he : (p.val : ℕ) = 2 * (q.val : ℕ) := congrArg (fun e : GreenEvent => (e.2 : ℕ)) h
      exact False.elim ((Nat.not_even_iff_odd.mpr p.property.1) ⟨(q.val : ℕ), by omega⟩)
  | inr p =>
    cases j with
    | inl q =>
      have he : 2 * (p.val : ℕ) = (q.val : ℕ) := congrArg (fun e : GreenEvent => (e.2 : ℕ)) h
      exact False.elim ((Nat.not_even_iff_odd.mpr q.property.1) ⟨(p.val : ℕ), by omega⟩)
    | inr q =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact mul_left_cancel (a := (2 : PNat)) (congrArg Prod.snd h)

private theorem odd_small_eq_one (p : PNat) (hp : Odd (p : ℕ)) (hsmall : ¬3 ≤ (p : ℕ)) : p = 1 := by
  obtain ⟨a, ha⟩ := hp
  apply PNat.eq
  change (p : ℕ) = 1
  have hpos : 0 < (p : ℕ) := p.property
  omega

private theorem even_pnat_eq_twice (p : PNat) (hp : Even (p : ℕ)) : ∃ q : PNat, p = 2 * q := by
  obtain ⟨a, ha⟩ := hp
  have hapos : 0 < a := by
    by_contra h
    have haz : a = 0 := Nat.eq_zero_of_not_pos h
    have hz : (p : ℕ) = 0 := by simpa only [haz, zero_add] using ha
    exact PNat.ne_zero p hz
  refine ⟨⟨a,hapos⟩, ?_⟩
  apply PNat.eq
  change (p : ℕ) = 2 * a
  omega

/-- Complete support statement, including the seed rows at parents one and two. -/
theorem baseTwoGreen_c2Source_eq_zero_off_generations (t : ℝ) (V : CoreState)
    (e : GreenEvent) (he : e ∉ Set.range baseTwoGenerationEvent) :
    baseTwoGreenProjection (greenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V)) e = 0 := by
  by_cases hcode : e.1 = 0
  · rcases e with ⟨r,p⟩
    change r = 0 at hcode
    subst r
    simp only [baseTwoGreenProjection_apply]
    change greenCoordinate canonicalCarryInfinitePartition (0,p) (c2GlobalGreenInputIsometry t V) = 0
    by_cases hp : Odd (p : ℕ)
    · by_cases hlarge : 3 ≤ (p : ℕ)
      · exact False.elim (he ⟨Sum.inl ⟨p,hp,hlarge⟩, rfl⟩)
      · have h1 := odd_small_eq_one p hp hlarge
        rw [greenCoordinate, verticalGreenStencil_baseTwo_oddParent t V p hp, h1,
          c2GlobalGreenInput_one]
        simp
    · obtain ⟨q,hq⟩ := even_pnat_eq_twice p (Nat.not_odd_iff_even.mp hp)
      by_cases hodd : Odd (q : ℕ)
      · by_cases hlarge : 3 ≤ (q : ℕ)
        · exact False.elim (he ⟨Sum.inr ⟨q,hodd,hlarge⟩, by simp [baseTwoGenerationEvent, hq]⟩)
        · have h1 := odd_small_eq_one q hodd hlarge
          rw [hq, greenCoordinate, verticalGreenStencil_baseTwo_twiceParent, h1,
            c2GlobalGreenInput_one]
          simp
      · rw [hq, greenCoordinate, verticalGreenStencil_baseTwo_twiceParent,
          c2GlobalGreenInput_even t V q (Nat.not_odd_iff_even.mp hodd)]
        simp
  · simp [hcode]

def baseTwoOddDiagonalWeight (p : OddMaterialIndex) : ℝ :=
  carryCameraWeight 2 (2 * (p.val : ℕ)) + carryCameraWeight 2 (4 * (p.val : ℕ)) / 8

theorem baseTwoOddDiagonalWeight_pos (p : OddMaterialIndex) : 0 < baseTwoOddDiagonalWeight p := by
  exact add_pos_of_pos_of_nonneg
    (carryCameraWeight_two_two_mul_odd_pos p.val p.property.1)
    (div_nonneg (carryCameraWeight_nonneg _ _) (by norm_num))

set_option backward.isDefEq.respectTransparency false in
/-- Exact two-generation reindexing of the whole base-two L² energy. -/
theorem baseTwoGreenStencilEnergy_eq_odd_diagonal (t : ℝ) (V : CoreState) :
    ‖baseTwoGreenProjection (greenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V))‖ ^ 2 =
      ∑' p : OddMaterialIndex, baseTwoOddDiagonalWeight p *
        Complex.normSq (c2GlobalGreenInputIsometry t V p.val) := by
  let x : ℓ²(GreenEvent, ℂ) := baseTwoGreenProjection (greenAnalysis canonicalCarryInfinitePartition
    (c2GlobalGreenInputIsometry t V))
  have hs : Summable (fun e : GreenEvent => Complex.normSq (x e)) := residualL2_normSq_summable x
  have hsleft : Summable (fun p : OddMaterialIndex => Complex.normSq (x (0,p.val))) := by
    apply (hs.comp_injective (baseTwoGenerationEvent_injective.comp Sum.inl_injective)).congr
    intro p
    rfl
  have hsright : Summable (fun p : OddMaterialIndex => Complex.normSq (x (0,2*p.val))) := by
    apply (hs.comp_injective (baseTwoGenerationEvent_injective.comp Sum.inr_injective)).congr
    intro p
    rfl
  have hsupport : Function.support (fun e : GreenEvent => Complex.normSq (x e)) ⊆ Set.range baseTwoGenerationEvent := by
    intro e he
    by_contra h
    have hz : x e = 0 := baseTwoGreen_c2Source_eq_zero_off_generations t V e h
    change Complex.normSq (x e) ≠ 0 at he
    exact he ((congrArg Complex.normSq hz).trans (by norm_num))
  calc
    ‖x‖ ^ 2 = ∑' e : GreenEvent, Complex.normSq (x e) :=
      (residualL2_normSq_tsum_eq_norm_sq x).symm
    _ = ∑' i : OddMaterialIndex ⊕ OddMaterialIndex, Complex.normSq (x (baseTwoGenerationEvent i)) :=
      (baseTwoGenerationEvent_injective.tsum_eq hsupport).symm
    _ = (∑' p : OddMaterialIndex, Complex.normSq (x (0,p.val))) +
        ∑' p : OddMaterialIndex, Complex.normSq (x (0,2*p.val))  := Summable.tsum_sum
          (f := fun i : OddMaterialIndex ⊕ OddMaterialIndex => Complex.normSq (x (baseTwoGenerationEvent i)))
          hsleft hsright
    _ = ∑' p : OddMaterialIndex, (Complex.normSq (x (0,p.val)) + Complex.normSq (x (0,2*p.val))) :=
      (hsleft.tsum_add hsright).symm
    _ = ∑' p : OddMaterialIndex, baseTwoOddDiagonalWeight p *
        Complex.normSq (c2GlobalGreenInputIsometry t V p.val) := by
      apply tsum_congr
      intro p
      change Complex.normSq (greenCoordinate canonicalCarryInfinitePartition (0,p.val)
        (c2GlobalGreenInputIsometry t V)) +
        Complex.normSq (greenCoordinate canonicalCarryInfinitePartition (0,2*p.val)
          (c2GlobalGreenInputIsometry t V)) = _
      rw [baseTwo_firstGeneration_greenCoordinate_normSq t V p.val p.property.1,
        baseTwo_secondGeneration_greenCoordinate_normSq t V p.val p.property.1]
      unfold baseTwoOddDiagonalWeight
      ring

theorem c2GlobalGreenInput_exists_nonzero_odd_coordinate (t : ℝ) (V : CoreState)
    (h : c2GlobalGreenInputIsometry t V ≠ 0) :
    ∃ p : OddMaterialIndex, c2GlobalGreenInputIsometry t V p.val ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  apply lp.ext
  funext p
  by_cases hp : Odd (p : ℕ) ∧ 3 ≤ (p : ℕ)
  · exact hn ⟨p,hp⟩
  · change oddMaterialToGreenState (globalCriticalPhysicalBranchIsometry t V) p = 0
    exact oddMaterialToGreenState_apply_off_sector _ p hp

theorem baseTwoGreenStencilEnergy_pos_of_c2Source_ne_zero (t : ℝ) (V : CoreState)
    (h : c2GlobalGreenInputIsometry t V ≠ 0) :
    0 < ‖baseTwoGreenProjection (greenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V))‖ ^ 2 := by
  obtain ⟨p,hp⟩ := c2GlobalGreenInput_exists_nonzero_odd_coordinate t V h
  let x := baseTwoGreenProjection (greenAnalysis canonicalCarryInfinitePartition
    (c2GlobalGreenInputIsometry t V))
  have ht : 0 < Complex.normSq (x (0,p.val)) := by
    change 0 < Complex.normSq (greenCoordinate canonicalCarryInfinitePartition (0,p.val)
      (c2GlobalGreenInputIsometry t V))
    rw [baseTwo_firstGeneration_greenCoordinate_normSq t V p.val p.property.1]
    exact mul_pos (carryCameraWeight_two_two_mul_odd_pos p.val p.property.1)
      (Complex.normSq_pos.mpr hp)
  have hle := (residualL2_normSq_summable x).le_tsum (0,p.val)
    (fun e _ => Complex.normSq_nonneg (x e))
  rw [residualL2_normSq_tsum_eq_norm_sq] at hle
  exact lt_of_lt_of_le ht hle

theorem baseTwoGreenStencilEnergy_pos_of_core_ne_zero (t : ℝ) (V : CoreState) (h : V ≠ 0) :
    0 < ‖baseTwoGreenProjection (greenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V))‖ ^ 2 := by
  apply baseTwoGreenStencilEnergy_pos_of_c2Source_ne_zero
  intro hz
  apply h
  apply (c2GlobalGreenInputIsometry t).injective
  simpa using hz

def baseTwoDefect (t : ℝ) (V : CoreState) : ℝ :=
  ‖baseTwoGreenProjection (greenAnalysis canonicalCarryInfinitePartition
    (c2GlobalGreenInputIsometry t V))‖ ^ 2 -
  ‖baseTwoGreenProjection (directGreenAnalysis canonicalCarryInfinitePartition
    (c2GlobalGreenInputIsometry t V))‖ ^ 2

theorem baseTwoDefect_eq_stencilEnergy (t : ℝ) (V : CoreState) :
    baseTwoDefect t V = ‖baseTwoGreenProjection (greenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V))‖ ^ 2 := by
  simp [baseTwoDefect, baseTwo_directGreenAnalysis_c2Source_eq_zero]

theorem baseTwoDefect_pos (t : ℝ) (V : CoreState) (h : V ≠ 0) : 0 < baseTwoDefect t V := by
  rw [baseTwoDefect_eq_stencilEnergy]
  exact baseTwoGreenStencilEnergy_pos_of_core_ne_zero t V h

/-- The two camera sectors are orthogonal coordinate masks, for every L² vector. -/
theorem baseTwo_nonBaseTwo_norm_sq_add (x : ℓ²(GreenEvent, ℂ)) :
    ‖baseTwoGreenProjection x‖ ^ 2 + ‖nonBaseTwoGreenProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [← residualL2_normSq_tsum_eq_norm_sq, ← residualL2_normSq_tsum_eq_norm_sq,
    ← residualL2_normSq_tsum_eq_norm_sq,
    ← (residualL2_normSq_summable (baseTwoGreenProjection x)).tsum_add
      (residualL2_normSq_summable (nonBaseTwoGreenProjection x))]
  apply tsum_congr
  intro e
  by_cases he : e.1 = 0 <;> simp [he]

def nonBaseTwoDefect (t : ℝ) (V : CoreState) : ℝ :=
  ‖nonBaseTwoGreenProjection (greenAnalysis canonicalCarryInfinitePartition
    (c2GlobalGreenInputIsometry t V))‖ ^ 2 -
  ‖nonBaseTwoGreenProjection (directGreenAnalysis canonicalCarryInfinitePartition
    (c2GlobalGreenInputIsometry t V))‖ ^ 2

theorem c2GlobalRawGreenDefect_eq_camera_ledger (t : ℝ) (V : CoreState) :
    c2GlobalRawGreenDefect t V = baseTwoDefect t V + nonBaseTwoDefect t V := by
  rw [c2GlobalRawGreenDefect_eq_stencil_defect,
    ← baseTwo_nonBaseTwo_norm_sq_add (greenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V)),
    ← baseTwo_nonBaseTwo_norm_sq_add (directGreenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V))]
  unfold baseTwoDefect nonBaseTwoDefect
  ring

theorem restrictedGram_eq_identity_implies_nonBaseTwo_exact_cancellation (t : ℝ)
    (h : c2GlobalRestrictedGreenGram t = 1) (V : CoreState) :
    nonBaseTwoDefect t V = -baseTwoDefect t V := by
  have hz : c2GlobalRawGreenDefect t V = 0 :=
    (c2GlobalRestrictedGreenGram_eq_one_iff_defect_zero t).mp h V
  rw [c2GlobalRawGreenDefect_eq_camera_ledger] at hz
  linarith

theorem restrictedGram_eq_identity_implies_nonBaseTwo_negative (t : ℝ)
    (hG : c2GlobalRestrictedGreenGram t = 1) (V : CoreState) (hV : V ≠ 0) :
    nonBaseTwoDefect t V < 0 := by
  rw [restrictedGram_eq_identity_implies_nonBaseTwo_exact_cancellation t hG V]
  exact neg_neg_of_pos (baseTwoDefect_pos t V hV)

/-- Pointwise source energy inherits the already proved real rotation invariance. -/
theorem c2GlobalGreenInput_normSq_independent_time (t s : ℝ) (V : CoreState)
    (p : OddMaterialIndex) :
    Complex.normSq (c2GlobalGreenInputIsometry t V p.val) =
      Complex.normSq (c2GlobalGreenInputIsometry s V p.val) := by
  rw [c2GlobalGreenInput_apply, c2GlobalGreenInput_apply,
    realPlaneToComplexIsometry_normSq, realPlaneToComplexIsometry_normSq]
  simp only [LinearEquiv.symm_apply_apply, scaleRealPlane_energy, rotateRealPlane_energy]

theorem baseTwoDefect_independent_time (t s : ℝ) (V : CoreState) :
    baseTwoDefect t V = baseTwoDefect s V := by
  rw [baseTwoDefect_eq_stencilEnergy, baseTwoDefect_eq_stencilEnergy,
    baseTwoGreenStencilEnergy_eq_odd_diagonal, baseTwoGreenStencilEnergy_eq_odd_diagonal]
  apply tsum_congr
  intro p
  rw [c2GlobalGreenInput_normSq_independent_time t s V p]


end GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
