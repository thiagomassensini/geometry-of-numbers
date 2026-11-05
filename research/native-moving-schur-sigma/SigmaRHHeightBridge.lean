import SigmaRemainderDescent
import RHHeightEulerMaclaurin
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Finite-height Riemann-zeta data for the native sigma isolation target

This file is the Lean 4.32 bridge from the externally proved finite-height zero statements to
the zero and order statements needed by `SigmaDisplacedProductIsolation`.  The external results
are represented here by their mathematical propositions, rather than by importing compiled
artifacts from the Lean 4.35 checkout.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator Complex Set
open CPFormal.Analytic.Cp
open HardyFirstZero
open Filter Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The exact positive-ordinate strip window counted by the height-50 certificate. -/
def sigmaRHStripZerosUpTo (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- RH with simplicity on the open critical strip through positive height 50. -/
def sigmaRHHeight50 : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 50 →
    ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1

/-- The exact distinct-zero count in the positive-ordinate strip window. -/
def sigmaZeroCount50 : Prop := (sigmaRHStripZerosUpTo 50).ncard = 10

/-- The first computed critical-line zero and its certified rational bracket. -/
def sigmaFirstZeroBracket : Prop :=
  ∃ t : ℝ, t ∈ Set.Ioo (1413 / 100 : ℝ) (1414 / 100) ∧
    riemannZeta (1 / 2 + t * Complex.I) = 0

/-- The ten disjoint ordinate boxes from the external Hardy-zero calculation. -/
def sigmaTenZeroBoxLower : Fin 10 → ℝ :=
  ![1413 / 100, 2102 / 100, 2501 / 100, 3042 / 100, 3293 / 100,
    3758 / 100, 4091 / 100, 4332 / 100, 4800 / 100, 4977 / 100]

/-- Upper endpoints of the ten disjoint ordinate boxes. -/
def sigmaTenZeroBoxUpper : Fin 10 → ℝ :=
  ![1414 / 100, 2103 / 100, 2502 / 100, 3043 / 100, 3294 / 100,
    3759 / 100, 4092 / 100, 4333 / 100, 4801 / 100, 4978 / 100]

/-- The ten externally certified line zeros, retaining each exact box. -/
def sigmaTenZeroBoxes : Prop :=
  ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
    ∀ i : Fin 10,
      ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i) ∧
        riemannZeta (1 / 2 + ts i * Complex.I) = 0

/-- Ten certified ordinate boxes whose first member is the zero supplied by
`sigmaFirstZeroBracket`. The external ten-zero construction uses that same first-zero witness. -/
def sigmaTenZeroBoxesWithFirst (γ : ℝ) : Prop :=
  ∃ ts : Fin 10 → ℝ, ts 0 = γ ∧ StrictMono ts ∧
    ∀ i : Fin 10,
      ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i) ∧
        riemannZeta (1 / 2 + ts i * Complex.I) = 0

def sigmaLineZero (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

/-- The nine individual height-50 box certificates after the first interval. Their disjoint
locations give an increasing sequence without assuming the aggregate theorem preserves boxes. -/
def sigmaNineZeroBoxes : Prop :=
  ∃ ts : Fin 9 → ℝ, ∀ i : Fin 9,
    ts i ∈ Set.Ioo (sigmaTenZeroBoxLower (Fin.succ i))
      (sigmaTenZeroBoxUpper (Fin.succ i)) ∧
      riemannZeta (1 / 2 + ts i * Complex.I) = 0

theorem sigmaTenZeroBoxesWithFirst_of_first_and_nine
    (γ : ℝ)
    (hγbox : γ ∈ Set.Ioo (1413 / 100 : ℝ) (1414 / 100))
    (hγzero : riemannZeta (sigmaLineZero γ) = 0)
    (hnine : sigmaNineZeroBoxes) : sigmaTenZeroBoxesWithFirst γ := by
  obtain ⟨ts, hts⟩ := hnine
  let us : Fin 10 → ℝ := Fin.cases γ ts
  refine ⟨us, ?_, ?_, ?_⟩
  · rfl
  · refine Fin.strictMono_iff_lt_succ.mpr ?_
    intro i
    cases i using Fin.cases with
    | zero =>
        change γ < ts 0
        have hγupper := hγbox.2
        have hnextlower := (hts 0).1.1
        norm_num [sigmaTenZeroBoxLower, sigmaTenZeroBoxUpper] at hγupper hnextlower ⊢
        linarith
    | succ i =>
        change ts (Fin.castSucc i) < ts (Fin.succ i)
        have hcurrent := (hts (Fin.castSucc i)).1
        have hnext := (hts (Fin.succ i)).1
        have hgap : sigmaTenZeroBoxUpper (Fin.succ (Fin.castSucc i)) <
            sigmaTenZeroBoxLower (Fin.succ (Fin.succ i)) := by
          fin_cases i <;>
            simp [sigmaTenZeroBoxUpper, sigmaTenZeroBoxLower, Fin.succ, Fin.castSucc] <;>
            norm_num
        exact lt_trans hcurrent.2 (lt_trans hgap hnext.1)
  · intro i
    cases i using Fin.cases with
    | zero =>
        constructor
        · simpa [us, sigmaTenZeroBoxLower, sigmaTenZeroBoxUpper] using hγbox
        · simpa [us, sigmaLineZero] using hγzero
    | succ i => simpa [us, sigmaLineZero] using hts i

lemma sigmaLineZero_mem_stripZeros50 {t : ℝ} (ht : 0 < t) (ht50 : t ≤ 50)
    (hzero : riemannZeta (sigmaLineZero t) = 0) :
    sigmaLineZero t ∈ sigmaRHStripZerosUpTo 50 := by
  have hre : (sigmaLineZero t).re = 1 / 2 := by simp [sigmaLineZero]
  have him : (sigmaLineZero t).im = t := by simp [sigmaLineZero]
  simp only [sigmaRHStripZerosUpTo, Set.mem_setOf_eq]
  refine ⟨hzero, ?_, ?_, ?_, ?_⟩
  · rw [hre]
    norm_num
  · rw [hre]
    norm_num
  · rw [him]
    exact ht
  · rw [him]
    exact ht50

lemma sigmaTenZeroLower_pos (i : Fin 10) : 0 < sigmaTenZeroBoxLower i := by
  fin_cases i <;> norm_num [sigmaTenZeroBoxLower]

lemma sigmaTenZeroUpper_lt_fifty (i : Fin 10) : sigmaTenZeroBoxUpper i < 50 := by
  fin_cases i <;> norm_num [sigmaTenZeroBoxUpper]

lemma sigmaTenZeroLower_after_first (i : Fin 10) (hi : i.val ≠ 0) :
    (2102 / 100 : ℝ) ≤ sigmaTenZeroBoxLower i := by
  fin_cases i <;> norm_num [sigmaTenZeroBoxLower] at *

/-- The ten line zeros exhaust the height-50 count. Consequently any other positive line zero
below `√300` is impossible; the next certified box already starts above that radius. -/
theorem sigmaLineZero_small_eq_first
    (γ : ℝ)
    (hcount : sigmaZeroCount50) (hboxes : sigmaTenZeroBoxesWithFirst γ)
    {t : ℝ} (ht : 0 < t) (htsqrt : t < Real.sqrt 300)
    (hzero : riemannZeta (sigmaLineZero t) = 0) : t = γ := by
  obtain ⟨ts, hts0, htsMono, htsBoxes⟩ := hboxes
  let K : Set ℂ := (fun i : Fin 10 => sigmaLineZero (ts i)) '' Set.univ
  have hts_in_count (i : Fin 10) : sigmaLineZero (ts i) ∈ sigmaRHStripZerosUpTo 50 := by
    have hb := (htsBoxes i).1
    apply sigmaLineZero_mem_stripZeros50
    · exact lt_trans (sigmaTenZeroLower_pos i) hb.1
    · exact le_of_lt (lt_trans hb.2 (sigmaTenZeroUpper_lt_fifty i))
    · simpa [sigmaLineZero] using (htsBoxes i).2
  have hK_sub : K ⊆ sigmaRHStripZerosUpTo 50 := by
    rintro ρ ⟨i, -, rfl⟩
    exact hts_in_count i
  have hmap_inj : Function.Injective (fun i : Fin 10 => sigmaLineZero (ts i)) := by
    intro i j hij
    apply htsMono.injective
    have him := congrArg Complex.im hij
    simpa [sigmaLineZero] using him
  have hK_card : K.ncard = 10 := by
    dsimp [K]
    rw [Set.ncard_image_of_injective Set.univ hmap_inj]
    simp
  have hcountEq : (sigmaRHStripZerosUpTo 50).ncard = 10 := hcount
  have hZ_finite : (sigmaRHStripZerosUpTo 50).Finite := by
    apply Set.finite_of_ncard_pos
    rw [hcountEq]
    norm_num
  have hsqrt50 : Real.sqrt 300 < 50 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 300 := Real.sqrt_nonneg _
    have hsquare : (Real.sqrt 300) ^ 2 = 300 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hnew_in_count : sigmaLineZero t ∈ sigmaRHStripZerosUpTo 50 := by
    apply sigmaLineZero_mem_stripZeros50 ht (le_of_lt (lt_trans htsqrt hsqrt50)) hzero
  have hKfinite : K.Finite := Set.Finite.image _ Set.finite_univ
  have hnew_mem_K : sigmaLineZero t ∈ K := by
    by_contra hnot
    have hins : insert (sigmaLineZero t) K ⊆ sigmaRHStripZerosUpTo 50 := by
      intro ρ hρ
      rcases hρ with rfl | hρ
      · exact hnew_in_count
      · exact hK_sub hρ
    have hcardIns : (insert (sigmaLineZero t) K).ncard = 11 := by
      rw [Set.ncard_insert_of_notMem hnot hKfinite, hK_card]
    have hle := Set.ncard_le_ncard hins hZ_finite
    rw [hcountEq] at hle
    omega
  rcases hnew_mem_K with ⟨i, -, hi⟩
  have hti : t = ts i := by
    have him := congrArg Complex.im hi
    simpa [sigmaLineZero] using him.symm
  by_cases hi0 : i.val = 0
  · have hiEq : i = 0 := Fin.ext hi0
    subst i
    simpa [hts0] using hti
  · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi0
    have hlow : (2102 / 100 : ℝ) < ts i := by
      exact lt_of_le_of_lt (sigmaTenZeroLower_after_first i hi0) (htsBoxes i).1.1
    have hsqrtNext : Real.sqrt 300 < 2102 / 100 := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt 300 := Real.sqrt_nonneg _
      have hsquare : (Real.sqrt 300) ^ 2 = 300 := Real.sq_sqrt (by norm_num)
      nlinarith
    linarith [htsqrt, hti]

/-- The Euler--Maclaurin tail bound at the first block, ported from the pinned external
height-50 development to this checkout's Lean 4.32 toolchain. -/
theorem sigmaNormTailOneLe {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖∑' k : ℕ, eBlock s ((k + 1 : ℕ) : ℝ)‖ ≤
      ‖P4 s‖ * (1 + 1 / (s.re + 3)) / 720 := by
  have hsum : Summable (fun k : ℕ => eBlock s ((k + 1 : ℕ) : ℝ)) := by
    refine Summable.of_norm_bounded
      (g := fun k : ℕ => ‖P4 s‖ * (((k + 1 : ℕ) : ℝ)) ^ (-s.re - 4) / 720) ?_ ?_
    · have hb : Summable (fun k : ℕ => ((k : ℝ)) ^ (-s.re - 4)) :=
        Real.summable_nat_rpow.mpr (by linarith)
      have hb1 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ (-s.re - 4)) :=
        (summable_nat_add_iff 1).mpr hb
      exact (hb1.mul_left _).div_const _
    · intro k
      exact norm_eBlock_le hs hs1 (Nat.one_le_cast.mpr (Nat.succ_pos k))
  have hsplit : ∑' k : ℕ, eBlock s ((k + 1 : ℕ) : ℝ) =
      eBlock s ((0 + 1 : ℕ) : ℝ) + ∑' k : ℕ, eBlock s ((k + 2 : ℕ) : ℝ) :=
    hsum.tsum_eq_zero_add
  have hfirst : ‖eBlock s ((0 + 1 : ℕ) : ℝ)‖ ≤ ‖P4 s‖ / 720 := by
    have h := norm_eBlock_le hs hs1 (x := ((0 + 1 : ℕ) : ℝ)) (by norm_num)
    simpa using h
  have hrest : ‖∑' k : ℕ, eBlock s ((k + 2 : ℕ) : ℝ)‖ ≤
      ‖P4 s‖ * (1 / (s.re + 3)) / 720 := by
    have h := norm_tail_le hs hs1 (N := 2) le_rfl
    have e : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
    rw [e, Real.one_rpow] at h
    exact h
  rw [hsplit]
  calc
    ‖eBlock s ((0 + 1 : ℕ) : ℝ) + ∑' k : ℕ, eBlock s ((k + 2 : ℕ) : ℝ)‖ ≤
        ‖eBlock s ((0 + 1 : ℕ) : ℝ)‖ +
          ‖∑' k : ℕ, eBlock s ((k + 2 : ℕ) : ℝ)‖ := norm_add_le _ _
    _ ≤ ‖P4 s‖ / 720 + ‖P4 s‖ * (1 / (s.re + 3)) / 720 := add_le_add hfirst hrest
    _ = ‖P4 s‖ * (1 + 1 / (s.re + 3)) / 720 := by ring

/-- The order-4 Euler--Maclaurin representation gives a local error bound for ζ in the upper
quarter plane. -/
theorem sigmaNormZetaSubMainOneLe {s : ℂ} (hs : s ∈ QP) :
    ‖riemannZeta s - (s + 2) * (s + 3) / (12 * (s - 1))‖ ≤
      ‖P4 s‖ * (1 + 1 / (s.re + 3)) / 720 := by
  have hs1 : s ≠ 1 := ne_one_of_QP hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [QP] at hs
  have hem := zeta_em4 hs (N := 1) le_rfl
  unfold emRHS at hem
  simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one, Complex.one_cpow,
    Complex.zero_cpow (neg_ne_zero.mpr hs0), mul_one, zero_add] at hem
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hmain : (1 : ℂ) / (s - 1) + 1 / 2 + s / 12 =
      (s + 2) * (s + 3) / (12 * (s - 1)) := by
    field_simp
    ring
  rw [hem, hmain, sub_sub_cancel_left, norm_neg]
  exact sigmaNormTailOneLe hs.1 hs1

/-- On the upper strip `0 < Re s < 1`, `0 < Im s ≤ 1`, the Euler--Maclaurin main term
dominates its remainder by a fixed margin. This quantitative form extends to the real boundary
by continuity and rules out a zero of ζ at ordinate zero. -/
theorem sigmaZetaNormGeOneNinth {s : ℂ} (hs : s ∈ QP)
    (hsre1 : s.re < 1) (hsim1 : s.im ≤ 1) :
    (1 / 9 : ℝ) ≤ ‖riemannZeta s‖ := by
  have hbound := sigmaNormZetaSubMainOneLe hs
  have hM : (1 / 3 : ℝ) < ‖(s + 2) * (s + 3) / (12 * (s - 1))‖ := by
    have hre2 : 2 < (s + 2).re := by simp; linarith [hs.1]
    have hre3 : 3 < (s + 3).re := by simp; linarith [hs.1]
    have hsminus : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (ne_one_of_QP hs))
    have hsminusSq : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have hsminusLt : ‖s - 1‖ < 3 / 2 := by
      have hxSq : (s.re - 1) ^ 2 ≤ 1 := by nlinarith [hs.1, hsre1]
      have hySq : s.im ^ 2 ≤ 1 := by nlinarith [hs.2, hsim1]
      have hn := norm_nonneg (s - 1)
      nlinarith [hsminusSq, hxSq, hySq]
    have hnorm : ‖(s + 2) * (s + 3) / (12 * (s - 1))‖ =
        (‖s + 2‖ * ‖s + 3‖) / (12 * ‖s - 1‖) := by
      rw [norm_div, norm_mul, norm_mul]
      norm_num
    rw [hnorm]
    have hnum : 6 < ‖s + 2‖ * ‖s + 3‖ := by
      have h1 := Complex.re_le_norm (s + 2)
      have h2 := Complex.re_le_norm (s + 3)
      nlinarith [hre2, hre3]
    have hden : 0 < 12 * ‖s - 1‖ := mul_pos (by norm_num) hsminus
    have hdenLt : 12 * ‖s - 1‖ < 18 := by nlinarith [hsminusLt]
    have := div_lt_div_of_pos_right hnum hden
    have hquot : 6 / (12 * ‖s - 1‖) > 1 / 3 := by
      rw [gt_iff_lt, lt_div_iff₀ hden]
      nlinarith [hdenLt]
    exact lt_trans hquot this
  have hnorms : ‖s‖ ≤ 2 ∧ ‖s + 1‖ ≤ 3 ∧ ‖s + 2‖ ≤ 4 ∧ ‖s + 3‖ ≤ 5 := by
    have h0 : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have h1 : ‖s + 1‖ ^ 2 = (s.re + 1) ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have h2 : ‖s + 2‖ ^ 2 = (s.re + 2) ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have h3 : ‖s + 3‖ ^ 2 = (s.re + 3) ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have hsreSq : s.re ^ 2 ≤ 1 := by nlinarith [hs.1, hsre1]
    have hsimSq : s.im ^ 2 ≤ 1 := by nlinarith [hs.2, hsim1]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hn := norm_nonneg s
      nlinarith [h0, hsreSq, hsimSq]
    · have hn := norm_nonneg (s + 1)
      have hx : (s.re + 1) ^ 2 ≤ 4 := by nlinarith [hsre1]
      nlinarith [h1, hx, hsimSq]
    · have hn := norm_nonneg (s + 2)
      have hx : (s.re + 2) ^ 2 ≤ 9 := by nlinarith [hsre1]
      nlinarith [h2, hx, hsimSq]
    · have hn := norm_nonneg (s + 3)
      have hx : (s.re + 3) ^ 2 ≤ 16 := by nlinarith [hsre1]
      nlinarith [h3, hx, hsimSq]
  have hP : ‖P4 s‖ ≤ 120 := by
    rw [P4, norm_mul, norm_mul, norm_mul]
    calc
      ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ ≤ 2 * 3 * 4 * 5 := by
        gcongr
        · exact hnorms.1
        · exact hnorms.2.1
        · exact hnorms.2.2.1
        · exact hnorms.2.2.2
      _ = 120 := by norm_num
  have herr : ‖P4 s‖ * (1 + 1 / (s.re + 3)) / 720 ≤ 2 / 9 := by
    have hfrac : 1 / (s.re + 3) ≤ 1 / 3 := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) (by linarith [hs.1])
    have hden : 0 < s.re + 3 := by linarith [hs.1]
    have hfactor_nonneg : 0 ≤ 1 + 1 / (s.re + 3) := by positivity
    calc
      ‖P4 s‖ * (1 + 1 / (s.re + 3)) / 720 ≤ 120 * (1 + 1 / 3) / 720 := by
        apply div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℝ) ≤ 720)
        calc
          ‖P4 s‖ * (1 + 1 / (s.re + 3)) ≤
              120 * (1 + 1 / (s.re + 3)) :=
            mul_le_mul_of_nonneg_right hP hfactor_nonneg
          _ ≤ 120 * (1 + 1 / 3) :=
            mul_le_mul_of_nonneg_left (by linarith [hfrac]) (by norm_num)
      _ = 2 / 9 := by norm_num
  have htri : ‖(s + 2) * (s + 3) / (12 * (s - 1))‖ ≤
      ‖(s + 2) * (s + 3) / (12 * (s - 1)) - riemannZeta s‖ + ‖riemannZeta s‖ := by
    calc
      _ = ‖((s + 2) * (s + 3) / (12 * (s - 1)) - riemannZeta s) + riemannZeta s‖ := by
        congr 1
        ring
      _ ≤ _ := norm_add_le _ _
  have hrem : ‖(s + 2) * (s + 3) / (12 * (s - 1)) - riemannZeta s‖ ≤ 2 / 9 := by
    have hnorm : ‖(s + 2) * (s + 3) / (12 * (s - 1)) - riemannZeta s‖ =
        ‖riemannZeta s - (s + 2) * (s + 3) / (12 * (s - 1))‖ := by
      rw [← neg_sub, norm_neg]
    rw [hnorm]
    exact hbound.trans herr
  linarith

/-- Zeta has no real zeros in the open critical strip. The upper-half-plane estimate above is
uniform as the ordinate tends to zero, and analyticity of ζ carries the positive lower bound to
the real boundary. -/
theorem riemannZeta_ne_zero_of_real_strip {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  let sseq : ℕ → ℂ := fun n =>
    (x : ℂ) + Complex.I * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hseq : Tendsto sseq atTop (𝓝 (x : ℂ)) := by
    have hrecipR : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop
        (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hrecip : Tendsto
        (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hrecipR
    have hmul : Tendsto (fun n : ℕ => Complex.I *
        ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := Complex.I)).mul hrecip
    simpa [sseq] using (tendsto_const_nhds (x := (x : ℂ))).add hmul
  have hlim : Tendsto (fun n : ℕ => ‖riemannZeta (sseq n)‖) atTop
      (𝓝 ‖riemannZeta (x : ℂ)‖) := by
    have hxne : (x : ℂ) ≠ 1 := by
      intro h
      have h' : x = 1 := by exact_mod_cast h
      linarith
    have hζ : ContinuousAt riemannZeta (x : ℂ) :=
      (differentiableAt_riemannZeta hxne).continuousAt
    exact (continuous_norm.continuousAt.comp hζ).tendsto.comp hseq
  have hlower : ∀ n : ℕ, (1 / 9 : ℝ) ≤ ‖riemannZeta (sseq n)‖ := by
    intro n
    have hRe : (sseq n).re = x := by simp [sseq]
    have hIm : (sseq n).im = 1 / ((n : ℝ) + 1) := by
      simp only [sseq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_add, zero_mul, one_mul]
    have hImPos : 0 < (sseq n).im := by rw [hIm]; positivity
    have hImLe : (sseq n).im ≤ 1 := by
      rw [hIm]
      have hle : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hle
    have hQP : sseq n ∈ QP := by rw [QP]; exact ⟨by rw [hRe]; exact hx0, hImPos⟩
    exact sigmaZetaNormGeOneNinth hQP (by rw [hRe]; exact hx1) hImLe
  have hlimitLower : (1 / 9 : ℝ) ≤ ‖riemannZeta (x : ℂ)‖ :=
    ge_of_tendsto' hlim hlower
  intro hzero
  have : ‖riemannZeta (x : ℂ)‖ = 0 := by rw [hzero]; simp
  rw [this] at hlimitLower
  norm_num at hlimitLower

/-- The entire completed-zeta expression in its natural spectral parameter. -/
def sigmaCompletedXiParameter (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

lemma completedNativeCharacteristicContinuation_eq_sigmaCompletedXiParameter (z : ℂ) :
    completedNativeCharacteristicContinuation z =
      sigmaCompletedXiParameter (operatorHeightParameter z) := rfl

/-- Away from the pole at one, the completed entire function is the usual completed zeta
multiplied by Mathlib's zeta. This identity is used outside the strip to rule out roots; it also
makes clear why trivial zeta zeros are cancelled by the gamma poles rather than becoming zeros
of the completed characteristic. -/
lemma sigmaCompletedXiParameter_eq_completedFactor_mul_zeta {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    sigmaCompletedXiParameter s =
      (1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    have hr : s.re = 0 := by simpa using congrArg Complex.re h
    linarith
  have hgam : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.div_re]; norm_num; linarith)
  have hgam1 : Complex.Gamma (s / 2 + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.div_re]; norm_num; linarith)
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr Real.pi_pos.ne')]
    exact Complex.exp_ne_zero _
  unfold sigmaCompletedXiParameter
  rw [riemannZeta_eq_mul_completedRiemannZeta₀ s, Complex.Gammaℝ_def,
    Complex.Gamma_add_one (s / 2) (div_ne_zero hs0 (by norm_num : (2 : ℂ) ≠ 0))]
  field_simp [hs0, hs1, hgam, hgam1, hpi]
  ring

lemma sigmaCompletedXiParameter_one_sub (s : ℂ) :
    sigmaCompletedXiParameter (1 - s) = sigmaCompletedXiParameter s := by
  rw [sigmaCompletedXiParameter, sigmaCompletedXiParameter,
    completedRiemannZeta₀_one_sub]
  ring

/-- The entire completed characteristic has no zero in the closed right half-plane. At `s = 1`
its value is `1/2`; elsewhere the gamma completion factor is nonzero and Mathlib's Euler-product
theorem excludes zeta zeros for `Re s ≥ 1`. -/
lemma sigmaCompletedXiParameter_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    sigmaCompletedXiParameter s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    norm_num [sigmaCompletedXiParameter]
  · have hpos : 0 < s.re := by linarith
    have hzero : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
    have hfactor := sigmaCompletedXiParameter_eq_completedFactor_mul_zeta hpos hs1
    have hs0 : s ≠ 0 := by
      intro h
      have hr : s.re = 0 := by simpa using congrArg Complex.re h
      linarith
    have hsSub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hgamma : Complex.Gammaℝ s ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos hpos
    have hnonzero :
        (1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s * riemannZeta s ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hsSub)
        hgamma) hzero
    intro h
    rw [h] at hfactor
    exact hnonzero hfactor.symm

/-- Zeros of the entire completed characteristic lie in the open critical strip. The functional
equation handles the left half-plane, while the right half-plane is excluded by nonvanishing of
zeta and its completion. This argument is for the completed Xi expression: trivial zeta zeros at
negative even integers are not treated as zeros of Xi. It does not assume a nonzero ordinate. -/
theorem sigmaCompletedXiParameter_zero_mem_genuineCriticalStrip {s : ℂ}
    (hzero : sigmaCompletedXiParameter s = 0) : s ∈ genuineCriticalStrip := by
  by_cases hleft : 0 < s.re
  · by_cases hright : s.re < 1
    · exact ⟨hleft, hright⟩
    · have hright' : 1 ≤ s.re := le_of_not_gt hright
      exfalso
      exact (sigmaCompletedXiParameter_ne_zero_of_one_le_re hright') hzero
  · have hleft' : s.re ≤ 0 := le_of_not_gt hleft
    have hreflect : sigmaCompletedXiParameter (1 - s) = 0 := by
      rw [sigmaCompletedXiParameter_one_sub]
      exact hzero
    have hreflectRe : 1 ≤ (1 - s).re := by simp; linarith
    exfalso
    exact (sigmaCompletedXiParameter_ne_zero_of_one_le_re hreflectRe) hreflect

/-- Every zero of the entire native continuation maps into the open critical strip under
`s = 1/2 + i z`, including the case where the ordinate is zero. -/
theorem completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip
    {z : ℂ} (hzero : completedNativeCharacteristicContinuation z = 0) :
    operatorHeightParameter z ∈ genuineCriticalStrip := by
  rw [completedNativeCharacteristicContinuation_eq_sigmaCompletedXiParameter] at hzero
  exact sigmaCompletedXiParameter_zero_mem_genuineCriticalStrip hzero

lemma operatorHeightParameter_re (z : ℂ) :
    (operatorHeightParameter z).re = 1 / 2 - z.im := by
  simp [CarrySelfAdjointOperator.operatorHeightParameter]
  ring

lemma operatorHeightParameter_im (z : ℂ) :
    (operatorHeightParameter z).im = z.re := by
  simp [CarrySelfAdjointOperator.operatorHeightParameter]

lemma operatorHeightParameter_analyticAt (z : ℂ) :
    AnalyticAt ℂ operatorHeightParameter z := by
  change AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) z
  fun_prop

lemma operatorHeightParameter_continuousAt (z : ℂ) :
    ContinuousAt operatorHeightParameter z := by
  change ContinuousAt (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) z
  fun_prop

lemma sigmaNativeCompletionFactor_ne_zero_of_strip {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    nativeXiCompletionFactor z ≠ 0 := by
  let s := operatorHeightParameter z
  have hsre : 0 < s.re := by simpa [s] using hs.1
  have hsrlt : s.re < 1 := by simpa [s] using hs.2
  have hs0 : s ≠ 0 := by
    intro h
    have hr : s.re = 0 := by simpa using congrArg Complex.re h
    linarith [hsre]
  have hs1 : s ≠ 1 := by
    intro h
    have hr : s.re = 1 := by simpa using congrArg Complex.re h
    linarith [hsrlt]
  have hg : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [Complex.div_re]
    norm_num
    linarith [hsre]
  have he : Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  unfold nativeXiCompletionFactor
  change (1 / 2 : ℂ) * s * (s - 1) *
    Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) * Complex.Gamma (s / 2) ≠ 0
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact hs0
      · exact sub_ne_zero.mpr hs1
    · exact he
  · exact hg

/-- In the genuine critical strip, the continued native characteristic has exactly the zeros
of Mathlib's zeta.  The archimedean completion factor is nonzero there. -/
theorem completedNativeCharacteristicContinuation_zero_iff_zeta
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeCharacteristicContinuation z = 0 ↔
      riemannZeta (operatorHeightParameter z) = 0 := by
  rw [completedNativeCharacteristicContinuation_eq_native hs,
    completedNativeOperatorCharacteristic_eq_completedRiemannZeta hs]
  simp [sigmaNativeCompletionFactor_ne_zero_of_strip hs]

lemma sigmaNativeCompletionFactor_analyticAt_of_strip {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    AnalyticAt ℂ nativeXiCompletionFactor z := by
  have hsHalf : 0 < (operatorHeightParameter z / 2).re := by
    rw [Complex.div_re]
    norm_num
    exact hs.1
  have hGamma : AnalyticAt ℂ Complex.Gamma (operatorHeightParameter z / 2) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hOpen : IsOpen {w : ℂ | 0 < w.re} := isOpen_Ioi.preimage continuous_re
    filter_upwards [hOpen.eventually_mem hsHalf] with w hw
    exact Complex.differentiableAt_Gamma w (by
      intro n hneg
      have hre : w.re = -(n : ℝ) := by
        simpa using congrArg Complex.re hneg
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  have hparamHalf : AnalyticAt ℂ (fun w : ℂ => operatorHeightParameter w / 2) z := by
    change AnalyticAt ℂ
      (fun w : ℂ => ((1 / 2 : ℂ) + Complex.I * w) / 2) z
    fun_prop
  have hgammaComp : AnalyticAt ℂ
      (fun w : ℂ => Complex.Gamma (operatorHeightParameter w / 2)) z :=
    AnalyticAt.comp (g := Complex.Gamma)
      (f := fun w : ℂ => operatorHeightParameter w / 2) (x := z) hGamma hparamHalf
  have hpoly : AnalyticAt ℂ
      (fun w : ℂ => (1 / 2 : ℂ) * operatorHeightParameter w *
        (operatorHeightParameter w - 1)) z := by
    exact (analyticAt_const.mul (operatorHeightParameter_analyticAt z)).mul
      ((operatorHeightParameter_analyticAt z).sub analyticAt_const)
  have hexp : AnalyticAt ℂ
      (fun w : ℂ => Complex.exp (-(operatorHeightParameter w / 2) *
        (Real.log Real.pi : ℂ))) z := by fun_prop
  change AnalyticAt ℂ
    (fun w : ℂ => (1 / 2 : ℂ) * operatorHeightParameter w *
      (operatorHeightParameter w - 1) *
        Complex.exp (-(operatorHeightParameter w / 2) * (Real.log Real.pi : ℂ)) *
          Complex.Gamma (operatorHeightParameter w / 2)) z
  exact (hpoly.mul hexp).mul hgammaComp

/-- In the strip, the analytic order of the entire continuation is exactly the order of ζ at
the corresponding spectral parameter. The gamma and elementary completion factor is analytic
and nonzero there, and the height change has nonzero derivative. -/
theorem completedNativeCharacteristicContinuation_order_eq_zeta {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    analyticOrderAt completedNativeCharacteristicContinuation z =
      analyticOrderAt riemannZeta (operatorHeightParameter z) := by
  have hstrip : ∀ᶠ w : ℂ in 𝓝 z,
      operatorHeightParameter w ∈ genuineCriticalStrip := by
    have hopen : IsOpen genuineCriticalStrip := by
      rw [genuineCriticalStrip]
      change IsOpen ((fun s : ℂ => s.re) ⁻¹' Set.Ioo (0 : ℝ) 1)
      exact isOpen_Ioo.preimage continuous_re
    have hparam : ContinuousAt operatorHeightParameter z :=
      operatorHeightParameter_continuousAt z
    exact hparam.eventually (hopen.mem_nhds hs)
  have hidentity : completedNativeCharacteristicContinuation =ᶠ[𝓝 z]
      (fun w : ℂ => nativeXiCompletionFactor w *
        riemannZeta (operatorHeightParameter w)) := by
    filter_upwards [hstrip] with w hw
    rw [completedNativeCharacteristicContinuation_eq_native hw,
      completedNativeOperatorCharacteristic_eq_completedRiemannZeta hw]
  have hfactor : AnalyticAt ℂ nativeXiCompletionFactor z :=
    sigmaNativeCompletionFactor_analyticAt_of_strip hs
  have hfactorOrder : analyticOrderAt nativeXiCompletionFactor z = 0 :=
    hfactor.analyticOrderAt_eq_zero.mpr
      (sigmaNativeCompletionFactor_ne_zero_of_strip hs)
  have hparam : AnalyticAt ℂ operatorHeightParameter z :=
    operatorHeightParameter_analyticAt z
  have hzeta : AnalyticAt ℂ riemannZeta (operatorHeightParameter z) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hne : operatorHeightParameter z ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [hs.2]
    filter_upwards [isOpen_ne.eventually_mem hne] with w hw
    exact differentiableAt_riemannZeta hw
  have hzetaComp : AnalyticAt ℂ
      (fun w : ℂ => riemannZeta (operatorHeightParameter w)) z := hzeta.comp hparam
  have hcompOrder :
      analyticOrderAt (riemannZeta ∘ operatorHeightParameter) z =
        analyticOrderAt riemannZeta (operatorHeightParameter z) := by
    apply analyticOrderAt_comp_of_deriv_ne_zero hparam
    have hderiv : deriv operatorHeightParameter z = Complex.I := by
      change deriv (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) z = Complex.I
      simp
    rw [hderiv]
    exact Complex.I_ne_zero
  calc
    analyticOrderAt completedNativeCharacteristicContinuation z =
        analyticOrderAt (fun w : ℂ => nativeXiCompletionFactor w *
          riemannZeta (operatorHeightParameter w)) z :=
      analyticOrderAt_congr hidentity
    _ = analyticOrderAt nativeXiCompletionFactor z +
        analyticOrderAt (riemannZeta ∘ operatorHeightParameter) z :=
      analyticOrderAt_mul hfactor hzetaComp
    _ = analyticOrderAt riemannZeta (operatorHeightParameter z) := by
      rw [hfactorOrder, hcompOrder]
      simp

/-- Any zero of the completed continuation whose height coordinate has absolute value at most
50 lies on the real height axis. Positive and negative ordinates use the height-50 certificate
and the functional equation symmetry; ordinate zero is excluded separately by the real-strip
Euler--Maclaurin estimate. -/
theorem sigmaContinuation_zero_im_eq_zero_of_height50
    (hRH : sigmaRHHeight50) {w : ℂ}
    (hzero : completedNativeCharacteristicContinuation w = 0)
    (hbound : |w.re| ≤ 50) : w.im = 0 := by
  have hs := completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip hzero
  have hζ := (completedNativeCharacteristicContinuation_zero_iff_zeta hs).mp hzero
  by_cases hpos : 0 < w.re
  · have hle : w.re ≤ 50 := (abs_le.mp hbound).2
    have hres := hRH (operatorHeightParameter w) hζ hs.1 hs.2
      (by rw [operatorHeightParameter_im]; exact hpos)
      (by rw [operatorHeightParameter_im]; exact hle)
    rw [operatorHeightParameter_re] at hres
    linarith [hres.1]
  · by_cases hneg : w.re < 0
    · have hzeroNeg : completedNativeCharacteristicContinuation (-w) = 0 := by
        rw [completedNativeCharacteristicContinuation_even]
        exact hzero
      have hsNeg :=
        completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip hzeroNeg
      have hζNeg :=
        (completedNativeCharacteristicContinuation_zero_iff_zeta hsNeg).mp hzeroNeg
      have hleNeg : -w.re ≤ 50 := by linarith [(abs_le.mp hbound).1]
      have hres := hRH (operatorHeightParameter (-w)) hζNeg hsNeg.1 hsNeg.2
        (by rw [operatorHeightParameter_im]; simp; exact hneg)
        (by rw [operatorHeightParameter_im]; simp; exact hleNeg)
      have hReNeg : (operatorHeightParameter (-w)).re = 1 / 2 + w.im := by
        rw [operatorHeightParameter_re]
        simp
      rw [hReNeg] at hres
      linarith [hres.1]
    · have hwre : w.re = 0 := by linarith
      have him : (operatorHeightParameter w).im = 0 := by
        rw [operatorHeightParameter_im, hwre]
      have hsreal : operatorHeightParameter w =
          ((operatorHeightParameter w).re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [him]
      have hζreal : riemannZeta ((operatorHeightParameter w).re : ℂ) = 0 := by
        rw [← hsreal]
        exact hζ
      exact False.elim
        ((riemannZeta_ne_zero_of_real_strip hs.1 hs.2) hζreal)

theorem sigmaContinuation_zero_re_ne_zero_of_height50 {w : ℂ}
    (hzero : completedNativeCharacteristicContinuation w = 0) : w.re ≠ 0 := by
  have hs := completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip hzero
  have hζ := (completedNativeCharacteristicContinuation_zero_iff_zeta hs).mp hzero
  intro hwre
  have him : (operatorHeightParameter w).im = 0 := by
    rw [operatorHeightParameter_im, hwre]
  have hsreal : operatorHeightParameter w =
      ((operatorHeightParameter w).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  have hζreal : riemannZeta ((operatorHeightParameter w).re : ℂ) = 0 := by
    rw [← hsreal]
    exact hζ
  exact (riemannZeta_ne_zero_of_real_strip hs.1 hs.2) hζreal

/-- The continuation inherits the external certificate's simple-zero result, including negative
ordinates by evenness. -/
theorem sigmaContinuation_zero_order_one_of_height50
    (hRH : sigmaRHHeight50) {w : ℂ}
    (hzero : completedNativeCharacteristicContinuation w = 0)
    (hbound : |w.re| ≤ 50) :
    analyticOrderAt completedNativeCharacteristicContinuation w = 1 := by
  have hne := sigmaContinuation_zero_re_ne_zero_of_height50 hzero
  by_cases hpos : 0 < w.re
  · have hs := completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip hzero
    have hζ := (completedNativeCharacteristicContinuation_zero_iff_zeta hs).mp hzero
    have hle : w.re ≤ 50 := (abs_le.mp hbound).2
    have hres := hRH (operatorHeightParameter w) hζ hs.1 hs.2
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
    have hleNeg : -w.re ≤ 50 := by linarith [(abs_le.mp hbound).1]
    have hres := hRH (operatorHeightParameter (-w)) hζNeg hsNeg.1 hsNeg.2
      (by rw [operatorHeightParameter_im]; simp; exact hneg)
      (by rw [operatorHeightParameter_im]; simp; exact hleNeg)
    have horderNeg : analyticOrderAt completedNativeCharacteristicContinuation (-w) = 1 := by
      rw [completedNativeCharacteristicContinuation_order_eq_zeta hsNeg]
      exact hres.2
    have hnegAnalytic : AnalyticAt ℂ (fun u : ℂ => -u) w := by fun_prop
    have hcompOrder :
        analyticOrderAt (completedNativeCharacteristicContinuation ∘
          (fun u : ℂ => -u)) w =
          analyticOrderAt completedNativeCharacteristicContinuation (-w) :=
      analyticOrderAt_comp_of_deriv_ne_zero hnegAnalytic (by simp)
    have heven : (completedNativeCharacteristicContinuation ∘
        (fun u : ℂ => -u)) =ᶠ[𝓝 w]
        completedNativeCharacteristicContinuation := by
      filter_upwards [] with u
      exact completedNativeCharacteristicContinuation_even u
    calc
      analyticOrderAt completedNativeCharacteristicContinuation w =
          analyticOrderAt (completedNativeCharacteristicContinuation ∘
            (fun u : ℂ => -u)) w := (analyticOrderAt_congr heven).symm
      _ = analyticOrderAt completedNativeCharacteristicContinuation (-w) := hcompOrder
      _ = 1 := horderNeg

lemma sigmaAbsReLeNorm (z : ℂ) : |z.re| ≤ ‖z‖ := by
  have hupper : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hlower : -z.re ≤ ‖z‖ := by
    have h := Complex.re_le_norm (-z)
    simpa using h
  exact abs_le.mpr ⟨by linarith, hupper⟩

lemma sigmaSqrt300_lt_fifty : Real.sqrt 300 < 50 := by
  have hsquare : (Real.sqrt 300) ^ 2 = 300 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 300]

lemma operatorHeightParameter_eq_sigmaLineZero_of_im_zero {w : ℂ}
    (him : w.im = 0) : operatorHeightParameter w = sigmaLineZero w.re := by
  apply Complex.ext
  · simp [operatorHeightParameter_re, sigmaLineZero, him]
  · simp [operatorHeightParameter_im, sigmaLineZero]

/-- Every real height of a completed zero below `sqrt 300` is the first certified height or its
negative. This is where RH with simplicity is supplemented by the distinct-zero count and all
nine higher boxes. -/
theorem sigmaContinuation_abs_height_eq_first
    {γ : ℝ} (hRH : sigmaRHHeight50) (hcount : sigmaZeroCount50)
    (hboxes : sigmaTenZeroBoxesWithFirst γ) {w : ℂ}
    (hzero : completedNativeCharacteristicContinuation w = 0)
    (hbound : |w.re| < Real.sqrt 300) : |w.re| = γ := by
  have hbound50 : |w.re| ≤ 50 :=
    (le_of_lt hbound).trans (le_of_lt sigmaSqrt300_lt_fifty)
  have him := sigmaContinuation_zero_im_eq_zero_of_height50 hRH hzero hbound50
  have hne := sigmaContinuation_zero_re_ne_zero_of_height50 hzero
  by_cases hpos : 0 < w.re
  · have hs := completedNativeCharacteristicContinuation_zero_mem_genuineCriticalStrip hzero
    have hζ := (completedNativeCharacteristicContinuation_zero_iff_zeta hs).mp hzero
    have hline : riemannZeta (sigmaLineZero w.re) = 0 := by
      rw [← operatorHeightParameter_eq_sigmaLineZero_of_im_zero him]
      exact hζ
    have hsmall : w.re < Real.sqrt 300 := by simpa [abs_of_pos hpos] using hbound
    have heq := sigmaLineZero_small_eq_first γ hcount hboxes hpos hsmall hline
    rw [abs_of_pos hpos]
    exact heq
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
    have hsmall : -w.re < Real.sqrt 300 := by
      simpa [abs_of_neg hneg] using hbound
    have heq := sigmaLineZero_small_eq_first γ hcount hboxes (by linarith) hsmall hline
    rw [abs_of_neg hneg]
    simpa using heq

/-- Inside the target disk, the source product has exactly the four signed conjugate roots of its
first displaced height. Zeta zeros at ordinate zero are already excluded by
`sigmaContinuation_zero_im_eq_zero_of_height50`. -/
theorem sigmaDisplacedProductContinuation_zero_iff_root
    {γ : ℝ} (hRH : sigmaRHHeight50) (hcount : sigmaZeroCount50)
    (hboxes : sigmaTenZeroBoxesWithFirst γ)
    {t : ℂ} (ht : ‖t‖ < Real.sqrt 300) :
    completedNativeDisplacedProductContinuation (1 / 5) t = 0 ↔
      sigmaDisplacedFirstPoleRoot
        ((γ : ℂ) + Complex.I * ((1 / 5 : ℝ) : ℂ)) t := by
  let τ : ℂ := (γ : ℂ) + Complex.I * ((1 / 5 : ℝ) : ℂ)
  change completedNativeDisplacedProductContinuation (1 / 5) t = 0 ↔
    sigmaDisplacedFirstPoleRoot τ t
  constructor
  · intro hzero
    let wm : ℂ := t - Complex.I * ((1 / 5 : ℝ) : ℂ)
    let wp : ℂ := t + Complex.I * ((1 / 5 : ℝ) : ℂ)
    have hprod : completedNativeCharacteristicContinuation wm *
        completedNativeCharacteristicContinuation wp = 0 := by
      simpa [wm, wp, completedNativeDisplacedProductContinuation] using hzero
    have htBound50 : ‖t‖ ≤ 50 :=
      (le_of_lt ht).trans (le_of_lt sigmaSqrt300_lt_fifty)
    have hwmRe : wm.re = t.re := by simp [wm]
    have hwpRe : wp.re = t.re := by simp [wp]
    have hwmBound : |wm.re| ≤ ‖t‖ := by rw [hwmRe]; exact sigmaAbsReLeNorm t
    have hwpBound : |wp.re| ≤ ‖t‖ := by rw [hwpRe]; exact sigmaAbsReLeNorm t
    have hwmBound50 : |wm.re| ≤ 50 := hwmBound.trans htBound50
    have hwpBound50 : |wp.re| ≤ 50 := hwpBound.trans htBound50
    rcases mul_eq_zero.mp hprod with hwmzero | hwpzero
    · have hwmIm := sigmaContinuation_zero_im_eq_zero_of_height50 hRH hwmzero hwmBound50
      have hheight := sigmaContinuation_abs_height_eq_first hRH hcount hboxes hwmzero
        (hwmBound.trans_lt ht)
      have habsT : |t.re| = γ := by rw [← hwmRe]; exact hheight
      have htIm : t.im = 1 / 5 := by
        have heq : wm.im = t.im - 1 / 5 := by simp [wm]
        rw [heq] at hwmIm
        linarith
      have hsign : t.re = γ ∨ t.re = -γ := by
        rcases le_total 0 t.re with hnonneg | hnonpos
        · left
          rw [abs_of_nonneg hnonneg] at habsT
          exact habsT
        · right
          rw [abs_of_nonpos hnonpos] at habsT
          linarith
      rcases hsign with hre | hre
      · left
        apply Complex.ext
        · simpa [τ] using hre
        · simp [τ, htIm]
      · right
        right
        right
        apply Complex.ext
        · simp [τ, hre]
        · simp [τ, htIm]
    · have hwpIm := sigmaContinuation_zero_im_eq_zero_of_height50 hRH hwpzero hwpBound50
      have hheight := sigmaContinuation_abs_height_eq_first hRH hcount hboxes hwpzero
        (hwpBound.trans_lt ht)
      have habsT : |t.re| = γ := by rw [← hwpRe]; exact hheight
      have htIm : t.im = -(1 / 5 : ℝ) := by
        have heq : wp.im = t.im + 1 / 5 := by simp [wp]
        rw [heq] at hwpIm
        linarith
      have hsign : t.re = γ ∨ t.re = -γ := by
        rcases le_total 0 t.re with hnonneg | hnonpos
        · left
          rw [abs_of_nonneg hnonneg] at habsT
          exact habsT
        · right
          rw [abs_of_nonpos hnonpos] at habsT
          linarith
      rcases hsign with hre | hre
      · right
        right
        left
        apply Complex.ext
        · simp [τ, hre]
        · simp [τ, htIm]
      · right
        left
        apply Complex.ext
        · simp [τ, hre]
        · simp [τ, htIm]

  · intro hroot
    obtain ⟨ts, hts0, -, htsBoxes⟩ := hboxes
    have hγzero : riemannZeta (sigmaLineZero γ) = 0 := by
      have h := (htsBoxes 0).2
      simpa [hts0, sigmaLineZero] using h
    have hsγ : operatorHeightParameter (γ : ℂ) ∈ genuineCriticalStrip := by
      norm_num [genuineCriticalStrip, CarrySelfAdjointOperator.operatorHeightParameter]
    have hζγ : riemannZeta (operatorHeightParameter (γ : ℂ)) = 0 := by
      rw [operatorHeightParameter_eq_sigmaLineZero_of_im_zero (by simp)]
      exact hγzero
    have hXiγ : completedNativeCharacteristicContinuation (γ : ℂ) = 0 :=
      (completedNativeCharacteristicContinuation_zero_iff_zeta hsγ).2 hζγ
    have hXiNeg : completedNativeCharacteristicContinuation (-(γ : ℂ)) = 0 := by
      rw [completedNativeCharacteristicContinuation_even]
      exact hXiγ
    have hτminus : τ - Complex.I * ((1 / 5 : ℝ) : ℂ) = (γ : ℂ) := by
      dsimp [τ]
      ring
    have hnegτplus : -τ + Complex.I * ((1 / 5 : ℝ) : ℂ) = -(γ : ℂ) := by
      dsimp [τ]
      simp
    have hstarτplus : star τ + Complex.I * ((1 / 5 : ℝ) : ℂ) = (γ : ℂ) := by
      dsimp [τ]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hnegstarτminus : -star τ - Complex.I * ((1 / 5 : ℝ) : ℂ) = -(γ : ℂ) := by
      dsimp [τ]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rcases hroot with hτ | hnegτ | hstarτ | hnegstarτ
    · subst t
      unfold completedNativeDisplacedProductContinuation
      rw [hτminus, hXiγ]
      simp
    · subst t
      unfold completedNativeDisplacedProductContinuation
      rw [hnegτplus, hXiNeg]
      simp
    · subst t
      unfold completedNativeDisplacedProductContinuation
      rw [hstarτplus, hXiγ]
      simp
    · subst t
      unfold completedNativeDisplacedProductContinuation
      rw [hnegstarτminus, hXiNeg]
      simp

/-- Each of the four isolated roots of the displaced product is simple. The two translated
characteristics cannot vanish together: the finite-height RH certificate puts each zero on the
real height axis, while their imaginary parts differ by `2/5`. -/
theorem sigmaDisplacedProduct_order_one_of_root
    {γ : ℝ} (hRH : sigmaRHHeight50) (hcount : sigmaZeroCount50)
    (hboxes : sigmaTenZeroBoxesWithFirst γ)
    {t : ℂ} (ht : ‖t‖ < Real.sqrt 300)
    (hroot : sigmaDisplacedFirstPoleRoot
      ((γ : ℂ) + Complex.I * ((1 / 5 : ℝ) : ℂ)) t) :
    analyticOrderAt (completedNativeDisplacedProductContinuation (1 / 5)) t = 1 := by
  let d : ℝ := 1 / 5
  let fminus : ℂ → ℂ := fun z =>
    completedNativeCharacteristicContinuation (z - Complex.I * (d : ℂ))
  let fplus : ℂ → ℂ := fun z =>
    completedNativeCharacteristicContinuation (z + Complex.I * (d : ℂ))
  have hd : 0 < d := by norm_num [d]
  have hprodZero : completedNativeDisplacedProductContinuation (1 / 5) t = 0 := by
    exact (sigmaDisplacedProductContinuation_zero_iff_root hRH hcount hboxes ht).2 hroot
  have hreMinus : (t - Complex.I * (d : ℂ)).re = t.re := by simp
  have hrePlus : (t + Complex.I * (d : ℂ)).re = t.re := by simp
  have hbound : |t.re| ≤ 50 := by
    have hnorm : |t.re| ≤ ‖t‖ := sigmaAbsReLeNorm t
    exact hnorm.trans (le_of_lt (lt_trans ht sigmaSqrt300_lt_fifty))
  have hminusBound : |(t - Complex.I * (d : ℂ)).re| ≤ 50 := by
    rw [hreMinus]
    exact hbound
  have hplusBound : |(t + Complex.I * (d : ℂ)).re| ≤ 50 := by
    rw [hrePlus]
    exact hbound
  have hnotboth : ¬ (fminus t = 0 ∧ fplus t = 0) := by
    rintro ⟨hm, hp⟩
    have himMinus := sigmaContinuation_zero_im_eq_zero_of_height50 hRH hm hminusBound
    have himPlus := sigmaContinuation_zero_im_eq_zero_of_height50 hRH hp hplusBound
    have heqMinus : (t - Complex.I * (d : ℂ)).im = t.im - d := by simp [d]
    have heqPlus : (t + Complex.I * (d : ℂ)).im = t.im + d := by simp [d]
    rw [heqMinus] at himMinus
    rw [heqPlus] at himPlus
    linarith
  have hminusAnalytic : AnalyticAt ℂ fminus t := by
    dsimp [fminus]
    exact (completedNativeCharacteristicContinuation_analyticAt _).comp
      (analyticAt_id.sub analyticAt_const)
  have hplusAnalytic : AnalyticAt ℂ fplus t := by
    dsimp [fplus]
    exact (completedNativeCharacteristicContinuation_analyticAt _).comp
      (analyticAt_id.add analyticAt_const)
  have hminusOrderTransport :
      analyticOrderAt fminus t =
        analyticOrderAt completedNativeCharacteristicContinuation
          (t - Complex.I * (d : ℂ)) := by
    have hparam : AnalyticAt ℂ (fun z : ℂ => z - Complex.I * (d : ℂ)) t := by
      fun_prop
    change analyticOrderAt
      (completedNativeCharacteristicContinuation ∘
        (fun z : ℂ => z - Complex.I * (d : ℂ))) t = _
    exact analyticOrderAt_comp_of_deriv_ne_zero
      hparam (by simp)
  have hplusOrderTransport :
      analyticOrderAt fplus t =
        analyticOrderAt completedNativeCharacteristicContinuation
          (t + Complex.I * (d : ℂ)) := by
    have hparam : AnalyticAt ℂ (fun z : ℂ => z + Complex.I * (d : ℂ)) t := by
      fun_prop
    change analyticOrderAt
      (completedNativeCharacteristicContinuation ∘
        (fun z : ℂ => z + Complex.I * (d : ℂ))) t = _
    exact analyticOrderAt_comp_of_deriv_ne_zero
      hparam (by simp)
  have hfactor : fminus t * fplus t = 0 := by
    simpa [fminus, fplus, completedNativeDisplacedProductContinuation, d] using hprodZero
  rcases mul_eq_zero.mp hfactor with hm | hp
  · have hpne : fplus t ≠ 0 := by
      intro h
      exact hnotboth ⟨hm, h⟩
    have hminusOrder : analyticOrderAt fminus t = 1 := by
      rw [hminusOrderTransport]
      exact sigmaContinuation_zero_order_one_of_height50 hRH hm hminusBound
    have hplusOrder : analyticOrderAt fplus t = 0 :=
      hplusAnalytic.analyticOrderAt_eq_zero.mpr hpne
    have hmulOrder := analyticOrderAt_mul hminusAnalytic hplusAnalytic
    change analyticOrderAt (fun z : ℂ => fminus z * fplus z) t = 1
    calc
      analyticOrderAt (fun z : ℂ => fminus z * fplus z) t =
          analyticOrderAt fminus t + analyticOrderAt fplus t := hmulOrder
      _ = 1 := by rw [hminusOrder, hplusOrder]; simp
  · have hmne : fminus t ≠ 0 := by
      intro h
      exact hnotboth ⟨h, hp⟩
    have hminusOrder : analyticOrderAt fminus t = 0 :=
      hminusAnalytic.analyticOrderAt_eq_zero.mpr hmne
    have hplusOrder : analyticOrderAt fplus t = 1 := by
      rw [hplusOrderTransport]
      exact sigmaContinuation_zero_order_one_of_height50 hRH hp hplusBound
    have hmulOrder := analyticOrderAt_mul hminusAnalytic hplusAnalytic
    change analyticOrderAt (fun z : ℂ => fminus z * fplus z) t = 1
    calc
      analyticOrderAt (fun z : ℂ => fminus z * fplus z) t =
          analyticOrderAt fminus t + analyticOrderAt fplus t := hmulOrder
      _ = 1 := by rw [hminusOrder, hplusOrder]; simp

/-- The first zero bracket, the nine disjoint height boxes, RH, and the exact zero count produce
the original source isolation structure. Its zero-set and order fields are proved here rather than
assumed. -/
theorem exists_firstSigmaDisplacedProductIsolation_from_height50
    (hRH : sigmaRHHeight50) (hcount : sigmaZeroCount50)
    (hfirst : sigmaFirstZeroBracket) (hnine : sigmaNineZeroBoxes) :
    ∃ γ : ℝ, γ ∈ Set.Ioo (1413 / 100 : ℝ) (1414 / 100) ∧
      SigmaDisplacedProductIsolation (1 / 5) γ (Real.sqrt 300) 1 := by
  obtain ⟨γ, hγbox, hγzero⟩ := hfirst
  have hγpos : 0 < γ := by
    exact lt_trans (by norm_num : (0 : ℝ) < 1413 / 100) hγbox.1
  have hγzero' : riemannZeta (sigmaLineZero γ) = 0 := by
    simpa [sigmaLineZero] using hγzero
  have hboxes := sigmaTenZeroBoxesWithFirst_of_first_and_nine
    γ hγbox hγzero' hnine
  let τ : ℂ := (γ : ℂ) + Complex.I * ((1 / 5 : ℝ) : ℂ)
  have hnormsq : ‖τ‖ ^ 2 = γ ^ 2 + (1 / 5 : ℝ) ^ 2 := by
    dsimp [τ]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hγsq : γ ^ 2 < (1414 / 100 : ℝ) ^ 2 := by
    have hfactor : 0 < (1414 / 100 - γ) * (1414 / 100 + γ) :=
      mul_pos (sub_pos.mpr hγbox.2) (by linarith [hγpos])
    nlinarith
  have hnormsqlt : ‖τ‖ ^ 2 < 300 := by
    rw [hnormsq]
    nlinarith [hγsq]
  have hrootSq : (Real.sqrt 300) ^ 2 = 300 := Real.sq_sqrt (by norm_num)
  have hpair : ‖τ‖ < Real.sqrt 300 := by
    have hnormNonneg := norm_nonneg τ
    have hsqrtNonneg := Real.sqrt_nonneg 300
    nlinarith
  refine ⟨γ, hγbox, ?_⟩
  refine ⟨Real.sqrt_pos.mpr (by norm_num), by norm_num, hγpos,
    by norm_num, by norm_num, ?_, ?_, ?_⟩
  · simpa [τ] using hpair
  · intro z hz
    exact sigmaDisplacedProductContinuation_zero_iff_root hRH hcount hboxes hz
  · intro z hz hroot
    exact sigmaDisplacedProduct_order_one_of_root hRH hcount hboxes hz hroot

/-- The existing Padé theorem's complete recovery package, including convergence to both complex
heights and eventual roots of the original finite sigma pencil. -/
abbrev SigmaPadeRootRecovery (d γ : ℝ) (m : ℕ) : Prop :=
  ∃ C η : ℝ, 0 < C ∧ 0 < η ∧
    η < ‖((γ : ℂ) + Complex.I * ((d : ℝ) : ℂ)) ^ (-2 : ℤ)‖ ∧
    (∀ n, (CarrySigmaSource.completedSigmaLogJet d n : ℂ) =
      (CarrySigmaPade.twoPoleMoment (m : ℝ)
        (((γ : ℂ) + Complex.I * ((d : ℝ) : ℂ)) ^ (-2 : ℤ)) n : ℂ) +
        (sigmaZeroPairRemainderMoment d (m : ℝ)
          (((γ : ℂ) + Complex.I * ((d : ℝ) : ℂ)) ^ (-2 : ℤ)) n : ℂ)) ∧
    (∀ n, |sigmaZeroPairRemainderMoment d (m : ℝ)
      (((γ : ℂ) + Complex.I * ((d : ℝ) : ℂ)) ^ (-2 : ℤ)) n| ≤ C * η ^ n) ∧
    Tendsto (fun k => CarrySigmaPade.sigmaPadeQuadraticRootLower (-1)
      (-CarrySigmaPade.sigmaPadeAlpha d k) (-CarrySigmaPade.sigmaPadeBeta d k)) atTop
        (𝓝 (((γ : ℂ) + Complex.I * ((d : ℝ) : ℂ)) ^ (-2 : ℤ))) ∧
    Tendsto (fun k => star (CarrySigmaPade.sigmaPadeQuadraticRootLower (-1)
      (-CarrySigmaPade.sigmaPadeAlpha d k) (-CarrySigmaPade.sigmaPadeBeta d k))) atTop
        (𝓝 (star (((γ : ℂ) + Complex.I * ((d : ℝ) : ℂ)) ^ (-2 : ℤ)))) ∧
    Tendsto (fun k => sigmaPadeRecoveredHeight d k) atTop
      (𝓝 ((γ : ℂ) + Complex.I * ((d : ℝ) : ℂ))) ∧
    Tendsto (fun k => star (sigmaPadeRecoveredHeight d k)) atTop
      (𝓝 ((γ : ℂ) - Complex.I * ((d : ℝ) : ℂ))) ∧
    ∀ᶠ k : ℕ in atTop,
      CarrySigmaPade.sigmaPencilCharacteristicComplex d k
        (CarrySigmaPade.sigmaPadeQuadraticRootLower (-1) (-CarrySigmaPade.sigmaPadeAlpha d k)
          (-CarrySigmaPade.sigmaPadeBeta d k)) = 0 ∧
      CarrySigmaPade.sigmaPencilCharacteristicComplex d k
        (star (CarrySigmaPade.sigmaPadeQuadraticRootLower (-1) (-CarrySigmaPade.sigmaPadeAlpha d k)
          (-CarrySigmaPade.sigmaPadeBeta d k))) = 0 ∧
      (CarrySigmaPade.sigmaPadeQuadraticRootLower (-1) (-CarrySigmaPade.sigmaPadeAlpha d k)
        (-CarrySigmaPade.sigmaPadeBeta d k)).im ≠ 0 ∧
      (sigmaPadeRecoveredHeight d k) ^ 2 =
        (CarrySigmaPade.sigmaPadeQuadraticRootLower (-1) (-CarrySigmaPade.sigmaPadeAlpha d k)
          (-CarrySigmaPade.sigmaPadeBeta d k))⁻¹ ∧
      (star (sigmaPadeRecoveredHeight d k)) ^ 2 = star
        ((CarrySigmaPade.sigmaPadeQuadraticRootLower (-1) (-CarrySigmaPade.sigmaPadeAlpha d k)
          (-CarrySigmaPade.sigmaPadeBeta d k))⁻¹)

/-- Apply the existing Padé recovery theorem to any proved isolation certificate. -/
theorem sigmaPadeRootRecovery_of_isolation
    (d γ r : ℝ) (m : ℕ)
    (hisolation : SigmaDisplacedProductIsolation d γ r m) :
    SigmaPadeRootRecovery d γ m :=
  completedNative_sigmaRemainder_pade_root_of_isolation d γ r m hisolation

/-- End-to-end conditional height-50 conclusion: the locally proved isolation certificate feeds
the original Padé theorem and yields both recovered complex heights and eventual sigma-pencil
roots. -/
theorem exists_firstSigmaHeight50PadeRecovery
    (hRH : sigmaRHHeight50) (hcount : sigmaZeroCount50)
    (hfirst : sigmaFirstZeroBracket) (hnine : sigmaNineZeroBoxes) :
    ∃ γ : ℝ, γ ∈ Set.Ioo (1413 / 100 : ℝ) (1414 / 100) ∧
      SigmaPadeRootRecovery (1 / 5) γ 1 := by
  obtain ⟨γ, hγbox, hisolation⟩ :=
    exists_firstSigmaDisplacedProductIsolation_from_height50 hRH hcount hfirst hnine
  exact ⟨γ, hγbox, sigmaPadeRootRecovery_of_isolation
    (1 / 5) γ (Real.sqrt 300) 1 hisolation⟩

/-! ## Axiom audit for the finite-height bridge -/

#print axioms CarrySigmaObstruction.sigmaContinuation_zero_im_eq_zero_of_height50
#print axioms CarrySigmaObstruction.sigmaDisplacedProductContinuation_zero_iff_root
#print axioms CarrySigmaObstruction.sigmaDisplacedProduct_order_one_of_root
#print axioms CarrySigmaObstruction.exists_firstSigmaDisplacedProductIsolation_from_height50
#print axioms CarrySigmaObstruction.sigmaPadeRootRecovery_of_isolation
#print axioms CarrySigmaObstruction.exists_firstSigmaHeight50PadeRecovery
end
end CarrySigmaObstruction
