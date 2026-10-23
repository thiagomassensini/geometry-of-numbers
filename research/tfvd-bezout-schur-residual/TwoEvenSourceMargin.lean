import Repartition
import SourceBlocks
import LiteralBudgetLimit

namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000

/-- Previously certified source reference points; not a replacement source. -/
def twoEvenReferenceReal (n : ℕ) : ℝ :=
  if n=0 then 497120778188314/1000000000000000 else
  if n=1 then -11485972157573/1000000000000000 else
  if n=2 then 123452018070/1000000000000000 else
    -832355481/1000000000000000

def twoEvenReference (n : ℕ) : ℂ := (twoEvenReferenceReal n : ℂ)
def twoMonic (t : ℝ) : Fin 2 → ℝ := ![t,1]

theorem two_reference_norm (i : Fin 4) : ‖twoEvenReference i.val‖ ≤ (1/2:ℝ) := by
  rw [twoEvenReference,Complex.norm_real,Real.norm_eq_abs]
  fin_cases i <;> norm_num [twoEvenReferenceReal]

theorem response_coefficient_small_bound (c : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ i : Fin 4, ‖c i.val‖ ≤ C) (n : ℕ) (hn : n<4) :
    ‖responseCoefficient c false n‖ ≤ 3*C := by
  cases n with
  | zero => simpa [responseCoefficient_even_zero] using (mul_nonneg (by norm_num : (0:ℝ)≤3) hC)
  | succ n =>
    rw [responseCoefficient_even_succ, norm_mul]
    simp only [norm_neg,Complex.norm_natCast]
    have hb := hc ⟨n+1,hn⟩
    have hle : ((n+1:ℕ):ℝ) ≤ 3 := by exact_mod_cast (show n+1≤3 by omega)
    exact mul_le_mul hle hb (norm_nonneg _) (by norm_num)

theorem two_coefficient_budget_bound (c d : ℕ → ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ∀ i : Fin 4, ‖c i.val‖ ≤ C) (hd : ∀ i : Fin 4, ‖d i.val‖ ≤ D)
    (i j : Fin 2) : coefficientBudget c d false i.val j.val ≤ 12*C*D := by
  have hterm₁ (k : ℕ) (hk : k ∈ Finset.range (j.val+1)) :
      ‖d (j.val-k)‖*‖responseCoefficient c false (i.val+k+1)‖ ≤ 3*C*D := by
    have hkn : k≤j.val := by simpa using hk
    have hleft := hd ⟨j.val-k,by omega⟩
    have hright := response_coefficient_small_bound c C hC hc (i.val+k+1) (by omega)
    exact (mul_le_mul hleft hright (norm_nonneg _) hD).trans_eq (by ring)
  have hterm₂ (k : ℕ) (hk : k ∈ Finset.range (j.val+1)) :
      ‖responseCoefficient c false (j.val-k)‖*‖d (i.val+k+1)‖ ≤ 3*C*D := by
    have hkn : k≤j.val := by simpa using hk
    have hleft := response_coefficient_small_bound c C hC hc (j.val-k) (by omega)
    have hright := hd ⟨i.val+k+1,by omega⟩
    exact mul_le_mul hleft hright (norm_nonneg _) (by positivity)
  have hs₁ := Finset.sum_le_sum (s:=Finset.range (j.val+1)) hterm₁
  have hs₂ := Finset.sum_le_sum (s:=Finset.range (j.val+1)) hterm₂
  have hle : ((j.val+1:ℕ):ℝ) ≤ 2 := by exact_mod_cast j.isLt
  have hprod : 0 ≤ 3*C*D := by positivity
  have hh : (∑ k ∈ Finset.range (j.val+1), (3*C*D)) ≤ 6*C*D := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right hle hprod).trans_eq (by ring)
  exact (add_le_add hs₁ hs₂).trans ((add_le_add hh hh).trans_eq (by ring))

theorem two_directional_budget_bound (c d : ℕ → ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ∀ i : Fin 4, ‖c i.val‖ ≤ C) (hd : ∀ i : Fin 4, ‖d i.val‖ ≤ D)
    (x y : Fin 2 → ℝ) (hx : ∀ i, |x i|≤1) (hy : ∀ i, |y i|≤1) :
    directionalBudget c d false 2 x y ≤ 48*C*D := by
  have hb (i j : Fin 2) :
      |x i| * coefficientBudget c d false i.val j.val * |y j| ≤ 12*C*D := by
    have hcoef := two_coefficient_budget_bound c d C D hC hD hc hd i j
    calc
      _ ≤ (12*C*D)*|y j| := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_right (hx i) (coefficientBudget_nonneg _ _ _ _ _)).trans
          (by simpa using hcoef)) (abs_nonneg _)
      _ ≤ (12*C*D)*1 := mul_le_mul_of_nonneg_left (hy j) (by positivity)
      _ = _ := by ring
  apply (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))).trans
  norm_num [Fin.sum_univ_two,directionalBudget]
  nlinarith

theorem coefficientPair_add_left (a b d : ℕ → ℂ) (s : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    coefficientPair (a+b) d s r x y = coefficientPair a d s r x y+coefficientPair b d s r x y := by
  unfold coefficientPair
  rw [mixedSourceKernel_add_left,coefficientBlock_add,complexPair_add]

theorem coefficientPair_add_right (c a b : ℕ → ℂ) (s : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    coefficientPair c (a+b) s r x y = coefficientPair c a s r x y+coefficientPair c b s r x y := by
  unfold coefficientPair
  rw [mixedSourceKernel_add_right,coefficientBlock_add,complexPair_add]

theorem coefficientPair_difference (c d : ℕ → ℂ) (s : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    coefficientPair c c s r x y-coefficientPair d d s r x y =
      coefficientPair (c-d) c s r x y+coefficientPair d (c-d) s r x y := by
  have hsum : d+(c-d)=c := by funext n; simp
  have hl := coefficientPair_add_left d (c-d) c s r x y
  have hr := coefficientPair_add_right d d (c-d) s r x y
  rw [hsum] at hl hr
  linear_combination hl+hr

theorem two_reference_monic_lower (t : ℝ) :
    (2/10^8:ℝ) < (coefficientPair twoEvenReference twoEvenReference false 2 (twoMonic t) (twoMonic t)).re := by
  have hmap := sourceKernel_map Complex.ofRealHom twoEvenReferenceReal false
  have hblock := congrArg (fun f : BiSeries ℂ => coefficientBlock f 2) hmap
  rw [coefficientBlock_map] at hblock
  change coefficientBlock (sourceKernel twoEvenReference false) 2 = _ at hblock
  have he : coefficientPair twoEvenReference twoEvenReference false 2 (twoMonic t) (twoMonic t) =
      (matrixPair (coefficientBlock (sourceKernel twoEvenReferenceReal false) 2) (twoMonic t) (twoMonic t) : ℂ) := by
    unfold coefficientPair
    change complexPair (coefficientBlock (sourceKernel twoEvenReference false) 2) _ _ = _
    rw [hblock,complexPair_real]
  rw [he,Complex.ofReal_re,source_even_two]
  norm_num [matrixPair,Matrix.mulVec,dotProduct,Fin.sum_univ_two,twoMonic,twoEvenReferenceReal]
  nlinarith [sq_nonneg ((2854957708610998856337600961:ℝ)/500000000000000000000000000000*t-
    3068528164593810089541699/25000000000000000000000000000)]

/-- A finite source property, independent of moments, Schur signs and whitening.
It holds for an interval of genuine monic directions, not a rounded vector. -/
theorem two_source_head_margin (H : ℕ → ℂ)
    (hH : ∀ i : Fin 4, ‖H i.val-twoEvenReference i.val‖ ≤ (2/10^12:ℝ))
    (t : ℝ) (ht : |t|≤1) :
    (1/10^8:ℝ) < (coefficientPair H H false 2 (twoMonic t) (twoMonic t)).re := by
  have hv (i : Fin 2) : |twoMonic t i|≤1 := by
    fin_cases i
    · simpa [twoMonic] using ht
    · simp [twoMonic]
  have hnorm (i : Fin 4) : ‖H i.val‖≤1 := by
    have hh := norm_le_norm_sub_add (H i.val) (twoEvenReference i.val)
    have hr := two_reference_norm i
    linarith [hH i]
  have href (i : Fin 4) : ‖twoEvenReference i.val‖≤1 := (two_reference_norm i).trans (by norm_num)
  have herr (i : Fin 4) : ‖(H-twoEvenReference) i.val‖≤(2/10^12:ℝ) := hH i
  have hb₁ := (mixed_direction_bound (H-twoEvenReference) H false 2 (twoMonic t) (twoMonic t)).trans
    (two_directional_budget_bound (H-twoEvenReference) H (2/10^12) 1 (by norm_num) (by norm_num) herr hnorm _ _ hv hv)
  have hb₂ := (mixed_direction_bound twoEvenReference (H-twoEvenReference) false 2 (twoMonic t) (twoMonic t)).trans
    (two_directional_budget_bound twoEvenReference (H-twoEvenReference) 1 (2/10^12) (by norm_num) (by norm_num) href herr _ _ hv hv)
  have hd := (norm_add_le _ _).trans (add_le_add hb₁ hb₂)
  change ‖coefficientPair (H-twoEvenReference) H false 2 (twoMonic t) (twoMonic t)+
    coefficientPair twoEvenReference (H-twoEvenReference) false 2 (twoMonic t) (twoMonic t)‖ ≤ _ at hd
  rw [← coefficientPair_difference] at hd
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hd)).1
  have hp := two_reference_monic_lower t
  simp only [Complex.sub_re] at hr
  norm_num at hr
  linarith

def splitErrorBudget (H T : ℕ → ℂ) (s : Bool) (r : ℕ) (x y : Fin r → ℝ) : ℝ :=
  directionalBudget H T s r x y+directionalBudget T H s r x y+directionalBudget T T s r x y

/-- All three ordered errors are retained in the same original split. -/
theorem split_error_bound (H T : ℕ → ℂ) (s : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    ‖coefficientPair (H+T) (H+T) s r x y-coefficientPair H H s r x y‖ ≤
      splitErrorBudget H T s r x y := by
  rw [coefficientPair_four_terms]
  rw [show coefficientPair H H s r x y+coefficientPair H T s r x y+
      coefficientPair T H s r x y+coefficientPair T T s r x y-coefficientPair H H s r x y =
    (coefficientPair H T s r x y+coefficientPair T H s r x y)+coefficientPair T T s r x y by ring]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_add_le _ _).trans (add_le_add
      (mixed_direction_bound H T s r x y) (mixed_direction_bound T H s r x y))
  · exact mixed_direction_bound T T s r x y

/-- Conservative rational upper bound on all three ordered error budgets. -/
theorem two_source_error_upper (H T : ℕ → ℂ)
    (hH : ∀ i : Fin 4, ‖H i.val‖≤1)
    (hT : ∀ i : Fin 4, ‖T i.val‖≤(1/10^15:ℝ))
    (t : ℝ) (ht : |t|≤1) :
    splitErrorBudget H T false 2 (twoMonic t) (twoMonic t)≤(1/10^13:ℝ) := by
  have hv (i : Fin 2) : |twoMonic t i|≤1 := by
    fin_cases i
    · simpa [twoMonic] using ht
    · simp [twoMonic]
  have h₁ := two_directional_budget_bound H T 1 (1/10^15) (by norm_num) (by norm_num) hH hT _ _ hv hv
  have h₂ := two_directional_budget_bound T H (1/10^15) 1 (by norm_num) (by norm_num) hT hH _ _ hv hv
  have h₃ := two_directional_budget_bound T T (1/10^15) (1/10^15) (by norm_num) (by norm_num) hT hT _ _ hv hv
  unfold splitErrorBudget
  norm_num at h₁ h₂ h₃
  linarith

theorem two_source_split_margin (H T : ℕ → ℂ)
    (hH : ∀ i : Fin 4, ‖H i.val-twoEvenReference i.val‖ ≤ (2/10^12:ℝ))
    (hT : ∀ i : Fin 4, ‖T i.val‖ ≤ (1/10^15:ℝ))
    (t : ℝ) (ht : |t|≤1) :
    splitErrorBudget H T false 2 (twoMonic t) (twoMonic t) <
      (coefficientPair H H false 2 (twoMonic t) (twoMonic t)).re := by
  have hv (i : Fin 2) : |twoMonic t i|≤1 := by
    fin_cases i
    · simpa [twoMonic] using ht
    · simp [twoMonic]
  have hnorm (i : Fin 4) : ‖H i.val‖≤1 := by
    have hh := norm_le_norm_sub_add (H i.val) (twoEvenReference i.val)
    have hr := two_reference_norm i
    linarith [hH i]
  have h₁ := two_directional_budget_bound H T 1 (1/10^15) (by norm_num) (by norm_num) hnorm hT _ _ hv hv
  have h₂ := two_directional_budget_bound T H (1/10^15) 1 (by norm_num) (by norm_num) hT hnorm _ _ hv hv
  have h₃ := two_directional_budget_bound T T (1/10^15) (1/10^15) (by norm_num) (by norm_num) hT hT _ _ hv hv
  have hmargin := two_source_head_margin H hH t ht
  unfold splitErrorBudget
  norm_num at h₁ h₂ h₃
  linarith

end
end CarrySourceBezout
