import C3JointQuadraticBudget

/-!
All-order coefficientwise *rational* upper envelope on the TT budget.
Uses the ORIGINAL accelerated C3 completion tail at M=384. This is a
conservative bound; the sharper 320 dps Arb intervals are still external.
-/
namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000

def responseBox (eps : ℕ → ℝ) (b : Bool) (k : ℕ) : ℝ :=
  if b then (k+1)*eps (k+1) else k*eps k

theorem responseBox_nonneg (eps : ℕ → ℝ)
    (hE : ∀ k, 0 ≤ eps k) (b : Bool) (k : ℕ) :
    0 ≤ responseBox eps b k := by
  cases b with
  | false =>
    simpa [responseBox] using
      (mul_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity) (hE k))
  | true =>
    simpa [responseBox] using
      (mul_nonneg (show (0:ℝ) ≤ ((k+1:ℕ):ℝ) by positivity) (hE (k+1)))

theorem responseCoefficient_box (c : ℕ → ℂ) (eps : ℕ → ℝ)
    (hc : ∀ k, ‖c k‖ ≤ eps k) (b : Bool) (k : ℕ) :
    ‖responseCoefficient c b k‖ ≤ responseBox eps b k := by
  cases b with
  | true =>
    rw [response_odd_explicit]
    simp only [norm_neg, norm_mul, Complex.norm_natCast]
    have h := mul_le_mul_of_nonneg_left (hc (k+1))
      (show 0 ≤ ((k+1:ℕ):ℝ) by positivity)
    simpa [responseBox] using h
  | false =>
    cases k with
    | zero =>
      simp [response_even_zero, responseBox]
    | succ k =>
      rw [response_even_succ]
      simp only [norm_neg, norm_mul, Complex.norm_natCast]
      have h := mul_le_mul_of_nonneg_left (hc (k+1))
        (show 0 ≤ ((k+1:ℕ):ℝ) by positivity)
      simpa [responseBox] using h

def coefficientBoxBudget (eps : ℕ → ℝ) (b : Bool) (i j : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (j+1),
       eps (j-k) * responseBox eps b (i+k+1)) +
   ∑ k ∈ Finset.range (j+1),
       responseBox eps b (j-k) * eps (i+k+1)

theorem coefficientBudget_le_box
    (c : ℕ → ℂ) (eps : ℕ → ℝ)
    (hE : ∀ k, 0 ≤ eps k)
    (hc : ∀ k, ‖c k‖ ≤ eps k)
    (b : Bool) (i j : ℕ) :
    coefficientBudget c c b i j ≤ coefficientBoxBudget eps b i j := by
  unfold coefficientBudget coefficientBoxBudget
  apply add_le_add
  · apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul (hc (j-k))
      (responseCoefficient_box c eps hc b (i+k+1))
      (norm_nonneg _)
      (hE (j-k))
  · apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul (responseCoefficient_box c eps hc b (j-k))
      (hc (i+k+1))
      (norm_nonneg _)
      (responseBox_nonneg eps hE b (j-k))

def directionalBoxBudget (eps : ℕ → ℝ) (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) : ℝ :=
  ∑ i : Fin r, ∑ j : Fin r,
    |x i| * coefficientBoxBudget eps b i.val j.val * |y j|

theorem directionalBudget_le_box
    (c : ℕ → ℂ) (eps : ℕ → ℝ)
    (hE : ∀ k, 0 ≤ eps k)
    (hc : ∀ k, ‖c k‖ ≤ eps k)
    (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    directionalBudget c c b r x y ≤
      directionalBoxBudget eps b r x y := by
  unfold directionalBudget directionalBoxBudget
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have h0 := coefficientBudget_le_box c eps hE hc b i.val j.val
  have h1 := mul_le_mul_of_nonneg_left h0 (abs_nonneg (x i))
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg (y j))

def c3RationalBox384 (j : ℕ) : ℝ :=
  CarryC3Tail.completedC3TailJetEnvelope 384 j

theorem c3RationalBox384_nonneg (j : ℕ) :
    0 ≤ c3RationalBox384 j := by
  unfold c3RationalBox384 CarryC3Tail.completedC3TailJetEnvelope
  positivity

theorem c3_all_jets_coarse_bound (j : ℕ) :
    ‖originalC3Tail384Nat j‖ ≤ c3RationalBox384 j :=
  c3_regrouped_tail_any_bound 384 j (by norm_num)

def signedQuadraticRational384 (alpha betaA : ℝ)
    (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ) : ℝ :=
  |alpha| * directionalBoxBudget c3RationalBox384 bB rB zB zB +
  |betaA| * directionalBoxBudget c3RationalBox384 bP rP zP zP

theorem c3_signed_quadratic_rational_upper
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ) :
    signedQuadraticTailBudget alpha betaA bB bP rB rP zB zP
        originalC3Tail384Nat ≤
      signedQuadraticRational384 alpha betaA bB bP rB rP zB zP := by
  unfold signedQuadraticTailBudget signedQuadraticRational384
  have hB := directionalBudget_le_box originalC3Tail384Nat
    c3RationalBox384 c3RationalBox384_nonneg
    c3_all_jets_coarse_bound bB rB zB zB
  have hP := directionalBudget_le_box originalC3Tail384Nat
    c3RationalBox384 c3RationalBox384_nonneg
    c3_all_jets_coarse_bound bP rP zP zP
  have h1 := mul_le_mul_of_nonneg_left hB (abs_nonneg alpha)
  have h2 := mul_le_mul_of_nonneg_left hP (abs_nonneg betaA)
  exact add_le_add h1 h2

/-- All coefficients and both sides of the true completed source
possess Lean-proved, index-specific, finite rational C3/384 tail budgets.
This theorem has no input margin, no assumed hCoeff, no hQuad. -/
theorem original_c3_joint_source_budget384_rational
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (hNB : 2*rB < 23) (hNP : 2*rP < 23) :
    ‖signedSourcePair alpha betaA bB bP rB rP zB zP
        (fun j => (nativeC j : ℂ)) (fun j => (nativeC j : ℂ)) -
      signedSourcePair alpha betaA bB bP rB rP zB zP
        originalC3Head384Nat originalC3Head384Nat‖ ≤
      (∑ j : Fin 23,
        ‖signedImpulseCoefficient 23 alpha betaA bB bP rB rP zB zP
            originalC3Head384Nat j‖ * originalC3Box384 j) +
        signedQuadraticRational384 alpha betaA bB bP rB rP zB zP := by
  exact (original_c3_joint_source_budget384_with_TT
    alpha betaA bB bP rB rP zB zP hNB hNP).trans
      (add_le_add_right
        (c3_signed_quadratic_rational_upper alpha betaA bB bP rB rP zB zP)
        _)

end
end CarrySourceBezout
