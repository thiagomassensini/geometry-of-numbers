import C3JointSource384

/-!
Remove the independent quadratic TT error assumption, using the actual
two original source legs and a finite directionalBudget. No positive
Green closure is postulated. The budget remains source dependent and
must be bounded by certified jet enclosures for a finite sign proof.
-/
namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

def signedQuadraticTailBudget (alpha betaA : ℝ)
    (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (T : ℕ → ℂ) : ℝ :=
  |alpha| * directionalBudget T T bB rB zB zB +
  |betaA| * directionalBudget T T bP rP zP zP

theorem signedQuadraticTailBudget_nonneg
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (T : ℕ → ℂ) :
    0 ≤ signedQuadraticTailBudget alpha betaA bB bP rB rP zB zP T := by
  unfold signedQuadraticTailBudget
  exact add_nonneg
    (mul_nonneg (abs_nonneg _) (directionalBudget_nonneg T T bB rB zB zB))
    (mul_nonneg (abs_nonneg _) (directionalBudget_nonneg T T bP rP zP zP))

theorem signed_quadratic_source_bound
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (T : ℕ → ℂ) :
    ‖signedSourcePair alpha betaA bB bP rB rP zB zP T T‖ ≤
      signedQuadraticTailBudget alpha betaA bB bP rB rP zB zP T := by
  have hB := mixed_direction_bound T T bB rB zB zB
  have hP := mixed_direction_bound T T bP rP zP zP
  unfold signedSourcePair coefficientPair signedQuadraticTailBudget
  have htriangle := norm_sub_le
    ((alpha:ℂ) * complexPair
      (coefficientBlock (mixedSourceKernel T T bB) rB)
      (fun i => (zB i:ℂ)) (fun j => (zB j:ℂ)))
    ((betaA:ℂ) * complexPair
      (coefficientBlock (mixedSourceKernel T T bP) rP)
      (fun i => (zP i:ℂ)) (fun j => (zP j:ℂ)))
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at htriangle ⊢
  have h1 := mul_le_mul_of_nonneg_left hB (abs_nonneg alpha)
  have h2 := mul_le_mul_of_nonneg_left hP (abs_nonneg betaA)
  linarith

/-- Final 384-source correlated budget, with BOTH HT+TH and TT proved
from the same genuine completed TFVD tail (no hCoeff or hQuad premise). -/
theorem original_c3_joint_source_budget384_with_TT
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
        signedQuadraticTailBudget alpha betaA bB bP rB rP zB zP
          originalC3Tail384Nat := by
  exact original_c3_joint_source_budget384 alpha betaA bB bP rB rP
    zB zP hNB hNP
    (signedQuadraticTailBudget alpha betaA bB bP rB rP zB zP
       originalC3Tail384Nat)
    (signed_quadratic_source_bound alpha betaA bB bP rB rP zB zP
       originalC3Tail384Nat)

end
end CarrySourceBezout
