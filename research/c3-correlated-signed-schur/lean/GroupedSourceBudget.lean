import SignedSourceTail

/-!
A genuine CORRELATED coefficient-level budget for the one source tail.
The exact coefficient expansion and certified tail-jet intervals are explicit
inputs: do not silently substitute floating-point deltas for interval bounds.
-/
namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

/-- After combining the two parity probes, take one absolute value
PER SHARED TAIL COEFFICIENT, not one per B/p matrix entry. -/
theorem joint_linear_coefficient_budget
    (N : ℕ) (ell t : Fin N → ℂ) (eps : Fin N → ℝ)
    (heps : ∀ j : Fin N, ‖t j‖ ≤ eps j) :
    ‖∑ j : Fin N, ell j*t j‖ ≤
      ∑ j : Fin N, ‖ell j‖*eps j := by
  calc
    ‖∑ j : Fin N, ell j*t j‖ ≤
        ∑ j : Fin N, ‖ell j*t j‖ := norm_sum_le _ _
    _ = ∑ j : Fin N, ‖ell j‖*‖t j‖ := by
        simp only [norm_mul]
    _ ≤ ∑ j : Fin N, ‖ell j‖*eps j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (heps j) (norm_nonneg _)

/-- Joint HT+TH grouping for the ORIGINAL signed source. The linear
coefficient expansion is an explicit proof obligation, not a hypothesis
about the sign of the completed source. -/
theorem signed_source_joint_interval_budget
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP N : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (H T : ℕ → ℂ)
    (ell : Fin N → ℂ) (eps : Fin N → ℝ) (quadBound : ℝ)
    (hCoeff :
      signedSourceLinear alpha betaA bB bP rB rP zB zP H T =
        ∑ j : Fin N, ell j*T j.val)
    (hEps : ∀ j : Fin N, ‖T j.val‖ ≤ eps j)
    (hQuad :
      ‖signedSourcePair alpha betaA bB bP rB rP zB zP T T‖ ≤ quadBound) :
    ‖signedSourcePair alpha betaA bB bP rB rP zB zP (H+T) (H+T) -
      signedSourcePair alpha betaA bB bP rB rP zB zP H H‖ ≤
        (∑ j : Fin N, ‖ell j‖*eps j) + quadBound := by
  have hLinear := joint_linear_coefficient_budget N ell
    (fun j => T j.val) eps hEps
  have he := signed_source_joint_error_bound alpha betaA bB bP rB rP zB zP H T
  rw [hCoeff] at he
  linarith

/-- Both genuine source parity probe weights are combined before bounding.
The old one-sided completion remains in the SAME common jet decomposition. -/
theorem signed_native_even_head_error (n : ℕ)
    (v : Fin (n+1) → ℝ) (alpha betaA : ℝ)
    (H T : ℕ → ℂ)
    (hsource : H+T = (fun k => (nativeC k : ℂ))) :
    |alpha*matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 1 (n+1)) v v -
      betaA*matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 0 (n+1)) v v -
      (signedSourcePair alpha betaA true false (n+1) (n+1)
        (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) H H).re| ≤
       ‖signedSourceLinear alpha betaA true false (n+1) (n+1)
          (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) H T‖ +
       ‖signedSourcePair alpha betaA true false (n+1) (n+1)
          (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) T T‖ := by
  have he := signed_source_joint_error_bound alpha betaA true false
    (n+1) (n+1) (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) H T
  rw [hsource] at he
  have ht := signed_source_native_even n v alpha betaA
  rw [← ht] at he
  have hre := Complex.abs_re_le_norm
    (((alpha*matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 1 (n+1)) v v -
       betaA*matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 0 (n+1)) v v : ℝ):ℂ) -
      signedSourcePair alpha betaA true false (n+1) (n+1)
        (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) H H)
  simpa only [Complex.sub_re, Complex.ofReal_re] using hre.trans he


/-- Same correlated and signed source tail bound in the ODD Schur sector,
whose B term belongs to the zero-padded even source chart. -/
theorem signed_native_odd_head_error (n : ℕ)
    (v : Fin (n+1) → ℝ) (alpha betaA : ℝ)
    (H T : ℕ → ℂ)
    (hsource : H+T = (fun k => (nativeC k : ℂ))) :
    |alpha*matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 2 (n+1)) v v -
      betaA*matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 1 (n+1)) v v -
      (signedSourcePair alpha betaA false true (n+2) (n+1)
        (mixedSourceLift (n+2) (Fin.cons 0 v)) (mixedSourceLift (n+1) v) H H).re| ≤
       ‖signedSourceLinear alpha betaA false true (n+2) (n+1)
          (mixedSourceLift (n+2) (Fin.cons 0 v)) (mixedSourceLift (n+1) v) H T‖ +
       ‖signedSourcePair alpha betaA false true (n+2) (n+1)
          (mixedSourceLift (n+2) (Fin.cons 0 v)) (mixedSourceLift (n+1) v) T T‖ := by
  have he := signed_source_joint_error_bound alpha betaA false true
    (n+2) (n+1) (mixedSourceLift (n+2) (Fin.cons 0 v))
    (mixedSourceLift (n+1) v) H T
  rw [hsource] at he
  have ht := signed_source_native_odd n v alpha betaA
  rw [← ht] at he
  have hre := Complex.abs_re_le_norm
    (((alpha*matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 2 (n+1)) v v -
       betaA*matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 1 (n+1)) v v : ℝ):ℂ) -
      signedSourcePair alpha betaA false true (n+2) (n+1)
        (mixedSourceLift (n+2) (Fin.cons 0 v)) (mixedSourceLift (n+1) v) H H)
  simpa only [Complex.sub_re, Complex.ofReal_re] using hre.trans he

end
end CarrySourceBezout
