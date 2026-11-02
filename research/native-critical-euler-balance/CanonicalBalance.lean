import CriticalReduction

namespace CarryCriticalEuler
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem canonical_critical_relation (s d : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s d)) :
    sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s (d+1) *ᵥ
      canonicalCriticalVector s d = Fin.snoc 0
        (sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s d) := by
  have h := MomentosHankel.schurVector_mulVec
    (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s d)
    (sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s d)
    (canonicalCompletedNativeLogDerivativeMoment (2*d+s))
    (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s (d+1))
    (by intro i j; rfl) (by intro i; rfl)
    (by intro j; simp [sourceMomentMatrix,sourceMomentCoupling,Nat.add_comm])
    (by simp [sourceMomentMatrix,two_mul]) hA
  exact h

theorem canonical_weighted_reduction (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s (n+1))) :
    weightedForm canonicalCompletedNativeLogDerivativeMoment s (canonicalCriticalVector s (n+1)) =
      ((2*((n+1:ℕ):ℝ)+(s:ℝ)+1)*(4*((n+1:ℕ):ℝ)+2*(s:ℝ)+3))*
        sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment (s+1) (n+2)
          (canonicalCriticalVector s (n+1)) -
      (16*((n+1:ℕ):ℝ)+8*(s:ℝ)+6)*canonicalCriticalVector s (n+1) (Fin.last n).castSucc*
        sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s (n+1) +
      4*sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment (s+1) (n+1)
        (eulerResidual n (canonicalCriticalVector s (n+1))) := by
  rw [stationary_weighted_reduction _ s n _ _ (canonical_critical_relation s (n+1) hA),pair_self]

theorem canonical_curvature_eq_weighted (s d : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s d)) :
    iteratedDeriv 2 (fun x => sigmaSchur x s d) 0 =
      -2*weightedForm canonicalCompletedNativeLogDerivativeMoment s (canonicalCriticalVector s d) :=
  moving_schur_curvature_expanded s d hA

/-- The new control problem is a specific balance of the same unweighted
source forms, including a strictly lower-degree residual. -/
theorem canonical_curvature_balance (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s (n+1))) :
    iteratedDeriv 2 (fun x => sigmaSchur x s (n+1)) 0 = -2 *
      (((2*((n+1:ℕ):ℝ)+(s:ℝ)+1)*(4*((n+1:ℕ):ℝ)+2*(s:ℝ)+3))*
        sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment (s+1) (n+2)
          (canonicalCriticalVector s (n+1)) -
      (16*((n+1:ℕ):ℝ)+8*(s:ℝ)+6)*canonicalCriticalVector s (n+1) (Fin.last n).castSucc*
        sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s (n+1) +
      4*sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment (s+1) (n+1)
        (eulerResidual n (canonicalCriticalVector s (n+1)))) := by
  rw [canonical_curvature_eq_weighted s (n+1) hA,canonical_weighted_reduction s n hA]

/-- A sufficient comparison in the original unweighted source forms. The
strictly lower shifted residual is controlled by the old prefix only. -/
theorem canonical_curvature_negative_of_source_budget (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s (n+1)))
    (hold : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment (s+1) (n+1)).PosSemidef)
    (hbudget :
      (16*((n+1:ℕ):ℝ)+8*(s:ℝ)+6)*canonicalCriticalVector s (n+1) (Fin.last n).castSucc*
        sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s (n+1) <
      ((2*((n+1:ℕ):ℝ)+(s:ℝ)+1)*(4*((n+1:ℕ):ℝ)+2*(s:ℝ)+3))*
        sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment (s+1) (n+2)
          (canonicalCriticalVector s (n+1))) :
    iteratedDeriv 2 (fun x => sigmaSchur x s (n+1)) 0 < 0 := by
  have hl := stationary_weighted_lower canonicalCompletedNativeLogDerivativeMoment s n
    (canonicalCriticalVector s (n+1)) _ (canonical_critical_relation s (n+1) hA) hold
  rw [pair_self] at hl
  rw [canonical_curvature_eq_weighted s (n+1) hA]
  linarith

end
end CarryCriticalEuler
