import MovingSchur

namespace CarryMovingSigma
open CarrySelfAdjointOperator CarrySigmaSource Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false

/-- Sector zero is the original even canonical Hankel. -/
theorem even_moving_schur_curvature (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n)) :
    iteratedDeriv 2 (fun d => sigmaSchur d 0 n) 0 =
      iteratedDeriv 2 (fun d => sigmaMomentForm d 0 (n+1) (canonicalCriticalVector 0 n)) 0 :=
  moving_schur_eq_fixed_form_curvature 0 n hA

/-- Sector one retains its shifted indices AND shifted curvature weights. -/
theorem odd_moving_schur_curvature (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)) :
    iteratedDeriv 2 (fun d => sigmaSchur d 1 n) 0 =
      iteratedDeriv 2 (fun d => sigmaMomentForm d 1 (n+1) (canonicalCriticalVector 1 n)) 0 :=
  moving_schur_eq_fixed_form_curvature 1 n hA

/-- The first even pivot is a nontrivial normalization check of the source. -/
theorem first_even_pivot_curvature :
    iteratedDeriv 2 (fun d => sigmaSchur d 0 0) 0 =
      -6 * canonicalCompletedNativeLogDerivativeMoment 1 := by
  have he : (fun d => sigmaSchur d 0 0) = (fun d => completedSigmaLogJet d 0) := by
    funext d
    simp [sigmaSchur,sourceMomentSchur,sourceMomentCoupling,dotProduct]
  rw [he,sigma_log_jet_curvature_center]
  norm_num

/-- The shifted first pivot has coefficient -20, not the even coefficient -6. -/
theorem first_odd_pivot_curvature :
    iteratedDeriv 2 (fun d => sigmaSchur d 1 0) 0 =
      -20 * canonicalCompletedNativeLogDerivativeMoment 2 := by
  have he : (fun d => sigmaSchur d 1 0) = (fun d => completedSigmaLogJet d 1) := by
    funext d
    simp [sigmaSchur,sourceMomentSchur,sourceMomentCoupling,dotProduct]
  rw [he,sigma_log_jet_curvature_center]
  norm_num

end
end CarryMovingSigma
