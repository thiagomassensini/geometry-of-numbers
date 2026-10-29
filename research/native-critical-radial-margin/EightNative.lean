import EightSign

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarryOddEnergy CarrySummableRadial NativeMomentOrthogonalization
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem fourth_odd_original_boundary_positive :
    let a : Fin 4 → ℝ := Fin.snoc (-(eightOldMatrix⁻¹ *ᵥ eightCoupling)) 1
    0 < nativeSourceFiniteBoundaryEnergy 8
      (nativeSourceBoundaryFromParity 4 0 (fun i => (a i:ℂ))) := by
  have hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment (1 : Fin 2).val 3) :=
    eight_old_matrix_isUnit
  have he := native_inverseSchur_boundary_energy (1 : Fin 2) 3 hA
  have hs : (1 : Fin 2) ≠ 0 := by decide
  simp only [hs,if_false] at he
  have he' : nativeSourceFiniteBoundaryEnergy 8
      (nativeSourceBoundaryFromParity 4 0
        (fun i => Complex.ofReal ((Fin.snoc (-(eightOldMatrix⁻¹ *ᵥ eightCoupling)) (1:ℝ) : Fin 4 → ℝ) i))) =
      4*sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 3 := by
    simpa [eightOldMatrix,eightCoupling] using he
  dsimp only
  rw [he']
  exact mul_pos (by norm_num) fourth_odd_schur_positive_via_source_anchor

end
end CarryCriticalRadialMargin
