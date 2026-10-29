import NativeBoundary
import QuarticCoefficient

namespace CarryStencilBoundary
open CarrySelfAdjointOperator NativeLaguerre CarryNativeTfvd CarryCriticalTfvd
open CarryCurvatureGreen
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem raw_stencil_two : rawStencil 2=
    Finsupp.single 0 1+Finsupp.single 1 (-2)+Finsupp.single 2 1 := by
  ext j
  rw [raw_stencil_apply]
  rcases j with _ | _ | _ | j
  · norm_num [completedGreenForwardWeight]
  · norm_num [completedGreenForwardWeight]
  · norm_num [completedGreenForwardWeight]
  · simp [completedGreenForwardWeight, Nat.choose_eq_zero_of_lt (by omega : 2 < j+3)]

/-- Regression against the original SECOND imaginary radial jet: its phase
is negative, unlike the unphased static stencil of order two. -/
theorem radial_second_regression (k : ℕ) : radialJetCoefficients k 2=criticalInput k 0 := by
  have hs : ((Nat.factorial 2 : ℂ)*canonicalCompletedC3RadialSecondStep k^2)⁻¹ =
      -(((k : ℝ)+1)^2 : ℂ)/2 := by simpa using second_scale k
  rw [radialJetCoefficients, raw_stencil_two, hs, critical_input_triple]
  ext j
  rcases j with _ | _ | _ | j
  all_goals simp [triple]

/-- The original static fourth stencil, with exactly its OLD 4! weights. -/
theorem static_fourth_regression : staticStencil 4=fourthShape := by
  simp only [staticStencil, rawStencil, fourthShape, Finset.smul_sum, smul_smul,
    div_eq_mul_inv, mul_comm]

theorem radial_fourth_regression (k : ℕ) :
    radialJetCoefficients k 4=(canonicalCompletedC3RadialSecondStep k^4)⁻¹ • fourthShape := by
  rw [← static_fourth_regression]
  simp only [radialJetCoefficients, staticStencil, smul_smul, mul_inv_rev]

theorem boundary_operator_two : boundaryOperator 2=
    (5 : ℂ) • 1-(2 : ℂ) • physicalRadialAdvance := by
  rw [boundary_operator_succ, boundary_operator_succ, boundary_operator_zero]
  norm_num
  unfold physicalComplement
  module

/-- The general boundary recovers the actual PR97 boundary vector, including
the original fourth radial step factor, without changing any coefficient. -/
theorem fourth_boundary_regression (k : ℕ) :
    nativeBoundary k 2=(canonicalCompletedC3RadialSecondStep k^4)⁻¹ •
      CarryQuarticBoundary.nativeBoundaryVector := by
  unfold nativeBoundary
  rw [boundary_operator_two]
  simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul,
    physicalRadialAdvance_feature, radialLeadingScalar,
    CarryQuarticBoundary.nativeBoundaryVector]
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    mul_one, pow_succ, pow_zero, mul_inv_rev, smul_smul]
  module

end
end CarryStencilBoundary
