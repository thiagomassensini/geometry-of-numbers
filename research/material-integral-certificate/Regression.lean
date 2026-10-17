import SourceIntegral

namespace CarryIntegralCertificate
open CarrySelfAdjointOperator GeometryOfNumbers.Analysis
set_option autoImplicit false

theorem thetaMode_zero_eq_thetaFirstMode : thetaMode 0 = thetaFirstMode := by
  funext u
  norm_num [thetaMode,XiThetaCosine.thetaTailMode,thetaFirstMode]
  ring

theorem thetaMode_fourth_matches_existing_cubic :
    thetaModeDerivative 0 4 = thetaFirstModeFourth := by
  rw [← iteratedDeriv_thetaMode,thetaMode_zero_eq_thetaFirstMode]
  exact thetaFirstMode_cubic_derivatives.2.2.2

/-- The old exact theta contrast remains the source obligation. -/
theorem fourth_pivot_preserves_theta_contrast :
    0 < carryMaterialFourthPivot ↔
      -(4*(Nat.factorial 18:ℝ))*
        CarryMaterialFourthPivotComparison.material_fourth_characteristic_ceiling <
        1224*completedNativeThetaTailMoment 16-completedNativeThetaTailMoment 18 := by
  simpa only [neg_mul] using
    CarryMaterialFourthPivotComparison.material_fourth_pivot_pos_iff_theta_balance

end CarryIntegralCertificate
