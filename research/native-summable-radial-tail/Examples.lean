import SummableFamily
import SixRegression

namespace CarrySummableRadial
open CarryOddCauchy CarrySpatialCorrection
noncomputable section
set_option autoImplicit false

theorem six_grid_cutoff_value : oddGridCutoff sixOrders = 24 := by
  norm_num [oddGridCutoff, oddGridSize, sixOrders, Finset.sup_insert, Finset.sup_empty]

theorem first_pair_constant_value : pairConstant 0 0 = (209:ℝ)/3 := by
  norm_num [pairConstant, oddFilterBudget, oddFilterCoefficient, nativeOddBeta,
    spatialCorrection, CarrySpatialCorrection.slope, CarrySpatialCorrection.curvature, Finset.sum_range_succ, Finset.sum_range_zero,
    Complex.norm_real, Real.norm_eq_abs, Nat.choose]

end
end CarrySummableRadial
