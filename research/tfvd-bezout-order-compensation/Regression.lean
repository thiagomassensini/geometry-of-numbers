import RankOneUpdate
import SourceBlocks

namespace CarrySourceBezout
noncomputable section
set_option autoImplicit false

/-- Independent 2-by-2 ordinary block regression, in the requested ordering. -/
theorem regression_even_two (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c false) 2 =
      !![-c 0*c 1, -2*c 0*c 2;
         -2*c 0*c 2, -c 1*c 2-3*c 0*c 3] :=
  source_even_two c

/-- Independent 2-by-2 shifted block regression. -/
theorem regression_odd_two (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c true) 2 =
      !![c 1^2-2*c 0*c 2, c 1*c 2-3*c 0*c 3;
         c 1*c 2-3*c 0*c 3, 2*c 2^2-2*c 1*c 3-4*c 0*c 4] :=
  source_odd_two c

/-- The third ordinary direction has only the coefficient `c₅` in its new
diagonal term, with the sign and normalization already recorded by PR #145. -/
theorem regression_even_three_last_entry (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c false) 3 (Fin.last 2) (Fin.last 2) =
      -5*c 0*c 5-3*c 1*c 4-c 2*c 3 := by
  change PowerSeries.coeff 2 (PowerSeries.coeff 2 (sourceKernel c false)) = _
  rw [sourceKernel_even_coefficient_explicit]
  norm_num [Finset.sum_range_succ]
  ring

/-- The third shifted direction has only the coefficient `c₆` in its new
diagonal term, including the exact quadratic correction from earlier jets. -/
theorem regression_odd_three_last_entry (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c true) 3 (Fin.last 2) (Fin.last 2) =
      -6*c 0*c 6-4*c 1*c 5-2*c 2*c 4+3*(c 3)^2 := by
  change PowerSeries.coeff 2 (PowerSeries.coeff 2 (sourceKernel c true)) = _
  rw [sourceKernel_odd_coefficient_explicit]
  norm_num [Finset.sum_range_succ]
  ring

theorem regression_even_three_last_update (c : ℕ → ℝ) (δ : ℝ) :
    coefficientBlock (sourceKernel (sourceCoefficientUpdate c 5 δ) false) 3
        (Fin.last 2) (Fin.last 2) =
      coefficientBlock (sourceKernel c false) 3 (Fin.last 2) (Fin.last 2) -
        5*c 0*δ := by
  have h := sourceKernel_even_last_update c 2 δ
  norm_num at h
  simpa [coefficientBlock] using h

theorem regression_odd_three_last_update (c : ℕ → ℝ) (δ : ℝ) :
    coefficientBlock (sourceKernel (sourceCoefficientUpdate c 6 δ) true) 3
        (Fin.last 2) (Fin.last 2) =
      coefficientBlock (sourceKernel c true) 3 (Fin.last 2) (Fin.last 2) -
        6*c 0*δ := by
  have h := sourceKernel_odd_last_update c 2 δ
  norm_num at h
  simpa [coefficientBlock] using h

/-- The synthetic series `1-u-u²` is an exact negative control, not a Carry source. -/
theorem regression_negative_control :
    ¬(coefficientBlock (sourceKernel negativeControl false) 2).PosSemidef :=
  negative_control_not_posSemidef

#print axioms regression_even_two
#print axioms regression_odd_two
#print axioms regression_even_three_last_entry
#print axioms regression_odd_three_last_entry
#print axioms regression_even_three_last_update
#print axioms regression_odd_three_last_update
#print axioms regression_negative_control

end
end CarrySourceBezout
