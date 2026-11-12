import SourceCoefficientGreen
import SourceSchurShift
import ChiralOrder11
import CofactorTransport

namespace C3CofactorChiral

open C3Cofactor C3GeneralCofactor CarrySourceBezout CarrySelfAdjointOperator
open CarryCriticalSource CarryCriticalRelative
open Filter Topology
open scoped Matrix

noncomputable section
set_option autoImplicit false

private abbrev coefficients : Fin 7 → ℝ := fun i => nativeC i.val

private theorem native_odd_block_eq :
    coefficientBlock (sourceKernel nativeC true) 3 =
      oddThirdB (sourceOddA coefficients) (sourceOddB coefficients)
        (sourceOddD coefficients) (sourceOddE coefficients)
        (sourceOddF coefficients) (sourceOddG coefficients) := by
  rw [CarrySourceDimensionThree.odd_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oddThirdB, coefficients, sourceOddA, sourceOddB, sourceOddD,
      sourceOddE, sourceOddF, sourceOddG] <;> ring

theorem c3_odd_third_cofactor_polynomial_positive :
    0 < oddPrefixDet (sourceOddA coefficients) (sourceOddB coefficients)
          (sourceOddD coefficients) *
        oddDirectionEnergy (sourceOddA coefficients) (sourceOddB coefficients)
          (sourceOddD coefficients) (sourceOddE coefficients) (sourceOddF coefficients)
          (sourceOddG coefficients) refXBall.center refYBall.center -
        oddAdjugateResidual (sourceOddA coefficients) (sourceOddB coefficients)
          (sourceOddD coefficients) (sourceOddE coefficients) (sourceOddF coefficients)
          refXBall.center refYBall.center :=
  (candidate_source_gate C3CofactorCorrelation.native_even_source_coefficient_boxes).2.2

theorem c3_odd_third_bezout_det_positive :
    0 < (coefficientBlock (sourceKernel nativeC true) 3).det := by
  rw [native_odd_block_eq, odd_third_cofactor_identity
    _ _ _ _ _ _ (refXBall.center : ℝ) (refYBall.center : ℝ)]
  exact c3_odd_third_cofactor_polynomial_positive

theorem c3_odd_third_native_pivot_positive : 0 < sourceMomentSchur h 1 2 := by
  have hB : (coefficientBlock (sourceKernel nativeC true) 3).PosDef := by
    rw [native_odd_block_eq]
    exact C3CofactorCorrelation.completed_native_odd_third_block_posDef
  exact sourceMomentSchur_pos_of_block_posDef h 1 2
    odd_third_prefix_isUnit_from_completed_c3 ((native_source_bezout_posDef_iff true 3).mp hB)

theorem c3_odd_third_source_schur_positive : 0 < sourceSchur nativeC true 2 := by
  rw [sourceSchur_eq_scaled nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero native_source_recurrence
    true 2 odd_third_prefix_isUnit_from_completed_c3]
  exact mul_pos (sq_pos_of_ne_zero completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero)
    c3_odd_third_native_pivot_positive

/-- The normalized Bézout cofactor is the coefficient vector already used
to synthesize the physical incident and returned states. -/
theorem c3_odd_cofactor_eq_criticalCoefficients :
    transportedCofactor nativeC true 2 = criticalCoefficients 1 2 := by
  exact transportedCofactor_eq_criticalVector nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero native_source_recurrence
    true 2 odd_third_prefix_isUnit_from_completed_c3

theorem c3_odd_third_gap_coefficient_positive : 0 < criticalGapCoefficient 1 2 :=
  odd_third_gap_coefficient_pos_iff.mpr c3_odd_third_native_pivot_positive

theorem c3_odd_third_scaled_relative_deficit_positive_limit :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ 11 * relativeDeficit 1 2 k) atTop (nhds L) :=
  ⟨criticalGapCoefficient 1 2, c3_odd_third_gap_coefficient_positive,
    odd_third_scaled_relative_deficit_tendsto⟩

theorem c3_odd_third_relative_gap_positive :
    ∀ᶠ k : ℕ in atTop, 0 < relativeDeficit 1 2 k :=
  odd_third_relative_deficit_eventually_pos c3_odd_third_native_pivot_positive

#print axioms c3_odd_third_cofactor_polynomial_positive
#print axioms c3_odd_third_bezout_det_positive
#print axioms c3_odd_third_native_pivot_positive
#print axioms c3_odd_third_source_schur_positive
#print axioms c3_odd_cofactor_eq_criticalCoefficients
#print axioms c3_odd_third_gap_coefficient_positive
#print axioms c3_odd_third_scaled_relative_deficit_positive_limit
#print axioms c3_odd_third_relative_gap_positive

end
end C3CofactorChiral
