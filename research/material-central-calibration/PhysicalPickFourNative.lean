import PhysicalPickTwoStrictNative
import CarrySelfAdjointOperator.CompletedNativeShiftedHankelEighthGate
import GeometryOfNumbers.Analysis.CarryMaterialPickFourParity
import Mathlib.Tactic

/-!
The fourth polarized Cauchy-Pick confluent determinant is the product
of the **already certified** unshifted and shifted 2x2 Hankel minors.
The genuine 4x4 source is not defined as a Hankel Gram: the comparison
comes from the limit of normalized finite differences.
-/
namespace CarrySelfAdjointOperator
open Filter GeometryOfNumbers.Analysis
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false

def canonicalCompletedNativeRadialFourPointDifferenceMatrix (k : ℕ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun p q =>
    completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k)
      (canonicalCompletedC3RadialSecondStep k) p q

theorem canonicalCompletedNativeRadialFourPointDifferenceMatrix_tendsto :
    Tendsto canonicalCompletedNativeRadialFourPointDifferenceMatrix atTop
      (nhds (Matrix.of fun i j : Fin 4 =>
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment i j)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hd : Tendsto (fun k : ℕ => (k,k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  change Tendsto (fun k => completedGreenKernelTwoStepShiftedForwardDifference
    canonicalCompletedNativePolarizedDslopeKernel
    (canonicalCompletedC3RadialSecondStep k)
    (canonicalCompletedC3RadialSecondStep k)
    (i : ℕ) (j : ℕ)) atTop (nhds _)
  simpa only [Function.comp_def, Matrix.of_apply] using
    (completedNativePolarizedDslope_shiftedRadial_tendsto (i : ℕ) (j : ℕ)).comp hd

theorem polarizedGreenMomentCoefficient_four_det (h : ℕ → ℝ) :
    (Matrix.of fun i j : Fin 4 => polarizedGreenMomentCoefficient h i j).det =
      (((h 0 * h 2 - h 1^2) * (h 1 * h 3 - h 2^2) : ℝ) : ℂ) := by
  have heq : (Matrix.of fun i j : Fin 4 =>
      polarizedGreenMomentCoefficient h i j) =
    !![(h 0 : ℂ), 0, (h 1 : ℂ), 0;
       0, (h 1 : ℂ), 0, (h 2 : ℂ);
       (h 1 : ℂ), 0, (h 2 : ℂ), 0;
       0, (h 2 : ℂ), 0, (h 3 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]
  rw [heq, c2_four_parity_determinant]
  push_cast
  ring

theorem canonicalCompletedNativeRadialFourPointDifferenceMatrix_det_tendsto :
    Tendsto (fun k => (canonicalCompletedNativeRadialFourPointDifferenceMatrix k).det) atTop
      (nhds (((canonicalCompletedNativeLogDerivativeMoment 0 *
        canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1 ^ 2) *
        (canonicalCompletedNativeLogDerivativeMoment 1 *
        canonicalCompletedNativeLogDerivativeMoment 3 -
        canonicalCompletedNativeLogDerivativeMoment 2 ^ 2) : ℝ) : ℂ)) := by
  have h := (continuous_id.matrix_det.tendsto _).comp
    canonicalCompletedNativeRadialFourPointDifferenceMatrix_tendsto
  simpa only [Function.comp_def, id_eq, polarizedGreenMomentCoefficient_four_det] using h

theorem canonicalCompletedNativeRadialFourPointDifferenceMatrix_det_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop,
      0 < (canonicalCompletedNativeRadialFourPointDifferenceMatrix k).det.re := by
  have he : 0 < canonicalCompletedNativeLogDerivativeMoment 0 *
      canonicalCompletedNativeLogDerivativeMoment 2 -
      canonicalCompletedNativeLogDerivativeMoment 1 ^ 2 := by
    simpa [canonicalCompletedNativeHankel_two_det_eq] using
      canonicalCompletedNativeHankel_two_det_pos
  have ho : 0 < canonicalCompletedNativeLogDerivativeMoment 1 *
      canonicalCompletedNativeLogDerivativeMoment 3 -
      canonicalCompletedNativeLogDerivativeMoment 2 ^ 2 := by
    simpa [canonicalCompletedNativeShiftedHankel_two_det_eq] using
      canonicalCompletedNativeShiftedHankel_two_det_pos
  have hLimit : 0 < ((
      (canonicalCompletedNativeLogDerivativeMoment 0 *
        canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1 ^ 2) *
      (canonicalCompletedNativeLogDerivativeMoment 1 *
        canonicalCompletedNativeLogDerivativeMoment 3 -
        canonicalCompletedNativeLogDerivativeMoment 2 ^ 2) : ℝ) : ℂ).re := by
    exact_mod_cast (mul_pos he ho)
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    canonicalCompletedNativeRadialFourPointDifferenceMatrix_det_tendsto
  exact Filter.Tendsto.eventually_lt tendsto_const_nhds ht hLimit

#print axioms polarizedGreenMomentCoefficient_four_det
#print axioms canonicalCompletedNativeRadialFourPointDifferenceMatrix_det_eventually_re_pos

end
end CarrySelfAdjointOperator
