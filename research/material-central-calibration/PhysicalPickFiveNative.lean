import PhysicalPickFiveSourceHankel
import CarrySelfAdjointOperator.CompletedNativeShiftedHankelEighthGate
import GeometryOfNumbers.Analysis.CarryMaterialPickFiveParity
import Mathlib.Tactic

/-!
The five-point physical Pick confluent limit is parity split:
  even 3×3 unshifted native Hankel times odd 2×2 shifted Hankel.
Both determinants have independent existing theta/material certificates.
The 5×5 Cauchy kernel itself is NOT defined as a moment Gram.
-/
namespace CarrySelfAdjointOperator
open Filter GeometryOfNumbers.Analysis CarryMaterialPhysicalFiveSource
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false

def canonicalCompletedNativeRadialFivePointDifferenceMatrix (k : ℕ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun p q =>
    completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k)
      (canonicalCompletedC3RadialSecondStep k) p q

theorem canonicalCompletedNativeRadialFivePointDifferenceMatrix_tendsto :
    Tendsto canonicalCompletedNativeRadialFivePointDifferenceMatrix atTop
      (nhds (Matrix.of fun i j : Fin 5 =>
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

theorem polarizedGreenMomentCoefficient_five_det (h : ℕ → ℝ) :
    (Matrix.of fun i j : Fin 5 => polarizedGreenMomentCoefficient h i j).det =
      (((hankelGram h 3).det * (shiftedHankel h 2).det : ℝ) : ℂ) := by
  have heq : (Matrix.of fun i j : Fin 5 =>
      polarizedGreenMomentCoefficient h i j) =
    !![(h 0 : ℂ), 0, (h 1 : ℂ), 0, (h 2 : ℂ);
       0, (h 1 : ℂ), 0, (h 2 : ℂ), 0;
       (h 1 : ℂ), 0, (h 2 : ℂ), 0, (h 3 : ℂ);
       0, (h 2 : ℂ), 0, (h 3 : ℂ), 0;
       (h 2 : ℂ), 0, (h 3 : ℂ), 0, (h 4 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]
  rw [heq, c2_five_parity_determinant]
  have hE :
      (!![(h 0 : ℂ), (h 1 : ℂ), (h 2 : ℂ);
           (h 1 : ℂ), (h 2 : ℂ), (h 3 : ℂ);
           (h 2 : ℂ), (h 3 : ℂ), (h 4 : ℂ)] : Matrix (Fin 3) (Fin 3) ℂ) =
        (hankelGram h 3).map Complex.ofRealHom := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hO :
      (!![(h 1 : ℂ), (h 2 : ℂ);
           (h 2 : ℂ), (h 3 : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) =
        (shiftedHankel h 2).map Complex.ofRealHom := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hE, hO]
  change (Complex.ofRealHom.mapMatrix (hankelGram h 3)).det *
      (Complex.ofRealHom.mapMatrix (shiftedHankel h 2)).det =
      Complex.ofRealHom ((hankelGram h 3).det * (shiftedHankel h 2).det)
  rw [← Complex.ofRealHom.map_det, ← Complex.ofRealHom.map_det,
    Complex.ofRealHom.map_mul]


theorem canonicalCompletedNativeRadialFivePointDifferenceMatrix_det_tendsto :
    Tendsto (fun k => (canonicalCompletedNativeRadialFivePointDifferenceMatrix k).det)
      atTop (nhds (((hankelGram canonicalCompletedNativeLogDerivativeMoment 3).det *
        (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 2).det : ℝ) : ℂ)) := by
  have h := (continuous_id.matrix_det.tendsto _).comp
    canonicalCompletedNativeRadialFivePointDifferenceMatrix_tendsto
  simpa only [Function.comp_def, id_eq, polarizedGreenMomentCoefficient_five_det] using h

theorem canonicalCompletedNativeRadialFivePointDifferenceMatrix_det_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop,
      0 < (canonicalCompletedNativeRadialFivePointDifferenceMatrix k).det.re := by
  have he : 0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 3).det :=
    canonical_native_unshifted_hankel_three_det_pos
  have ho : 0 < (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 2).det :=
    canonicalCompletedNativeShiftedHankel_two_det_pos
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    canonicalCompletedNativeRadialFivePointDifferenceMatrix_det_tendsto
  apply Filter.Tendsto.eventually_lt tendsto_const_nhds ht
  simpa only [Complex.ofReal_re] using mul_pos he ho

#print axioms polarizedGreenMomentCoefficient_five_det
#print axioms canonicalCompletedNativeRadialFivePointDifferenceMatrix_det_eventually_re_pos

end
end CarrySelfAdjointOperator
