import PhysicalPickSixNative
import PhysicalPickSevenEvenSourceHankel
import GeometryOfNumbers.Analysis.CarryMaterialPickSevenParity
import Mathlib.Tactic

/-!
The seven-point radial Cauchy--Pick finite-difference limit: parity
splits into the canonical even H4 and shifted odd K3. The original
material source independently certifies both scalar margins.
-/
namespace CarrySelfAdjointOperator
open Filter GeometryOfNumbers.Analysis CarryMaterialPhysicalSevenSource
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false

def canonicalCompletedNativeRadialSevenPointDifferenceMatrix (k : ℕ) :
    Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.of fun p q =>
    completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k)
      (canonicalCompletedC3RadialSecondStep k) p q

theorem canonicalCompletedNativeRadialSevenPointDifferenceMatrix_tendsto :
    Tendsto canonicalCompletedNativeRadialSevenPointDifferenceMatrix atTop
      (nhds (Matrix.of fun i j : Fin 7 =>
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

theorem polarizedGreenMomentCoefficient_seven_det (h : ℕ → ℝ) :
    (Matrix.of fun i j : Fin 7 => polarizedGreenMomentCoefficient h i j).det =
      (((hankelGram h 4).det * (shiftedHankel h 3).det : ℝ) : ℂ) := by
  have heq : (Matrix.of fun i j : Fin 7 =>
      polarizedGreenMomentCoefficient h i j) =
    !![(h 0 : ℂ), 0, (h 1 : ℂ), 0, (h 2 : ℂ), 0, (h 3 : ℂ);
       0, (h 1 : ℂ), 0, (h 2 : ℂ), 0, (h 3 : ℂ), 0;
       (h 1 : ℂ), 0, (h 2 : ℂ), 0, (h 3 : ℂ), 0, (h 4 : ℂ);
       0, (h 2 : ℂ), 0, (h 3 : ℂ), 0, (h 4 : ℂ), 0;
       (h 2 : ℂ), 0, (h 3 : ℂ), 0, (h 4 : ℂ), 0, (h 5 : ℂ);
       0, (h 3 : ℂ), 0, (h 4 : ℂ), 0, (h 5 : ℂ), 0;
       (h 3 : ℂ), 0, (h 4 : ℂ), 0, (h 5 : ℂ), 0, (h 6 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]
  rw [heq, c2_seven_parity_determinant]
  have hE :
      (!![(h 0 : ℂ), (h 1 : ℂ), (h 2 : ℂ), (h 3 : ℂ);
           (h 1 : ℂ), (h 2 : ℂ), (h 3 : ℂ), (h 4 : ℂ);
           (h 2 : ℂ), (h 3 : ℂ), (h 4 : ℂ), (h 5 : ℂ);
           (h 3 : ℂ), (h 4 : ℂ), (h 5 : ℂ), (h 6 : ℂ)] :
            Matrix (Fin 4) (Fin 4) ℂ) =
        (hankelGram h 4).map Complex.ofRealHom := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hO :
      (!![(h 1 : ℂ), (h 2 : ℂ), (h 3 : ℂ);
           (h 2 : ℂ), (h 3 : ℂ), (h 4 : ℂ);
           (h 3 : ℂ), (h 4 : ℂ), (h 5 : ℂ)] : Matrix (Fin 3) (Fin 3) ℂ) =
        (shiftedHankel h 3).map Complex.ofRealHom := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hE, hO]
  change (Complex.ofRealHom.mapMatrix (hankelGram h 4)).det *
      (Complex.ofRealHom.mapMatrix (shiftedHankel h 3)).det =
      Complex.ofRealHom ((hankelGram h 4).det * (shiftedHankel h 3).det)
  rw [← Complex.ofRealHom.map_det, ← Complex.ofRealHom.map_det,
    Complex.ofRealHom.map_mul]

theorem canonicalCompletedNativeRadialSevenPointDifferenceMatrix_det_tendsto :
    Tendsto (fun k => (canonicalCompletedNativeRadialSevenPointDifferenceMatrix k).det)
      atTop (nhds (((hankelGram canonicalCompletedNativeLogDerivativeMoment 4).det *
        (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 3).det : ℝ) : ℂ)) := by
  have h := (continuous_id.matrix_det.tendsto _).comp
    canonicalCompletedNativeRadialSevenPointDifferenceMatrix_tendsto
  simpa only [Function.comp_def, id_eq, polarizedGreenMomentCoefficient_seven_det] using h

theorem canonicalCompletedNativeRadialSevenPointDifferenceMatrix_det_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop,
      0 < (canonicalCompletedNativeRadialSevenPointDifferenceMatrix k).det.re := by
  have he : 0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 4).det :=
    canonical_native_unshifted_hankel_four_det_pos
  have ho : 0 < (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 3).det :=
    canonicalCompletedNativeShiftedHankel_three_det_pos
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    canonicalCompletedNativeRadialSevenPointDifferenceMatrix_det_tendsto
  apply Filter.Tendsto.eventually_lt tendsto_const_nhds ht
  simpa only [Complex.ofReal_re] using mul_pos he ho

#print axioms polarizedGreenMomentCoefficient_seven_det
#print axioms canonicalCompletedNativeRadialSevenPointDifferenceMatrix_det_eventually_re_pos

end
end CarrySelfAdjointOperator
