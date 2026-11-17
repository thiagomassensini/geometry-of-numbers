import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy
import CarrySelfAdjointOperator.CompletedNativeRadialThreePointDeterminant
import GeometryOfNumbers.Analysis.CarryMaterialPickThreeSchurCriterion
import Mathlib.Tactic

/-! Invertibility of the native two-point radial dslope section, proved
from the *already certified* confluent Taylor limit h0*h1>0.
No 2x2 PD is postulated. -/
namespace CarrySelfAdjointOperator
open Filter
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false

def completedGreenTwoPointDifferenceTransform (h : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, -h⁻¹; 0, h⁻¹]

theorem completedGreenTwoPointDifference_congruence
    (kernel : ℂ → ℂ → ℂ) (h : ℂ) (hh : h ≠ 0) :
    (Matrix.of fun p q : Fin 2 =>
      completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
    (completedGreenTwoPointDifferenceTransform h)ᴴ *
      (Matrix.of fun i j : Fin 2 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) *
      completedGreenTwoPointDifferenceTransform h := by
  have hc : conj h ≠ 0 := by simpa using hh
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [completedGreenTwoPointDifferenceTransform,
      completedGreenKernelTwoStepShiftedForwardDifference,
      completedGreenKernelTwoStepShiftedRawDifference,
      completedGreenForwardDifference,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      ] <;>
    field_simp [hh, hc] <;> ring

def canonicalCompletedNativeRadialTwoPointDifferenceMatrix (k : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun p q =>
    completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k)
      (canonicalCompletedC3RadialSecondStep k) p q

theorem canonicalCompletedNativeRadialTwoPointDifferenceMatrix_eq_congruence
    (k : ℕ) :
    canonicalCompletedNativeRadialTwoPointDifferenceMatrix k =
      (completedGreenTwoPointDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k))ᴴ *
      canonicalCompletedNativeRadialDslopeSampleMatrix k 2 *
      completedGreenTwoPointDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k) := by
  rw [canonicalCompletedNativeRadialTwoPointDifferenceMatrix,
    completedGreenTwoPointDifference_congruence _ _
      (canonicalCompletedC3RadialSecondStep_ne_zero k)]
  congr 2
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [nsmul_eq_mul]

theorem canonicalCompletedNativeRadialTwoPointDifferenceMatrix_tendsto :
    Tendsto canonicalCompletedNativeRadialTwoPointDifferenceMatrix atTop
      (nhds (Matrix.of fun i j : Fin 2 =>
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
    (canonicalCompletedC3RadialSecondStep k) (canonicalCompletedC3RadialSecondStep k)
    (i : ℕ) (j : ℕ)) atTop (nhds _)
  simpa only [Function.comp_def, Matrix.of_apply] using
    (completedNativePolarizedDslope_shiftedRadial_tendsto (i : ℕ) (j : ℕ)).comp hd

theorem polarizedGreenMomentCoefficient_two_det (h : ℕ → ℝ) :
    (Matrix.of fun i j : Fin 2 => polarizedGreenMomentCoefficient h i j).det =
      ((h 0 * h 1 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

theorem canonicalCompletedNativeRadialTwoPointDifferenceMatrix_det_tendsto :
    Tendsto (fun k => (canonicalCompletedNativeRadialTwoPointDifferenceMatrix k).det)
      atTop (nhds ((canonicalCompletedNativeLogDerivativeMoment 0 *
                     canonicalCompletedNativeLogDerivativeMoment 1 : ℝ) : ℂ)) := by
  have h := (continuous_id.matrix_det.tendsto _).comp
    canonicalCompletedNativeRadialTwoPointDifferenceMatrix_tendsto
  simpa only [Function.comp_def, id_eq, polarizedGreenMomentCoefficient_two_det] using h

theorem canonicalCompletedNativeRadialDslopeSampleMatrix_two_det_eventually_ne_zero :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialDslopeSampleMatrix k 2).det ≠ 0 := by
  have h0 : 0 < canonicalCompletedNativeLogDerivativeMoment 0 :=
    canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have h1 : 0 < canonicalCompletedNativeLogDerivativeMoment 1 :=
    (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      canonicalCompletedNativeLowOrderHerglotzCurvaturePositive).2
  have hLim : ((canonicalCompletedNativeLogDerivativeMoment 0 *
                 canonicalCompletedNativeLogDerivativeMoment 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos h0 h1))
  filter_upwards
    [canonicalCompletedNativeRadialTwoPointDifferenceMatrix_det_tendsto.eventually_ne hLim]
    with k hD
  rw [canonicalCompletedNativeRadialTwoPointDifferenceMatrix_eq_congruence,
    Matrix.det_mul, Matrix.det_mul] at hD
  intro hZero
  apply hD
  rw [hZero]
  simp

#print axioms canonicalCompletedNativeRadialDslopeSampleMatrix_two_det_eventually_ne_zero

end
end CarrySelfAdjointOperator
