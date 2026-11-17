import PhysicalPickFourNative
import Mathlib.Tactic

/-! Exact fourth-order forward difference coordinates, preserving the
full physical complex Cauchy kernel and all 16 cross entries. -/
namespace CarrySelfAdjointOperator
open GeometryOfNumbers.Analysis Filter
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false

def completedGreenFourPointDifferenceTransform (h : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, -h⁻¹, (2*h^2)⁻¹, -(6*h^3)⁻¹;
     0, h⁻¹, -(h^2)⁻¹, (2*h^3)⁻¹;
     0, 0, (2*h^2)⁻¹, -(2*h^3)⁻¹;
     0, 0, 0, (6*h^3)⁻¹]

theorem completedGreenFourPointDifference_congruence
    (kernel : ℂ → ℂ → ℂ) (h : ℂ) (hh : h ≠ 0) :
    (Matrix.of fun p q : Fin 4 =>
      completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
    (completedGreenFourPointDifferenceTransform h)ᴴ *
      (Matrix.of fun i j : Fin 4 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) *
      completedGreenFourPointDifferenceTransform h := by
  have hc : conj h ≠ 0 := by simpa using hh
  have hstar6 : (starRingEnd ℂ) (6 : ℂ) = 6 := by
    exact map_natCast (starRingEnd ℂ) 6
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [completedGreenFourPointDifferenceTransform,
      completedGreenKernelTwoStepShiftedForwardDifference,
      completedGreenKernelTwoStepShiftedRawDifference,
      Function.iterate_succ_apply, completedGreenForwardDifference,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      two_mul, add_assoc] <;>
    field_simp [hh, hc]
  all_goals
    try simp only [hstar6]
    ring

theorem canonicalCompletedNativeRadialFourPointDifferenceMatrix_eq_congruence
    (k : ℕ) :
    canonicalCompletedNativeRadialFourPointDifferenceMatrix k =
      (completedGreenFourPointDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k))ᴴ *
        canonicalCompletedNativeRadialDslopeSampleMatrix k 4 *
        completedGreenFourPointDifferenceTransform
          (canonicalCompletedC3RadialSecondStep k) := by
  rw [canonicalCompletedNativeRadialFourPointDifferenceMatrix,
    completedGreenFourPointDifference_congruence _ _
      (canonicalCompletedC3RadialSecondStep_ne_zero k)]
  congr 2
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [nsmul_eq_mul]

#print axioms completedGreenFourPointDifference_congruence
#print axioms canonicalCompletedNativeRadialFourPointDifferenceMatrix_eq_congruence

end
end CarrySelfAdjointOperator
