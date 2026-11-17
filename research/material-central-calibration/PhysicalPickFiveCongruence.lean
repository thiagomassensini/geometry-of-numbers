import PhysicalPickFiveNative
import Mathlib.Tactic

/-! Exact fourth-order forward difference coordinates, preserving the
full physical complex Cauchy kernel and all 25 cross entries. -/
namespace CarrySelfAdjointOperator
open GeometryOfNumbers.Analysis Filter
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def completedGreenFivePointDifferenceTransform (h : ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  !![1, -h⁻¹, (2*h^2)⁻¹, -(6*h^3)⁻¹, (24*h^4)⁻¹;
     0, h⁻¹, -(h^2)⁻¹, (2*h^3)⁻¹, -(6*h^4)⁻¹;
     0, 0, (2*h^2)⁻¹, -(2*h^3)⁻¹, (4*h^4)⁻¹;
     0, 0, 0, (6*h^3)⁻¹, -(6*h^4)⁻¹;
     0, 0, 0, 0, (24*h^4)⁻¹]

theorem completedGreenFivePointDifference_congruence
    (kernel : ℂ → ℂ → ℂ) (h : ℂ) (hh : h ≠ 0) :
    (Matrix.of fun p q : Fin 5 =>
      completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
    (completedGreenFivePointDifferenceTransform h)ᴴ *
      (Matrix.of fun i j : Fin 5 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) *
      completedGreenFivePointDifferenceTransform h := by
  have hc : conj h ≠ 0 := by simpa using hh
  have hstar4 : (starRingEnd ℂ) (4 : ℂ) = 4 := map_natCast (starRingEnd ℂ) 4
  have hstar6 : (starRingEnd ℂ) (6 : ℂ) = 6 := map_natCast (starRingEnd ℂ) 6
  have hstar24 : (starRingEnd ℂ) (24 : ℂ) = 24 := map_natCast (starRingEnd ℂ) 24
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [completedGreenFivePointDifferenceTransform,
      completedGreenKernelTwoStepShiftedForwardDifference,
      completedGreenKernelTwoStepShiftedRawDifference,
      Function.iterate_succ_apply, completedGreenForwardDifference,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      two_mul, add_assoc] <;>
    field_simp [hh, hc]
  all_goals
    try simp only [hstar4, hstar6, hstar24]
    ring

theorem canonicalCompletedNativeRadialFivePointDifferenceMatrix_eq_congruence
    (k : ℕ) :
    canonicalCompletedNativeRadialFivePointDifferenceMatrix k =
      (completedGreenFivePointDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k))ᴴ *
        canonicalCompletedNativeRadialDslopeSampleMatrix k 5 *
        completedGreenFivePointDifferenceTransform
          (canonicalCompletedC3RadialSecondStep k) := by
  rw [canonicalCompletedNativeRadialFivePointDifferenceMatrix,
    completedGreenFivePointDifference_congruence _ _
      (canonicalCompletedC3RadialSecondStep_ne_zero k)]
  congr 2
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [nsmul_eq_mul]

#print axioms completedGreenFivePointDifference_congruence
#print axioms canonicalCompletedNativeRadialFivePointDifferenceMatrix_eq_congruence

end
end CarrySelfAdjointOperator
