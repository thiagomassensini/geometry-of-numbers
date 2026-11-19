import PhysicalPickSixNative
import Mathlib.Tactic

/-! Exact fifth-order forward difference coordinate transform
on ALL 36 crossings of an arbitrary complex two-variable kernel.
No Gram positivity or Hilbert isometry is presumed.
-/
namespace CarrySelfAdjointOperator
open GeometryOfNumbers.Analysis Filter
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

def completedGreenSixPointDifferenceTransform (h : ℂ) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  !![1, -h⁻¹, (2*h^2)⁻¹, -(6*h^3)⁻¹, (24*h^4)⁻¹, -(120*h^5)⁻¹;
     0, h⁻¹, -(h^2)⁻¹, (2*h^3)⁻¹, -(6*h^4)⁻¹, (24*h^5)⁻¹;
     0, 0, (2*h^2)⁻¹, -(2*h^3)⁻¹, (4*h^4)⁻¹, -(12*h^5)⁻¹;
     0, 0, 0, (6*h^3)⁻¹, -(6*h^4)⁻¹, (12*h^5)⁻¹;
     0, 0, 0, 0, (24*h^4)⁻¹, -(24*h^5)⁻¹;
     0, 0, 0, 0, 0, (120*h^5)⁻¹]

theorem completedGreenSixPointDifference_congruence
    (kernel : ℂ → ℂ → ℂ) (h : ℂ) (hh : h ≠ 0) :
    (Matrix.of fun p q : Fin 6 =>
      completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
    (completedGreenSixPointDifferenceTransform h)ᴴ *
      (Matrix.of fun i j : Fin 6 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) *
      completedGreenSixPointDifferenceTransform h := by
  have hc : conj h ≠ 0 := by simpa using hh
  have hstar4 : (starRingEnd ℂ) (4 : ℂ) = 4 := map_natCast (starRingEnd ℂ) 4
  have hstar6 : (starRingEnd ℂ) (6 : ℂ) = 6 := map_natCast (starRingEnd ℂ) 6
  have hstar12 : (starRingEnd ℂ) (12 : ℂ) = 12 := map_natCast (starRingEnd ℂ) 12
  have hstar24 : (starRingEnd ℂ) (24 : ℂ) = 24 := map_natCast (starRingEnd ℂ) 24
  have hstar120 : (starRingEnd ℂ) (120 : ℂ) = 120 := map_natCast (starRingEnd ℂ) 120
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [completedGreenSixPointDifferenceTransform,
      completedGreenKernelTwoStepShiftedForwardDifference,
      completedGreenKernelTwoStepShiftedRawDifference,
      Function.iterate_succ_apply, completedGreenForwardDifference,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      two_mul, add_assoc] <;>
    field_simp [hh, hc]
  all_goals
    try simp only [hstar4, hstar6, hstar12, hstar24, hstar120]
    ring

theorem canonicalCompletedNativeRadialSixPointDifferenceMatrix_eq_congruence
    (k : ℕ) :
    canonicalCompletedNativeRadialSixPointDifferenceMatrix k =
      (completedGreenSixPointDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k))ᴴ *
        canonicalCompletedNativeRadialDslopeSampleMatrix k 6 *
        completedGreenSixPointDifferenceTransform
          (canonicalCompletedC3RadialSecondStep k) := by
  rw [canonicalCompletedNativeRadialSixPointDifferenceMatrix,
    completedGreenSixPointDifference_congruence _ _
      (canonicalCompletedC3RadialSecondStep_ne_zero k)]
  congr 2
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [nsmul_eq_mul]

#print axioms completedGreenSixPointDifference_congruence
#print axioms canonicalCompletedNativeRadialSixPointDifferenceMatrix_eq_congruence

end
end CarrySelfAdjointOperator
