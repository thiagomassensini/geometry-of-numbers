import PhysicalPickNineNative
import CarrySelfAdjointOperator.CompletedNativeChiralPickHankel
import Mathlib.Tactic

/-!
Exact nine-point radial stencil congruence, transported from the
GENERAL all-order binomial coefficient theorem already proved in CSA.
No re-expansion of 81 crossings, no new metric, no Gram hypothesis.
-/
namespace CarrySelfAdjointOperator
open GeometryOfNumbers.Analysis Filter
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false

/-- Exactly the source-native signed binomial forward-difference matrix. -/
def completedGreenNinePointDifferenceTransform (h : ℂ) :
    Matrix (Fin 9) (Fin 9) ℂ :=
  completedGreenComplexForwardDifferenceTransform h 9

/-- ALL 81 crossings are transported via the general theorem of the
original complex Cauchy–Pick carrier, for any complex kernel. -/
theorem completedGreenNinePointDifference_congruence
    (kernel : ℂ → ℂ → ℂ) (h : ℂ) (_hh : h ≠ 0) :
    (Matrix.of fun p q : Fin 9 =>
      completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
    (completedGreenNinePointDifferenceTransform h)ᴴ *
      (Matrix.of fun i j : Fin 9 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) *
      completedGreenNinePointDifferenceTransform h := by
  have hsrc :
      (Matrix.of fun p q : Fin 9 =>
        completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
      completedGreenComplexShiftedKernelForwardDifferenceMatrix kernel h 9 := by
    ext p q
    exact (completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply
      kernel h 9 p q).symm
  have hgrid :
      completedGreenComplexShiftedKernelSampleMatrix kernel h 9 =
      Matrix.of (fun i j : Fin 9 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) := by
    ext i j
    change kernel (((i : ℕ) + 1 : ℕ) * h)
        (((j : ℕ) + 1 : ℕ) * h) =
      kernel (h + (i : ℕ) * h) (h + (j : ℕ) * h)
    congr 1 <;> push_cast <;> ring
  rw [hsrc]
  simp only [completedGreenComplexShiftedKernelForwardDifferenceMatrix,
    completedGreenNinePointDifferenceTransform, hgrid]

theorem canonicalCompletedNativeRadialNinePointDifferenceMatrix_eq_congruence
    (k : ℕ) :
    canonicalCompletedNativeRadialNinePointDifferenceMatrix k =
      (completedGreenNinePointDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k))ᴴ *
        canonicalCompletedNativeRadialDslopeSampleMatrix k 9 *
        completedGreenNinePointDifferenceTransform
          (canonicalCompletedC3RadialSecondStep k) := by
  rw [canonicalCompletedNativeRadialNinePointDifferenceMatrix,
    completedGreenNinePointDifference_congruence _ _
      (canonicalCompletedC3RadialSecondStep_ne_zero k)]
  congr 2
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [nsmul_eq_mul]

#print axioms completedGreenNinePointDifference_congruence
#print axioms canonicalCompletedNativeRadialNinePointDifferenceMatrix_eq_congruence

end
end CarrySelfAdjointOperator
