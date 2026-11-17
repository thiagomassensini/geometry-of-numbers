import PhysicalPickSevenNative
import CarrySelfAdjointOperator.CompletedNativeChiralPickHankel
import Mathlib.Tactic

/-!
Exact seven-point radial stencil congruence, transported from the
GENERAL all-order binomial coefficient theorem already proved in CSA.
No re-expansion of 49 crossings, no new metric, no Gram hypothesis.
-/
namespace CarrySelfAdjointOperator
open GeometryOfNumbers.Analysis Filter
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false

/-- Exactly the source-native signed binomial forward-difference matrix. -/
def completedGreenSevenPointDifferenceTransform (h : ℂ) :
    Matrix (Fin 7) (Fin 7) ℂ :=
  completedGreenComplexForwardDifferenceTransform h 7

/-- ALL 49 crossings are transported via the general theorem of the
original complex Cauchy–Pick carrier, for any complex kernel. -/
theorem completedGreenSevenPointDifference_congruence
    (kernel : ℂ → ℂ → ℂ) (h : ℂ) (_hh : h ≠ 0) :
    (Matrix.of fun p q : Fin 7 =>
      completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
    (completedGreenSevenPointDifferenceTransform h)ᴴ *
      (Matrix.of fun i j : Fin 7 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) *
      completedGreenSevenPointDifferenceTransform h := by
  have hsrc :
      (Matrix.of fun p q : Fin 7 =>
        completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
      completedGreenComplexShiftedKernelForwardDifferenceMatrix kernel h 7 := by
    ext p q
    exact (completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply
      kernel h 7 p q).symm
  have hgrid :
      completedGreenComplexShiftedKernelSampleMatrix kernel h 7 =
      Matrix.of (fun i j : Fin 7 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) := by
    ext i j
    change kernel (((i : ℕ) + 1 : ℕ) * h)
        (((j : ℕ) + 1 : ℕ) * h) =
      kernel (h + (i : ℕ) * h) (h + (j : ℕ) * h)
    congr 1 <;> push_cast <;> ring
  rw [hsrc]
  simp only [completedGreenComplexShiftedKernelForwardDifferenceMatrix,
    completedGreenSevenPointDifferenceTransform, hgrid]

theorem canonicalCompletedNativeRadialSevenPointDifferenceMatrix_eq_congruence
    (k : ℕ) :
    canonicalCompletedNativeRadialSevenPointDifferenceMatrix k =
      (completedGreenSevenPointDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k))ᴴ *
        canonicalCompletedNativeRadialDslopeSampleMatrix k 7 *
        completedGreenSevenPointDifferenceTransform
          (canonicalCompletedC3RadialSecondStep k) := by
  rw [canonicalCompletedNativeRadialSevenPointDifferenceMatrix,
    completedGreenSevenPointDifference_congruence _ _
      (canonicalCompletedC3RadialSecondStep_ne_zero k)]
  congr 2
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [nsmul_eq_mul]

#print axioms completedGreenSevenPointDifference_congruence
#print axioms canonicalCompletedNativeRadialSevenPointDifferenceMatrix_eq_congruence

end
end CarrySelfAdjointOperator
