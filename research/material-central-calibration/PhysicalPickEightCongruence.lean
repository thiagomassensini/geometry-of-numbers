import PhysicalPickEightNative
import CarrySelfAdjointOperator.CompletedNativeChiralPickHankel
import Mathlib.Tactic

/-!
Exact eight-point radial stencil congruence, transported from the
GENERAL all-order binomial coefficient theorem already proved in CSA.
No re-expansion of 64 crossings, no new metric, no Gram hypothesis.
-/
namespace CarrySelfAdjointOperator
open GeometryOfNumbers.Analysis Filter
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false

/-- Exactly the source-native signed binomial forward-difference matrix. -/
def completedGreenEightPointDifferenceTransform (h : ℂ) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  completedGreenComplexForwardDifferenceTransform h 8

/-- ALL 64 crossings are transported via the general theorem of the
original complex Cauchy–Pick carrier, for any complex kernel. -/
theorem completedGreenEightPointDifference_congruence
    (kernel : ℂ → ℂ → ℂ) (h : ℂ) (_hh : h ≠ 0) :
    (Matrix.of fun p q : Fin 8 =>
      completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
    (completedGreenEightPointDifferenceTransform h)ᴴ *
      (Matrix.of fun i j : Fin 8 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) *
      completedGreenEightPointDifferenceTransform h := by
  have hsrc :
      (Matrix.of fun p q : Fin 8 =>
        completedGreenKernelTwoStepShiftedForwardDifference kernel h h p q) =
      completedGreenComplexShiftedKernelForwardDifferenceMatrix kernel h 8 := by
    ext p q
    exact (completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply
      kernel h 8 p q).symm
  have hgrid :
      completedGreenComplexShiftedKernelSampleMatrix kernel h 8 =
      Matrix.of (fun i j : Fin 8 => kernel (h+(i:ℕ)*h) (h+(j:ℕ)*h)) := by
    ext i j
    change kernel (((i : ℕ) + 1 : ℕ) * h)
        (((j : ℕ) + 1 : ℕ) * h) =
      kernel (h + (i : ℕ) * h) (h + (j : ℕ) * h)
    congr 1 <;> push_cast <;> ring
  rw [hsrc]
  simp only [completedGreenComplexShiftedKernelForwardDifferenceMatrix,
    completedGreenEightPointDifferenceTransform, hgrid]

theorem canonicalCompletedNativeRadialEightPointDifferenceMatrix_eq_congruence
    (k : ℕ) :
    canonicalCompletedNativeRadialEightPointDifferenceMatrix k =
      (completedGreenEightPointDifferenceTransform
        (canonicalCompletedC3RadialSecondStep k))ᴴ *
        canonicalCompletedNativeRadialDslopeSampleMatrix k 8 *
        completedGreenEightPointDifferenceTransform
          (canonicalCompletedC3RadialSecondStep k) := by
  rw [canonicalCompletedNativeRadialEightPointDifferenceMatrix,
    completedGreenEightPointDifference_congruence _ _
      (canonicalCompletedC3RadialSecondStep_ne_zero k)]
  congr 2
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [nsmul_eq_mul]

#print axioms completedGreenEightPointDifference_congruence
#print axioms canonicalCompletedNativeRadialEightPointDifferenceMatrix_eq_congruence

end
end CarrySelfAdjointOperator
