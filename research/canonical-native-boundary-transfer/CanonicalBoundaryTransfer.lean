import CanonicalClockGap
import Regression
import CarrySelfAdjointOperator.CompletedNativeChiralBoundaryParityCoordinates
import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundarySplit
import CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesOperator
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace CanonicalNativeBoundaryTransfer
open scoped BigOperators ComplexConjugate Matrix
open GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator
open CarryStructuralKrylov
noncomputable section
set_option autoImplicit false

private def crossQuadratic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, M i j * (conj (u i) * u j).re

private theorem crossQuadratic_real_imag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℂ) :
    crossQuadratic M u =
      star (fun i => (u i).re) ⬝ᵥ (M *ᵥ fun i => (u i).re) +
      star (fun i => (u i).im) ⬝ᵥ (M *ᵥ fun i => (u i).im) := by
  change (∑ i, ∑ j, M i j * (conj (u i) * u j).re) =
    (∑ i, (u i).re * ∑ j, M i j * (u j).re) +
    (∑ i, (u i).im * ∑ j, M i j * (u j).im)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

private theorem crossQuadratic_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) (u : Fin n → ℂ) : 0 ≤ crossQuadratic M u := by
  rw [crossQuadratic_real_imag]
  exact add_nonneg (hM.posSemidef.dotProduct_mulVec_nonneg _)
    (hM.posSemidef.dotProduct_mulVec_nonneg _)

private theorem crossQuadratic_pos {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) (u : Fin n → ℂ) (hu : u ≠ 0) : 0 < crossQuadratic M u := by
  rw [crossQuadratic_real_imag]
  by_cases hr : (fun i => (u i).re) = 0
  · have hi : (fun i => (u i).im) ≠ 0 := by
      intro hi
      apply hu
      funext i
      apply Complex.ext
      · exact congrFun hr i
      · exact congrFun hi i
    exact add_pos_of_nonneg_of_pos (hM.posSemidef.dotProduct_mulVec_nonneg _)
      (hM.dotProduct_mulVec_pos hi)
  · exact add_pos_of_pos_of_nonneg (hM.dotProduct_mulVec_pos hr)
      (hM.posSemidef.dotProduct_mulVec_nonneg _)

/-- Fixed-order transfer: canonical Hankel positivity at size `n` implies
strict positivity of the original native boundary energy at size `2*n`. -/
theorem boundary_energy_pos_of_canonical_pair_posDef (n : ℕ)
  (hEven : (GeometryOfNumbers.Analysis.hankelGram canonicalCompletedNativeLogDerivativeMoment n).PosDef)
  (hOdd : (GeometryOfNumbers.Analysis.shiftedHankel canonicalCompletedNativeLogDerivativeMoment n).PosDef) :
    ∀ x : Fin (2 * n) → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy (2 * n) x := by
  intro x hx
  rw [nativeSourceFiniteBoundaryEnergy_even_split]
  change 0 < 4 *
    (crossQuadratic (hankelGram primeDepthGeometricMoment n) (nativeSourceEvenBoundaryPhase n x) +
      crossQuadratic (shiftedHankel primeDepthGeometricMoment n) (nativeSourceOddBoundaryPhase n x))
  rw [primeDepthGeometricMoment_eq_canonical]
  obtain he | ho := nativeSourceBoundaryPhase_nonzero n x hx
  · exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
      (crossQuadratic_pos hEven _ he) (crossQuadratic_nonneg hOdd _))
  · exact mul_pos (by norm_num) (add_pos_of_nonneg_of_pos
      (crossQuadratic_nonneg hEven _) (crossQuadratic_pos hOdd _ ho))

private theorem canonical_h6k6_posDef_native :
    (GeometryOfNumbers.Analysis.hankelGram canonicalCompletedNativeLogDerivativeMoment 6).PosDef ∧
      (GeometryOfNumbers.Analysis.shiftedHankel canonicalCompletedNativeLogDerivativeMoment 6).PosDef := by
  simpa [canonical_moments_eq_native] using regression_H6_K6

/-- Capstone target E12: strict positivity of the original native boundary
energy, reusing the canonical H6/K6 certificates. -/
theorem nativeSourceFiniteBoundaryEnergy_pos_12 :
    ∀ x : Fin 12 → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy 12 x := by
  have h6 := canonical_h6k6_posDef_native
  simpa [Nat.mul_comm] using
    boundary_energy_pos_of_canonical_pair_posDef 6 h6.1 h6.2

private def fin4to6 : Fin 4 → Fin 6 := Fin.castLE (by decide : 4 ≤ 6)

private theorem fin4to6_injective : Function.Injective fin4to6 := by
  intro a b h
  exact Fin.ext (by simpa [fin4to6] using congrArg Fin.val h)

private theorem hankel4_posDef_native :
  (GeometryOfNumbers.Analysis.hankelGram canonicalCompletedNativeLogDerivativeMoment 4).PosDef := by
  have h6 := canonical_h6k6_posDef_native
  have hsub := Matrix.PosDef.submatrix h6.1 fin4to6_injective
  convert hsub using 1
  ext i j
  simp [fin4to6]

private theorem shifted4_posDef_native :
  (GeometryOfNumbers.Analysis.shiftedHankel canonicalCompletedNativeLogDerivativeMoment 4).PosDef := by
  have h6 := canonical_h6k6_posDef_native
  have hsub := Matrix.PosDef.submatrix h6.2 fin4to6_injective
  convert hsub using 1
  ext i j
  simp [fin4to6]

/-- Capstone target E8: strict positivity of the original native boundary
energy, obtained by principal-section inheritance from the canonical 6x6 pair. -/
theorem nativeSourceFiniteBoundaryEnergy_pos_8 :
    ∀ x : Fin 8 → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy 8 x := by
  simpa [Nat.mul_comm] using
    boundary_energy_pos_of_canonical_pair_posDef 4 hankel4_posDef_native shifted4_posDef_native

end
end CanonicalNativeBoundaryTransfer
