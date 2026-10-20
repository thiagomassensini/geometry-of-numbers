import NativeApplication
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! Same source Schur formula, weakening the old algebraic sewing hypothesis
from positive definiteness to invertibility. No source definition is changed. -/
namespace NativeMomentOrthogonalization
open CarrySelfAdjointOperator
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1200000
theorem sourceMomentSchur_sewing_of_isUnit (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) (x : Fin n → ℝ) (t : ℝ) :
    sourceMomentQuadratic m s (n+1) (Fin.snoc x t) =
      sourceMomentQuadratic m s n
        (x + t • ((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n)) +
      sourceMomentSchur m s n*t^2 := by
  let A := sourceMomentMatrix m s n
  let b := sourceMomentCoupling m s n
  let v := A⁻¹ *ᵥ b
  letI := hA.invertible
  have hv : A *ᵥ v = b := by
    dsimp [v, A]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have ht : Aᵀ = A := by
    ext i j
    simp [A, sourceMomentMatrix, add_comm]
  have hxv : v ⬝ᵥ (A *ᵥ x) = b ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← ht, Matrix.vecMul_transpose, hv]
  have hq : sourceMomentQuadratic m s n (x+t • v) =
      sourceMomentQuadratic m s n x + 2*t*(b ⬝ᵥ x) + (b ⬝ᵥ v)*t^2 := by
    change (x+t • v) ⬝ᵥ (A *ᵥ (x+t • v)) =
      x ⬝ᵥ (A *ᵥ x) + 2*t*(b ⬝ᵥ x) + (b ⬝ᵥ v)*t^2
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hv]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hxv]
    rw [dotProduct_comm x b, dotProduct_comm v b]
    ring
  rw [sourceMomentQuadratic_snoc]
  change _ = sourceMomentQuadratic m s n (x+t • v) +
    (m (2*n+s)-b ⬝ᵥ v)*t^2
  rw [hq]
  ring

/-- A concrete nonzero test vector reads the exact next pivot. -/
theorem sourceMomentSchur_critical_direction_of_isUnit (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) :
    sourceMomentQuadratic m s (n+1)
      (Fin.snoc (-((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n)) 1) =
      sourceMomentSchur m s n := by
  rw [sourceMomentSchur_sewing_of_isUnit m s n hA]
  simp [sourceMomentQuadratic]


theorem momentForm_eq_sourceMomentQuadratic (m : ℕ → ℝ) (s n : ℕ) (a : Fin n → ℝ) :
    momentForm (fun k => m (k+s)) (coefficientPolynomial a) (coefficientPolynomial a) =
      sourceMomentQuadratic m s n a := by
  rw [momentForm_coefficients, GeometryOfNumbers.Analysis.carryPairingBilinear_eq_dotProduct]
  simp only [sourceMomentQuadratic, star_trivial]
  rfl

/-- Sector choice is the existing parity reindexing of real coefficients. -/
theorem native_boundary_real_sector (s : Fin 2) (N : ℕ) (u : Fin N → ℝ) :
    nativeSourceFiniteBoundaryEnergy (2*N)
      (if s = 0 then nativeSourceBoundaryFromParity N (fun i => (u i : ℂ)) 0
       else nativeSourceBoundaryFromParity N 0 (fun i => (u i : ℂ))) =
      4 * momentForm (fun k => canonicalCompletedNativeLogDerivativeMoment (k+s.val))
        (coefficientPolynomial u) (coefficientPolynomial u) := by
  fin_cases s
  · change nativeSourceFiniteBoundaryEnergy (2*N)
      (nativeSourceBoundaryFromParity N (fun i => (u i : ℂ)) 0) = _
    exact native_boundary_real_even N u
  · change nativeSourceFiniteBoundaryEnergy (2*N)
      (nativeSourceBoundaryFromParity N 0 (fun i => (u i : ℂ))) = _
    exact native_boundary_real_odd N u

/-- The original inverse-Schur critical coefficients in the original
boundary source, with invertibility and no sign of the old or new section. -/
theorem native_inverseSchur_boundary_energy (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s.val n)) :
    let a : Fin (n+1) → ℝ := Fin.snoc (-((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s.val n)⁻¹ *ᵥ
      sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s.val n)) 1
    nativeSourceFiniteBoundaryEnergy (2*(n+1))
      (if s = 0 then nativeSourceBoundaryFromParity (n+1) (fun i => (a i : ℂ)) 0
       else nativeSourceBoundaryFromParity (n+1) 0 (fun i => (a i : ℂ))) =
      4 * sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s.val n := by
  dsimp only
  rw [native_boundary_real_sector, momentForm_eq_sourceMomentQuadratic,
    sourceMomentSchur_critical_direction_of_isUnit _ _ _ hA]

end
end NativeMomentOrthogonalization
