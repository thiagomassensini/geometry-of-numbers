import PhysicalPickNineCongruence
import Mathlib.Tactic

/-!
Determinant sign on the *original* native 9×9 radial Pick matrix.
The genuine seven-point finite difference is a congruence, so its strictly
positive determinant transfers without assuming a positive target Gram.
-/
namespace CarrySelfAdjointOperator
open Filter
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
set_option autoImplicit false

theorem canonicalCompletedNativeRadialDslopeSampleMatrix_nine_det_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop,
      0 < (canonicalCompletedNativeRadialDslopeSampleMatrix k 9).det.re := by
  filter_upwards
    [canonicalCompletedNativeRadialNinePointDifferenceMatrix_det_eventually_re_pos]
    with k hDif
  let T := completedGreenNinePointDifferenceTransform
    (canonicalCompletedC3RadialSecondStep k)
  let M := canonicalCompletedNativeRadialDslopeSampleMatrix k 9
  have hdet :
      (canonicalCompletedNativeRadialNinePointDifferenceMatrix k).det =
        (Complex.normSq T.det : ℂ) * M.det := by
    calc
      (canonicalCompletedNativeRadialNinePointDifferenceMatrix k).det =
          (Tᴴ * M * T).det := by
            rw [canonicalCompletedNativeRadialNinePointDifferenceMatrix_eq_congruence]
      _ = star T.det * M.det * T.det := by
            rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
      _ = (T.det * star T.det) * M.det := by ring
      _ = (Complex.normSq T.det : ℂ) * M.det := by
            rw [show star T.det = conj T.det by rfl, Complex.mul_conj]
  have hp : 0 < Complex.normSq T.det * M.det.re := by
    rw [hdet] at hDif
    simpa [Complex.mul_re] using hDif
  by_contra hNo
  have hNonpos : M.det.re ≤ 0 := le_of_not_gt hNo
  have hFactNonneg : 0 ≤ Complex.normSq T.det :=
    Complex.normSq_nonneg _
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hFactNonneg hNonpos)) hp

#print axioms canonicalCompletedNativeRadialDslopeSampleMatrix_nine_det_eventually_re_pos

end
end CarrySelfAdjointOperator
