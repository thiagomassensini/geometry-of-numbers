import GeometryOfNumbers.Analysis.CarryMaterialComplexAnalyticIdentity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Physical C2 chiral multiplier gate

Cauchy-Pick PSD is proved **conditional on** PSD of the genuine source
multiplier defect matrix. The condition is NOT made true by definition:
the defect is built from the exact C2 Hilbert vector companion, not from
a target matrix. No all-order sign theorem is asserted.
-/

namespace GeometryOfNumbers.Analysis
open scoped InnerProductSpace ComplexConjugate ComplexOrder Matrix MatrixOrder
noncomputable section
set_option autoImplicit false

def carryMaterialComplexSourceDefectMatrix (N : ℕ) (z : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    (Complex.I / (z j - conj (z i))) *
      (1 - conj (carryMaterialComplexChiralQuotient (z i)) *
        carryMaterialComplexChiralQuotient (z j))

def carryMaterialComplexSourceGaugeMatrix (N : ℕ) (z : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => carryMaterialComplexChiralGauge (z i))

def carryMaterialComplexSourcePickMatrix (N : ℕ) (z : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => carryMaterialComplexPickKernel (z i) (z j)

/-- The complete physical Pick sample is an EXACT diagonal congruence of
the source Hermite--Biehler multiplier defect. This neither changes the
metric nor discards either of the original material channels. -/
theorem carryMaterialComplexSourcePickMatrix_eq_gaugedDefect
    (N : ℕ) (z : Fin N → ℂ)
    (hUpper : ∀ i : Fin N, 0 < (z i).im)
    (hF : ∀ i : Fin N, carryMaterialComplexValueReadout (z i) ≠ 0)
    (hHB : ∀ i : Fin N, carryMaterialComplexPositiveHB (z i) ≠ 0) :
    carryMaterialComplexSourcePickMatrix N z =
      (carryMaterialComplexSourceGaugeMatrix N z)ᴴ *
        carryMaterialComplexSourceDefectMatrix N z *
          carryMaterialComplexSourceGaugeMatrix N z := by
  ext i j
  have hsep := carryMaterialComplexPick_separated_of_positive_im
    (z i) (z j) (hUpper i) (hUpper j)
  change carryMaterialComplexPickKernel (z i) (z j) = _
  rw [carryMaterialComplexPickKernel_eq_sourceHermiteBiehler
      (z i) (z j) (hF i) (hF j) (hHB i) (hHB j) hsep]
  simp [carryMaterialComplexSourceGaugeMatrix,
    carryMaterialComplexSourceDefectMatrix, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, RCLike.star_def]
  ring

/-- The conditional positivity transport uses an ACTUAL source matrix
congruence. It is not a proof that the defect itself is PSD. -/
theorem carryMaterialComplexSourcePickMatrix_posSemidef_of_sourceDefect
    (N : ℕ) (z : Fin N → ℂ)
    (hUpper : ∀ i : Fin N, 0 < (z i).im)
    (hF : ∀ i : Fin N, carryMaterialComplexValueReadout (z i) ≠ 0)
    (hHB : ∀ i : Fin N, carryMaterialComplexPositiveHB (z i) ≠ 0)
    (hDef : (carryMaterialComplexSourceDefectMatrix N z).PosSemidef) :
    (carryMaterialComplexSourcePickMatrix N z).PosSemidef := by
  rw [carryMaterialComplexSourcePickMatrix_eq_gaugedDefect N z hUpper hF hHB]
  exact hDef.conjTranspose_mul_mul_same _



/-- The physical C2 Pick PSD test is EQUIVALENT to the source multiplier
defect PSD test on every finite upper-half-plane sample with nonzero
regularity coordinates. The source gauge is invertible because it comes
from the original nonzero physical HB and completion factors. -/
theorem carryMaterialComplexSourcePickMatrix_posSemidef_iff_sourceDefect
    (N : ℕ) (z : Fin N → ℂ)
    (hUpper : ∀ i : Fin N, 0 < (z i).im)
    (hF : ∀ i : Fin N, carryMaterialComplexValueReadout (z i) ≠ 0)
    (hHB : ∀ i : Fin N, carryMaterialComplexPositiveHB (z i) ≠ 0) :
    (carryMaterialComplexSourcePickMatrix N z).PosSemidef ↔
      (carryMaterialComplexSourceDefectMatrix N z).PosSemidef := by
  have hUnit : IsUnit (carryMaterialComplexSourceGaugeMatrix N z) := by
    rw [carryMaterialComplexSourceGaugeMatrix, Matrix.isUnit_diagonal,
      Pi.isUnit_iff]
    intro i
    apply isUnit_iff_ne_zero.mpr
    unfold carryMaterialComplexChiralGauge
    exact div_ne_zero (hHB i) (mul_ne_zero (by norm_num) (hF i))
  rw [carryMaterialComplexSourcePickMatrix_eq_gaugedDefect N z hUpper hF hHB]
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.IsUnit.posSemidef_star_left_conjugate_iff
      (U := carryMaterialComplexSourceGaugeMatrix N z)
      (x := carryMaterialComplexSourceDefectMatrix N z) hUnit)

end
end GeometryOfNumbers.Analysis

#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexSourcePickMatrix_eq_gaugedDefect
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexSourcePickMatrix_posSemidef_of_sourceDefect

#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexSourcePickMatrix_posSemidef_iff_sourceDefect
