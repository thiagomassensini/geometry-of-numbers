import PhysicalPickNineSchurDetLaw
import Mathlib.Tactic

/-!
A normalized source-only interpretation of the ninth even sign.
The finite source's inverse-coupling energy is nonnegative because
the OLD H4 is positive definite, while its full new diagonal exceeds
that energy by the source-certified positive Schur residual.
No physical all-order metric or asymptotic decay assertion follows.
-/
namespace CarrySelfAdjointOperator
open CarryCriticalSource
open scoped Matrix
noncomputable section
set_option autoImplicit false

def nativeNineEvenCouplingEnergy : ℝ :=
  sourceMomentCoupling h 0 4 ⬝ᵥ
    ((sourceMomentMatrix h 0 4)⁻¹ *ᵥ sourceMomentCoupling h 0 4)

theorem nativeNineEvenCouplingEnergy_nonneg :
    0 ≤ nativeNineEvenCouplingEnergy := by
  have hA : (sourceMomentMatrix h 0 4).PosDef :=
    sourceMatrices_through_four_posDef (0 : Fin 2) 4 (by omega)
  exact hA.inv.posSemidef.dotProduct_mulVec_nonneg (sourceMomentCoupling h 0 4)

theorem nativeNineEvenSourceDiagonal_pos : 0 < h 8 := by
  have hs : 0 < h 8 - nativeNineEvenCouplingEnergy := by
    simpa [sourceMomentSchur, nativeNineEvenCouplingEnergy] using
      (fifth_even_pivot_pos : 0 < sourceMomentSchur h 0 4)
  linarith [nativeNineEvenCouplingEnergy_nonneg]

/-- The fraction of the ninth-even diagonal *spent* on old-even
couplings lies in the closed-open interval [0,1). This is
a source Hilbert angle-type fraction, not a new physical metric. -/
theorem nativeNineEvenNormalizedCoupling_range :
    0 ≤ nativeNineEvenCouplingEnergy / h 8 ∧
      nativeNineEvenCouplingEnergy / h 8 < 1 := by
  have hσ : 0 < h 8 - nativeNineEvenCouplingEnergy := by
    simpa [sourceMomentSchur, nativeNineEvenCouplingEnergy] using
      (fifth_even_pivot_pos : 0 < sourceMomentSchur h 0 4)
  exact ⟨div_nonneg nativeNineEvenCouplingEnergy_nonneg
     nativeNineEvenSourceDiagonal_pos.le,
    (div_lt_one nativeNineEvenSourceDiagonal_pos).mpr (sub_pos.mp hσ)⟩

/-- The source Schur fraction remaining after the full
four-dimensional inverse-coupled projection is strictly positive.
The normalization by h8 does not alter the source coefficients. -/
theorem nativeNineEvenNormalizedResidual_pos_le_one :
    0 < sourceMomentSchur h 0 4 / h 8 ∧
      sourceMomentSchur h 0 4 / h 8 ≤ 1 := by
  have hσ : 0 < h 8 - nativeNineEvenCouplingEnergy := by
    simpa [sourceMomentSchur, nativeNineEvenCouplingEnergy] using
      (fifth_even_pivot_pos : 0 < sourceMomentSchur h 0 4)
  have hrest : sourceMomentSchur h 0 4 =
      h 8 - nativeNineEvenCouplingEnergy := by
    rfl
  rw [hrest]
  constructor
  · exact div_pos hσ nativeNineEvenSourceDiagonal_pos
  · exact (div_le_one nativeNineEvenSourceDiagonal_pos).mpr
      (sub_le_self _ nativeNineEvenCouplingEnergy_nonneg)

theorem nativeNineEvenNormalizedPartition :
    sourceMomentSchur h 0 4 / h 8 +
      nativeNineEvenCouplingEnergy / h 8 = 1 := by
  have hn : h 8 ≠ 0 := nativeNineEvenSourceDiagonal_pos.ne'
  change (h 8 - nativeNineEvenCouplingEnergy) / h 8 +
    nativeNineEvenCouplingEnergy / h 8 = 1
  field_simp [hn]
  ring

#print axioms nativeNineEvenCouplingEnergy_nonneg
#print axioms nativeNineEvenNormalizedCoupling_range
#print axioms nativeNineEvenNormalizedResidual_pos_le_one
#print axioms nativeNineEvenNormalizedPartition

end
end CarrySelfAdjointOperator
