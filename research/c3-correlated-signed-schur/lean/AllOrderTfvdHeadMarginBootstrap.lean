import TfvdBoundaryLaw
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur
import Mathlib.Tactic

/-!
# ALL-ORDER source-first Schur bootstrap by TFVD head/tail compensation

This is a *conditional structural theorem*, never an RH assumption.
It combines the original source's algebraic last-coefficient law (GoN #316),
the exact source head+tail expansion (GoN #70/#316), and the native
all-order Schur criterion (CSA NativeSourceAllOrderSchur).

The hypothesis is one family of EXPLICIT coefficient/head/tail inequalities
at each order and in each parity; it does not import any positive
zero-supported measure or assume a Hankel matrix positive.

No claim that the all-order head margins have been proved is made here.
-/

namespace CarryWheelNativeSignedGate

open CarrySourceBezout CarrySelfAdjointOperator
open scoped BigOperators Matrix

noncomputable section

/-- The original completion has a strictly positive central coefficient. -/
theorem nativeC0_pos_geometric :
    0 < nativeC 0 := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third

/-- A source-first *sufficient* obligation on the actual TFVD head and
tail at every order and both parities, with no reference to zeros.

Crucially, the old prefix is represented by the exact SCHUR expression
with the one NEW characteristic coefficient set to zero, so the required
condition is an explicit head margin; no positivity is hidden in a
replacement Gram or in a presumed spectrum. -/
def HasNativeAllOrderTfvdHeadMargins : Prop :=
  ∀ (n : ℕ) (b : Bool), ∃ (M : ℕ) (ε : ℝ),
    0 ≤ ε ∧
      |(literalTail M (sourceBoundaryCoefficientIndex n b)).re| ≤ ε ∧
      (sourceSchur
        (sourceCoefficientZero nativeC (sourceBoundaryCoefficientIndex n b))
          b n -
          (sourceBoundaryCoefficientIndex n b : ℝ)*nativeC 0*
            (literalHead M (sourceBoundaryCoefficientIndex n b)).re) >
        (sourceBoundaryCoefficientIndex n b : ℝ)*nativeC 0*ε

/-- All-order physical head margin implies every original Bézout
Schur complement is strictly positive. The tail is not dropped;
the sign depends on an EXPLICIT excess over its absolute bound. -/
theorem nativeSourceSchur_pos_of_allOrderTfvdHeadMargins
    (hmargins : HasNativeAllOrderTfvdHeadMargins)
    (n : ℕ) (b : Bool) :
    0 < sourceSchur nativeC b n := by
  obtain ⟨M, ε, hε, htail, hhead⟩ := hmargins n b
  have hsplit := nativeC_coefficient_eq_literal_head_tail
    M (sourceBoundaryCoefficientIndex n b)
  have hupdate := nativeSource_lastCoefficient_threshold n b
  rw [hsplit] at hupdate
  have hm : 0 < (sourceBoundaryCoefficientIndex n b : ℝ) := by
    cases b <;> simp [sourceBoundaryCoefficientIndex] <;> positivity
  have hf : 0 ≤ (sourceBoundaryCoefficientIndex n b : ℝ) * nativeC 0 :=
    (mul_pos hm nativeC0_pos_geometric).le
  have htailLe := (abs_le.mp htail).2
  have htailMul := mul_le_mul_of_nonneg_left htailLe hf
  nlinarith

/-- All orders, both sectors: strict PosDef of the ORIGINAL canonical
completed-native moment Hankel matrices. This is a theorem reducing the
all-order analytic task to genuine TFVD head/tail margins, NOT a proof
that those margins hold. -/
theorem nativeCanonicalAllOrders_posDef_of_tfvdHeadMargins
    (hmargins : HasNativeAllOrderTfvdHeadMargins)
    (b : Bool) :
    ∀ n : ℕ,
      (sourceMomentMatrix nativeH (if b then 1 else 0) n).PosDef := by
  intro n
  induction n with
  | zero =>
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
      (sourceMomentMatrix_isHermitian nativeH (if b then 1 else 0) 0)
    intro x hx
    exact (hx (Subsingleton.elim _ _)).elim
  | succ n ih =>
    apply (sourceMomentMatrix_succ_posDef_iff nativeH
      (if b then 1 else 0) n ih).mpr
    have hA : IsUnit
        (sourceMomentMatrix nativeH (if b then 1 else 0) n) := ih.isUnit
    have hscaled := sourceSchur_eq_scaled nativeC nativeH
      (ne_of_gt nativeC0_pos_geometric)
      native_source_recurrence b n hA
    have hschur := nativeSourceSchur_pos_of_allOrderTfvdHeadMargins
      hmargins n b
    rw [hscaled] at hschur
    have hfactor : 0 < (nativeC 0)^2 :=
      sq_pos_of_pos nativeC0_pos_geometric
    exact (mul_pos_iff_of_pos_left hfactor).mp hschur

/-- The all-order TFVD head-margin condition also supplies the already
existing ORIGINAL finite boundary energy positivity in every even
dimension. This is exactly the physical carrier, not a rebranded
abstract Hankel Gram. -/
theorem nativeBoundary_all_orders_strictly_positive_of_tfvdHeadMargins
    (hmargins : HasNativeAllOrderTfvdHeadMargins) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x := by
  apply nativeSourceBoundary_all_pos_iff_sourceSchur.mpr
  intro n
  have hEven := nativeSourceSchurRemainder_eq 0 n
  have hOdd := nativeSourceSchurRemainder_eq 1 n
  have hsEven :=
    (sourceMomentMatrix_all_posDef_iff_schur nativeH 0).mp
      (nativeCanonicalAllOrders_posDef_of_tfvdHeadMargins hmargins false) n
  have hsOdd :=
    (sourceMomentMatrix_all_posDef_iff_schur nativeH 1).mp
      (nativeCanonicalAllOrders_posDef_of_tfvdHeadMargins hmargins true) n
  constructor
  · rw [hEven]
    exact mul_pos nativeC0_pos_geometric hsEven
  · rw [hOdd]
    exact mul_pos nativeC0_pos_geometric hsOdd

end
end CarryWheelNativeSignedGate
