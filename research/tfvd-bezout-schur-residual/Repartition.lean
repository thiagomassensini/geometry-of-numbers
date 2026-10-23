import LiteralTfvd
import KernelBudget

namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

theorem mixed_four_terms {R : Type*} [CommRing R]
    (H T P Q : ℕ → R) (b : Bool) :
    mixedSourceKernel (H+T) (P+Q) b =
      mixedSourceKernel H P b + mixedSourceKernel H Q b +
      mixedSourceKernel T P b + mixedSourceKernel T Q b := by
  rw [mixedSourceKernel_add_left, mixedSourceKernel_add_right, mixedSourceKernel_add_right]
  abel

/-- Exact transfer of a boundary between head and tail in each independent slot.
No source, coefficient, moment, or total kernel is altered by this identity. -/
theorem boundary_repartition {R : Type*} [CommRing R]
    (H T P Q U V : ℕ → R) (b : Bool) :
    mixedSourceKernel H P b + mixedSourceKernel H Q b +
      mixedSourceKernel T P b + mixedSourceKernel T Q b =
    mixedSourceKernel (H+U) (P+V) b + mixedSourceKernel (H+U) (Q-V) b +
      mixedSourceKernel (T-U) (P+V) b + mixedSourceKernel (T-U) (Q-V) b := by
  rw [← mixed_four_terms, ← mixed_four_terms]
  congr 1 <;> (funext n; simp only [Pi.add_apply, Pi.sub_apply]; ring)

def coefficientPair (c d : ℕ → ℂ) (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) : ℂ :=
  complexPair (coefficientBlock (mixedSourceKernel c d b) r)
    (fun i => (x i : ℂ)) (fun j => (y j : ℂ))

theorem coefficientPair_four_terms (H T P Q : ℕ → ℂ) (b : Bool)
    (r : ℕ) (x y : Fin r → ℝ) :
    coefficientPair (H+T) (P+Q) b r x y =
      coefficientPair H P b r x y + coefficientPair H Q b r x y +
      coefficientPair T P b r x y + coefficientPair T Q b r x y := by
  unfold coefficientPair
  rw [mixed_four_terms]
  simp only [coefficientBlock_add, complexPair_add]

theorem coefficientPair_boundary_repartition (H T P Q U V : ℕ → ℂ) (b : Bool)
    (r : ℕ) (x y : Fin r → ℝ) :
    coefficientPair H P b r x y + coefficientPair H Q b r x y +
      coefficientPair T P b r x y + coefficientPair T Q b r x y =
    coefficientPair (H+U) (P+V) b r x y + coefficientPair (H+U) (Q-V) b r x y +
      coefficientPair (T-U) (P+V) b r x y + coefficientPair (T-U) (Q-V) b r x y := by
  rw [← coefficientPair_four_terms, ← coefficientPair_four_terms]
  congr 1 <;> (funext n; simp only [Pi.add_apply, Pi.sub_apply]; ring)

/-- The original residual, after exact boundary repartition and with all four
ordered crossings. The boundary arguments are not chosen from a desired sign. -/
theorem native_residual_repartition (M P : ℕ) (U V : ℕ → ℂ) (b : Bool) (n : ℕ)
    (hA : IsUnit (CarrySelfAdjointOperator.sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) n
    coefficientPair (literalHead M+U) (literalHead P+V) b (n+1) z z +
      coefficientPair (literalHead M+U) (literalTail P-V) b (n+1) z z +
      coefficientPair (literalTail M-U) (literalHead P+V) b (n+1) z z +
      coefficientPair (literalTail M-U) (literalTail P-V) b (n+1) z z =
      (nativeC 0*CarrySelfAdjointOperator.nativeSourceSchurRemainder (if b then 1 else 0) n : ℝ) := by
  dsimp only
  rw [← coefficientPair_boundary_repartition]
  exact native_residual_literal_four_terms M P b n hA

end
end CarrySourceBezout
