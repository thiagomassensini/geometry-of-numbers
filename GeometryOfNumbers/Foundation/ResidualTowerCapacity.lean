import GeometryOfNumbers.Foundation.EmergentResidualTower

/-!
# Exact capacity of the resolved residual prefix

This layer counts only the resolved prefix of the previously constructed tower,
not its unbounded tail. A prefix consists of one bounded coordinate per level.
Its value is the existing tower reconstruction with a zero tail.

The inverse encoding uses the existing cycle-generated tower, not division or
modulo. The two inverse laws certify the exact capacity `b ^ depth`.
`Init` has no Mathlib `Equiv` or cardinality API; the equivalence is packaged
as the explicit maps and their proved inverse laws. No measure is introduced.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false

/-- Only the resolved coordinates; the first `Fin b` is the lowest residual. -/
def ResidualPrefix (b : Nat) : Nat → Type
  | 0 => PUnit
  | depth + 1 => Fin b × ResidualPrefix b depth

/-- Insert the prefix into the existing tower with no unresolved tail. -/
def residualPrefixTower (b : Nat) : {depth : Nat} →
    ResidualPrefix b depth → ResidualTowerCoordinates depth
  | 0, _ => (0 : Nat)
  | _ + 1, (residual, rest) => (residual.val, residualPrefixTower b rest)

/-- The value is literally the existing tower value, not a new numeral evaluator. -/
def residualPrefixValue (b : Nat) {depth : Nat} (resolved : ResidualPrefix b depth) : Nat :=
  residualTowerValue b (residualPrefixTower b resolved)

/-- Typed prefix coordinates give precisely the existing tower bounds. -/
theorem residualPrefixTower_bounded (b depth : Nat) (resolved : ResidualPrefix b depth) :
    BoundedResidualTower b (residualPrefixTower b resolved) := by
  induction depth with
  | zero => exact True.intro
  | succ depth ih =>
    rcases resolved with ⟨residual, rest⟩
    exact ⟨residual.isLt, ih rest⟩

/-- Embedding a resolved prefix does not silently add a tail. -/
theorem residualPrefixTower_tail_eq_zero (b depth : Nat) (resolved : ResidualPrefix b depth) :
    residualTowerTail (residualPrefixTower b resolved) = 0 := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact ih resolved.2

/-- Every bounded prefix lies below the accumulated reconstruction scale.
This even holds for zero capacity, where positive-depth prefixes are empty. -/
theorem residualPrefix_value_lt_pow (b depth : Nat) (resolved : ResidualPrefix b depth) :
    residualPrefixValue b resolved < b ^ depth := by
  induction depth with
  | zero =>
    change 0 < b ^ 0
    rw [Nat.pow_zero]
    exact Nat.zero_lt_one
  | succ depth ih =>
    rcases resolved with ⟨residual, rest⟩
    change residualPrefixValue b rest * b + residual.val < b ^ (depth + 1)
    rw [Nat.pow_succ]
    have hstep : residualPrefixValue b rest * b + residual.val <
        (residualPrefixValue b rest + 1) * b := by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left residual.isLt _
    exact Nat.lt_of_lt_of_le hstep
      (Nat.mul_le_mul_right b (Nat.succ_le_of_lt (ih rest)))

/-- A count below the prefix capacity has no unresolved tail at that depth.
This follows from reconstruction and order, without division. -/
theorem residualTower_tail_eq_zero_of_lt_pow (b depth n : Nat) (hb : 0 < b)
    (hn : n < b ^ depth) :
    residualTowerTail (emergentResidualTower b depth n) = 0 := by
  by_cases hz : residualTowerTail (emergentResidualTower b depth n) = 0
  · exact hz
  · have hpos := Nat.pos_of_ne_zero hz
    have hle : b ^ depth ≤ n := by
      rw [emergentResidualTower_expansion b depth n hb]
      exact Nat.le_trans (Nat.le_mul_of_pos_left (b ^ depth) hpos)
        (Nat.le_add_left _ _)
    exact False.elim (Nat.not_lt_of_ge hle hn)

/-- Forget only the tail of a bounded tower, keeping its actual residuals. -/
def residualPrefixOfBoundedTower (b : Nat) : {depth : Nat} →
    (coordinates : ResidualTowerCoordinates depth) →
    BoundedResidualTower b coordinates → ResidualPrefix b depth
  | 0, _, _ => PUnit.unit
  | _ + 1, (residual, rest), hbound =>
      (⟨residual, hbound.1⟩, residualPrefixOfBoundedTower b rest hbound.2)

private theorem prefixTower_ofBoundedTower (b depth : Nat)
    (coordinates : ResidualTowerCoordinates depth)
    (hbound : BoundedResidualTower b coordinates)
    (htail : residualTowerTail coordinates = 0) :
    residualPrefixTower b (residualPrefixOfBoundedTower b coordinates hbound) =
      coordinates := by
  induction depth with
  | zero => exact htail.symm
  | succ depth ih =>
    rcases coordinates with ⟨residual, rest⟩
    exact Prod.ext rfl (ih rest hbound.2 htail)

/-- The typed prefix embedding itself preserves all resolved information. -/
theorem residualPrefixTower_injective (b depth : Nat) :
    FaithfulRepresentation (residualPrefixTower b (depth := depth)) := by
  induction depth with
  | zero =>
    intro left right _
    cases left
    cases right
    rfl
  | succ depth ih =>
    intro left right heq
    exact Prod.ext (Fin.ext (congrArg Prod.fst heq))
      (ih (congrArg Prod.snd heq))

/-- Encode by the existing reconstruction and the proved strict bound. -/
def residualPrefixEncode (b depth : Nat) (resolved : ResidualPrefix b depth) :
    Fin (b ^ depth) :=
  ⟨residualPrefixValue b resolved, residualPrefix_value_lt_pow b depth resolved⟩

/-- Decode through the canonical tower and retain its resolved prefix. -/
def residualPrefixDecode (b depth : Nat) (hb : 0 < b) (n : Fin (b ^ depth)) :
    ResidualPrefix b depth :=
  residualPrefixOfBoundedTower b (emergentResidualTower b depth n.val)
    (emergentResidualTower_bounded b depth n.val hb)

/-- Decoding has exactly the provenance of the existing zero-tail tower. -/
theorem residualPrefixDecode_toTower (b depth : Nat) (hb : 0 < b)
    (n : Fin (b ^ depth)) :
    residualPrefixTower b (residualPrefixDecode b depth hb n) =
      emergentResidualTower b depth n.val :=
  prefixTower_ofBoundedTower b depth _ (emergentResidualTower_bounded b depth n.val hb)
    (residualTower_tail_eq_zero_of_lt_pow b depth n.val hb n.isLt)

/-- Reconstruction proves the first inverse law. -/
theorem residualPrefix_encode_decode (b depth : Nat) (hb : 0 < b)
    (n : Fin (b ^ depth)) :
    residualPrefixEncode b depth (residualPrefixDecode b depth hb n) = n := by
  apply Fin.ext
  change residualTowerValue b (residualPrefixTower b (residualPrefixDecode b depth hb n)) = n.val
  rw [residualPrefixDecode_toTower]
  exact emergentResidualTower_value b depth n.val hb

/-- Tower uniqueness and the faithful embedding prove the second inverse law. -/
theorem residualPrefix_decode_encode (b depth : Nat) (hb : 0 < b)
    (resolved : ResidualPrefix b depth) :
    residualPrefixDecode b depth hb (residualPrefixEncode b depth resolved) = resolved := by
  apply residualPrefixTower_injective b depth
  have hcanonical := residualTower_eq_canonical b depth (residualPrefixValue b resolved) hb
    (residualPrefixTower b resolved) (residualPrefixTower_bounded b depth resolved) rfl
  exact (residualPrefixDecode_toTower b depth hb (residualPrefixEncode b depth resolved)).trans
    hcanonical.symm

/-- Explicit equivalence data, without introducing a Mathlib dependency. -/
def residualPrefixEquivFin (b depth : Nat) (hb : 0 < b) :
    { maps : (ResidualPrefix b depth → Fin (b ^ depth)) ×
        (Fin (b ^ depth) → ResidualPrefix b depth) //
      (∀ resolved, maps.2 (maps.1 resolved) = resolved) ∧
        (∀ n, maps.1 (maps.2 n) = n) } :=
  ⟨(residualPrefixEncode b depth, residualPrefixDecode b depth hb),
    residualPrefix_decode_encode b depth hb, residualPrefix_encode_decode b depth hb⟩

/-- Exact cardinality certified by a faithful, onto encoding in `Fin (b^depth)`,
not by defining a desired cardinality or counting the unbounded whole tower. -/
theorem residualPrefix_cardinality (b depth : Nat) (hb : 0 < b) :
    FaithfulRepresentation (residualPrefixEncode b depth) ∧
      ∀ n : Fin (b ^ depth), ∃ resolved : ResidualPrefix b depth,
        residualPrefixEncode b depth resolved = n := by
  constructor
  · intro left right heq
    exact (residualPrefix_decode_encode b depth hb left).symm.trans
      ((congrArg (residualPrefixDecode b depth hb) heq).trans
        (residualPrefix_decode_encode b depth hb right))
  · intro n
    exact ⟨residualPrefixDecode b depth hb n, residualPrefix_encode_decode b depth hb n⟩

/-- Every finite code has exactly one prefix, with its witness supplied explicitly. -/
theorem existsUnique_residualPrefix_for_fin (b depth : Nat) (hb : 0 < b)
    (n : Fin (b ^ depth)) :
    ∃ resolved : ResidualPrefix b depth, residualPrefixEncode b depth resolved = n ∧
      ∀ other, residualPrefixEncode b depth other = n → other = resolved := by
  refine ⟨residualPrefixDecode b depth hb n, residualPrefix_encode_decode b depth hb n, ?_⟩
  intro other heq
  exact (residualPrefix_cardinality b depth hb).1
    (heq.trans (residualPrefix_encode_decode b depth hb n).symm)

end GeometryOfNumbers.Foundation
