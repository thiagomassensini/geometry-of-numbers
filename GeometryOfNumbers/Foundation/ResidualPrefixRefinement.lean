import GeometryOfNumbers.Foundation.ResidualPrefixNormalization

/-!
# Structural refinement and conservation of formal prefix shares

The first coordinate is the LOWEST residual. Refinement appends a coordinate
at the deepest end; truncation removes that coordinate, not the first one.
The fiber is parametrized before any power identity is used. All structural
maps and inverse laws work at zero capacity as well.

Only after proving the fiber equivalence do we total the actual child shares
with a common denominator. Conservation follows for the existing canonical
counting normalization. Formal depth mass is then a name for that coherent
normalization, not a premise or a numerical/countably additive measure.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false

/-- Forget the highest residual, keeping the lowest ones in their original order. -/
def truncateResidualPrefix (b : Nat) : {depth : Nat} →
    ResidualPrefix b (depth + 1) → ResidualPrefix b depth
  | 0, _ => PUnit.unit
  | _ + 1, (residual, rest) => (residual, truncateResidualPrefix b rest)

/-- Add a new deepest residual, without changing any existing coordinate. -/
def extendResidualPrefix (b : Nat) : {depth : Nat} →
    ResidualPrefix b depth → Fin b → ResidualPrefix b (depth + 1)
  | 0, _, child => (child, PUnit.unit)
  | _ + 1, (residual, rest), child => (residual, extendResidualPrefix b rest child)

/-- Read the new highest residual, not the lowest coordinate of the tuple. -/
def topResidual (b : Nat) : {depth : Nat} → ResidualPrefix b (depth + 1) → Fin b
  | 0, (residual, _) => residual
  | _ + 1, (_, rest) => topResidual b rest

theorem truncateResidualPrefix_extend (b depth : Nat)
    (parent : ResidualPrefix b depth) (child : Fin b) :
    truncateResidualPrefix b (extendResidualPrefix b parent child) = parent := by
  induction depth with
  | zero => cases parent; rfl
  | succ depth ih => exact Prod.ext rfl (ih parent.2)

theorem topResidual_extend (b depth : Nat)
    (parent : ResidualPrefix b depth) (child : Fin b) :
    topResidual b (extendResidualPrefix b parent child) = child := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact ih parent.2

theorem extendResidualPrefix_truncate_top (b depth : Nat)
    (refined : ResidualPrefix b (depth + 1)) :
    extendResidualPrefix b (truncateResidualPrefix b refined) (topResidual b refined) =
      refined := by
  induction depth with
  | zero => rcases refined with ⟨residual, rest⟩; cases rest; rfl
  | succ depth ih => exact Prod.ext rfl (ih refined.2)

/-- This truncation agrees with extracting prefixes of the existing cycle tower.
The unresolved count is not required to be zero and is not discarded globally. -/
theorem truncateResidualPrefix_of_canonicalTower (b depth n : Nat) (hb : 0 < b) :
    truncateResidualPrefix b
      (residualPrefixOfBoundedTower b (emergentResidualTower b (depth + 1) n)
        (emergentResidualTower_bounded b (depth + 1) n hb)) =
    residualPrefixOfBoundedTower b (emergentResidualTower b depth n)
      (emergentResidualTower_bounded b depth n hb) := by
  induction depth generalizing n with
  | zero => rfl
  | succ depth ih => exact Prod.ext rfl (ih (completedCycleCount b n))

/-- No cardinality is built into the fiber: it is the actual preimage of truncation. -/
def ResidualPrefixRefinementFiber (b depth : Nat) (parent : ResidualPrefix b depth) :=
  { refined : ResidualPrefix b (depth + 1) // truncateResidualPrefix b refined = parent }

/-- A child label produces an actual member of the truncation fiber. -/
def residualPrefixRefinementChild (b depth : Nat) (parent : ResidualPrefix b depth)
    (child : Fin b) : ResidualPrefixRefinementFiber b depth parent :=
  ⟨extendResidualPrefix b parent child, truncateResidualPrefix_extend b depth parent child⟩

theorem residualPrefixRefinementChild_top (b depth : Nat)
    (parent : ResidualPrefix b depth) (child : Fin b) :
    topResidual b (residualPrefixRefinementChild b depth parent child).val = child :=
  topResidual_extend b depth parent child

theorem residualPrefixRefinementChild_recovers (b depth : Nat)
    (parent : ResidualPrefix b depth) (refined : ResidualPrefixRefinementFiber b depth parent) :
    residualPrefixRefinementChild b depth parent (topResidual b refined.val) = refined := by
  apply Subtype.ext
  have h := extendResidualPrefix_truncate_top b depth refined.val
  rw [refined.property] at h
  exact h

/-- The exact `b` refinements come from a concrete fiber equivalence, not powers. -/
def residualPrefixRefinementEquivFin (b depth : Nat) (parent : ResidualPrefix b depth) :
    { maps : (Fin b → ResidualPrefixRefinementFiber b depth parent) ×
        (ResidualPrefixRefinementFiber b depth parent → Fin b) //
      (∀ child, maps.2 (maps.1 child) = child) ∧
        (∀ refined, maps.1 (maps.2 refined) = refined) } :=
  ⟨(residualPrefixRefinementChild b depth parent, fun refined => topResidual b refined.val),
    residualPrefixRefinementChild_top b depth parent,
    residualPrefixRefinementChild_recovers b depth parent⟩

theorem residualPrefixRefinementChild_injective (b depth : Nat)
    (parent : ResidualPrefix b depth) :
    FaithfulRepresentation (residualPrefixRefinementChild b depth parent) := by
  intro left right heq
  exact (residualPrefixRefinementChild_top b depth parent left).symm.trans
    ((congrArg (fun refined => topResidual b refined.val) heq).trans
      (residualPrefixRefinementChild_top b depth parent right))

/-- Every refinement appears, and no child label appears twice. -/
theorem residualPrefixRefinement_fiber_cardinality (b depth : Nat)
    (parent : ResidualPrefix b depth) :
    FaithfulRepresentation (residualPrefixRefinementChild b depth parent) ∧
      ∀ refined : ResidualPrefixRefinementFiber b depth parent, ∃ child : Fin b,
        residualPrefixRefinementChild b depth parent child = refined :=
  ⟨residualPrefixRefinementChild_injective b depth parent,
    fun refined => ⟨topResidual b refined.val,
      residualPrefixRefinementChild_recovers b depth parent refined⟩⟩

private theorem addMul (a c b : Nat) : (a + c) * b = a * b + c * b := by
  rw [Nat.mul_comm (a + c) b, Nat.mul_add, Nat.mul_comm b a, Nat.mul_comm b c]

private theorem mulAssoc (a c b : Nat) : (a * c) * b = a * (c * b) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_add, ih]

/-- After constructing refinement, evaluation identifies the new coordinate's scale. -/
theorem residualPrefixValue_extend (b depth : Nat)
    (parent : ResidualPrefix b depth) (child : Fin b) :
    residualPrefixValue b (extendResidualPrefix b parent child) =
      residualPrefixValue b parent + child.val * b ^ depth := by
  induction depth with
  | zero =>
    change 0 * b + child.val = 0 + child.val * b ^ 0
    rw [Nat.zero_mul, Nat.pow_zero, Nat.mul_one]
  | succ depth ih =>
    change residualPrefixValue b (extendResidualPrefix b parent.2 child) * b + parent.1.val =
      (residualPrefixValue b parent.2 * b + parent.1.val) + child.val * b ^ (depth + 1)
    rw [ih parent.2, addMul, mulAssoc, Nat.pow_succ,
      Nat.add_right_comm (residualPrefixValue b parent.2 * b)
        (child.val * (b ^ depth * b)) parent.1.val]

/-- Total actual numerators indexed by the proved fiber, retaining their common
canonical denominator. The definition does NOT assert conservation. -/
def residualPrefixRefinementAggregateShare (b depth : Nat) (hb : 0 < b)
    (parent : ResidualPrefix b depth) : FormalCountingShare where
  numerator := finiteLabelTotal b (fun child =>
    (canonicalResidualPrefixCountingShare b (depth + 1) hb
      (residualPrefixRefinementChild b depth parent child).val).numerator)
  denominator := finiteLabelTotal (b ^ (depth + 1)) (fun _ => 1)
  denominator_positive := by
    rw [finiteLabelTotal_unit]
    exact Nat.pow_pos hb

/-- All actual child shares use exactly the aggregation denominator. -/
theorem residualPrefixRefinementAggregateShare_common_denominator
    (b depth : Nat) (hb : 0 < b) (parent : ResidualPrefix b depth) (child : Fin b) :
    (canonicalResidualPrefixCountingShare b (depth + 1) hb
      (residualPrefixRefinementChild b depth parent child).val).denominator =
    (residualPrefixRefinementAggregateShare b depth hb parent).denominator := rfl

/-- The numerator `b` is obtained by adding the shares of the exact fiber. -/
theorem residualPrefixRefinementAggregateShare_numerator
    (b depth : Nat) (hb : 0 < b) (parent : ResidualPrefix b depth) :
    (residualPrefixRefinementAggregateShare b depth hb parent).numerator = b :=
  finiteLabelTotal_unit b

/-- Conservation is a theorem about the aggregation of the actual fiber.
Power arithmetic is used only here, after the structural fiber construction. -/
theorem residualPrefix_refinement_conserves_share (b depth : Nat) (hb : 0 < b)
    (parent : ResidualPrefix b depth) :
    SameCountingShare (residualPrefixRefinementAggregateShare b depth hb parent)
      (canonicalResidualPrefixCountingShare b depth hb parent) := by
  change finiteLabelTotal b (fun _ => 1) * finiteLabelTotal (b ^ depth) (fun _ => 1) =
    1 * finiteLabelTotal (b ^ (depth + 1)) (fun _ => 1)
  rw [finiteLabelTotal_unit, finiteLabelTotal_unit, finiteLabelTotal_unit,
    Nat.one_mul, Nat.pow_succ, Nat.mul_comm b]

/-- Aggregate a specified finite number of equal formal shares without division. -/
def repeatCountingShare (count : Nat) (share : FormalCountingShare) : FormalCountingShare where
  numerator := finiteLabelTotal count (fun _ => share.numerator)
  denominator := share.denominator
  denominator_positive := share.denominator_positive

/-- At zero capacity an empty refinement cannot conserve the unit of the empty
prefix. This is why a coherent depth-mass family requires positive capacity. -/
theorem zeroRefinement_cannot_conserve_unit (share : FormalCountingShare) :
    ¬ SameCountingShare (repeatCountingShare 0 share) ⟨1, 1, Nat.zero_lt_one⟩ := by
  intro heq
  change 0 * 1 = 1 * share.denominator at heq
  rw [Nat.zero_mul, Nat.one_mul] at heq
  have hpositive := share.denominator_positive
  rw [heq.symm] at hpositive
  exact Nat.not_lt_zero 0 hpositive

/-- Depth mass is only the already constructed canonical share at a representative.
The representative does not privilege a state: independence is proved below. -/
def canonicalResidualDepthMass (b depth : Nat) (hb : 0 < b) : FormalCountingShare :=
  canonicalResidualPrefixCountingShare b depth hb
    (residualPrefixDecode b depth hb ⟨0, Nat.pow_pos hb⟩)

/-- Identifies the new terminology with the existing share, even as a presentation. -/
theorem canonicalResidualPrefixCountingShare_eq_depthMass (b depth : Nat) (hb : 0 < b)
    (resolved : ResidualPrefix b depth) :
    canonicalResidualPrefixCountingShare b depth hb resolved =
      canonicalResidualDepthMass b depth hb := rfl

/-- The computed aggregation is the repetition of the common next-depth mass. -/
theorem residualPrefixRefinementAggregateShare_eq_repeat_depthMass
    (b depth : Nat) (hb : 0 < b) (parent : ResidualPrefix b depth) :
    residualPrefixRefinementAggregateShare b depth hb parent =
      repeatCountingShare b (canonicalResidualDepthMass b (depth + 1) hb) := rfl

/-- The empty prefix carries the whole formal unit, without normalization by division. -/
theorem canonicalResidualDepthMass_zero (b : Nat) (hb : 0 < b) :
    canonicalResidualDepthMass b 0 hb = ⟨1, 1, Nat.zero_lt_one⟩ := rfl

/-- Mass conservation follows from fiber conservation, not from a new mass axiom. -/
theorem canonicalResidualDepthMass_refinement (b depth : Nat) (hb : 0 < b) :
    SameCountingShare (repeatCountingShare b (canonicalResidualDepthMass b (depth + 1) hb))
      (canonicalResidualDepthMass b depth hb) := by
  have h := residualPrefix_refinement_conserves_share b depth hb
    (residualPrefixDecode b depth hb ⟨0, Nat.pow_pos hb⟩)
  rw [residualPrefixRefinementAggregateShare_eq_repeat_depthMass,
    canonicalResidualPrefixCountingShare_eq_depthMass] at h
  exact h

/-- This is an identification after refinement, not the definition of depth mass. -/
theorem canonicalResidualDepthMass_eq_unit_over_capacity
    (b depth : Nat) (hb : 0 < b) :
    (canonicalResidualDepthMass b depth hb).numerator = 1 ∧
      (canonicalResidualDepthMass b depth hb).denominator = b ^ depth :=
  canonicalResidualPrefixCountingShare_eq_unit_over_capacity b depth hb _

end GeometryOfNumbers.Foundation
