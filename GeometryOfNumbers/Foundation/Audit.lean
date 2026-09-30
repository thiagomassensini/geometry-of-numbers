import GeometryOfNumbers
import Lean

/-! Zone A audit: every listed theorem must have an empty axiom footprint. -/

open Lean Elab Command

/-- Fail elaboration if a foundational theorem acquires any axiom dependency. -/
elab "#assert_no_axioms " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms decl
  unless axioms.isEmpty do
    throwError "Zone A violation: {decl} depends on {axioms}"

namespace GeometryOfNumbers.Foundation

#assert_no_axioms sameLocal_forces_extension_difference
#assert_no_axioms faithfulRepresentation_comp
#assert_no_axioms localRecurrence_forces_extension_difference
#assert_no_axioms positiveLocalReturn_implies_periodic_readout
#assert_no_axioms boundedLeastOrAbsent
#assert_no_axioms finiteCodeCollision
#assert_no_axioms unitTrajectory_forces_localRecurrence
#assert_no_axioms autonomousLocalDynamics_has_positiveReturn
#assert_no_axioms emergentLocalCapacity_unique
#assert_no_axioms emergentLocalCapacity_gt_one_of_first_step_changes
#assert_no_axioms exists_emergentLocalCapacity
#assert_no_axioms existsUnique_emergentLocalCapacity
#assert_no_axioms exists_emergentLocalCapacity_gt_one
#assert_no_axioms cycleCoordinatesRec_spec
#assert_no_axioms cycleDecomposition_unique
#assert_no_axioms cycleDecomposition_eq_recursive
#assert_no_axioms cycle_step_inside
#assert_no_axioms cycle_step_at_boundary
#assert_no_axioms cycle_step_dichotomy
#assert_no_axioms firstSaturation_coordinates
#assert_no_axioms cycleResidual_controls_localReadout
#assert_no_axioms localReturn_iff_cycleResidual_zero
#assert_no_axioms cycle_reset_forces_extension_difference
#assert_no_axioms emergentResidualTower_bounded
#assert_no_axioms emergentResidualTower_value
#assert_no_axioms residualTower_unique
#assert_no_axioms residualTower_eq_canonical
#assert_no_axioms residualTowerValue_eq_prefix_add_scaled_tail
#assert_no_axioms emergentResidualTower_expansion
#assert_no_axioms emergentResidualTower_truncate
#assert_no_axioms emergentResidualTower_first_residual_preserves_observation
#assert_no_axioms residualPrefixTower_bounded
#assert_no_axioms residualPrefixTower_tail_eq_zero
#assert_no_axioms residualPrefix_value_lt_pow
#assert_no_axioms residualTower_tail_eq_zero_of_lt_pow
#assert_no_axioms residualPrefixTower_injective
#assert_no_axioms residualPrefixDecode_toTower
#assert_no_axioms residualPrefix_encode_decode
#assert_no_axioms residualPrefix_decode_encode
#assert_no_axioms residualPrefixEquivFin
#assert_no_axioms residualPrefix_cardinality
#assert_no_axioms existsUnique_residualPrefix_for_fin
#assert_no_axioms finiteLabelTransposition
#assert_no_axioms residualPrefixRelabeling
#assert_no_axioms finiteLabel_relabelingInvariant_iff_constant
#assert_no_axioms residualPrefix_relabelingInvariant_iff_constant
#assert_no_axioms finiteLabelTotal_of_equal
#assert_no_axioms finiteLabelTotal_unit
#assert_no_axioms finiteCapacity_does_not_force_uniformity
#assert_no_axioms finiteLabel_normalization_forces_unitShare
#assert_no_axioms finiteLabel_normalizedShare_unique
#assert_no_axioms canonicalResidualPrefixCountingShare
#assert_no_axioms canonicalResidualPrefixCountingShare_invariant
#assert_no_axioms canonicalResidualPrefixCountingShare_eq_unit_over_capacity
#assert_no_axioms residualPrefix_normalizedShare_unique
#assert_no_axioms truncateResidualPrefix
#assert_no_axioms extendResidualPrefix
#assert_no_axioms topResidual
#assert_no_axioms ResidualPrefixRefinementFiber
#assert_no_axioms residualPrefixRefinementChild
#assert_no_axioms residualPrefixRefinementEquivFin
#assert_no_axioms residualPrefixRefinementAggregateShare
#assert_no_axioms repeatCountingShare
#assert_no_axioms zeroRefinement_cannot_conserve_unit
#assert_no_axioms canonicalResidualDepthMass
#assert_no_axioms truncateResidualPrefix_extend
#assert_no_axioms topResidual_extend
#assert_no_axioms extendResidualPrefix_truncate_top
#assert_no_axioms truncateResidualPrefix_of_canonicalTower
#assert_no_axioms residualPrefixRefinementChild_top
#assert_no_axioms residualPrefixRefinementChild_recovers
#assert_no_axioms residualPrefixRefinementChild_injective
#assert_no_axioms residualPrefixRefinement_fiber_cardinality
#assert_no_axioms residualPrefixValue_extend
#assert_no_axioms residualPrefixRefinementAggregateShare_common_denominator
#assert_no_axioms residualPrefixRefinementAggregateShare_numerator
#assert_no_axioms residualPrefix_refinement_conserves_share
#assert_no_axioms canonicalResidualPrefixCountingShare_eq_depthMass
#assert_no_axioms residualPrefixRefinementAggregateShare_eq_repeat_depthMass
#assert_no_axioms canonicalResidualDepthMass_zero
#assert_no_axioms canonicalResidualDepthMass_refinement
#assert_no_axioms canonicalResidualDepthMass_eq_unit_over_capacity
#assert_no_axioms quadraticExponentEquation_iff_half
#assert_no_axioms quadraticCarryCompatibleAt_iff_half
#assert_no_axioms quadratic_carry_exponent_iff_half
#assert_no_axioms quadraticCarryCompatibleAt_zero

#print axioms sameLocal_forces_extension_difference
#print axioms faithfulRepresentation_comp
#print axioms localRecurrence_forces_extension_difference
#print axioms positiveLocalReturn_implies_periodic_readout
#print axioms boundedLeastOrAbsent
#print axioms finiteCodeCollision
#print axioms unitTrajectory_forces_localRecurrence
#print axioms autonomousLocalDynamics_has_positiveReturn
#print axioms emergentLocalCapacity_unique
#print axioms emergentLocalCapacity_gt_one_of_first_step_changes
#print axioms exists_emergentLocalCapacity
#print axioms existsUnique_emergentLocalCapacity
#print axioms exists_emergentLocalCapacity_gt_one
#print axioms cycleCoordinatesRec_spec
#print axioms cycleDecomposition_unique
#print axioms cycleDecomposition_eq_recursive
#print axioms cycle_step_inside
#print axioms cycle_step_at_boundary
#print axioms cycle_step_dichotomy
#print axioms firstSaturation_coordinates
#print axioms cycleResidual_controls_localReadout
#print axioms localReturn_iff_cycleResidual_zero
#print axioms cycle_reset_forces_extension_difference
#print axioms emergentResidualTower_bounded
#print axioms emergentResidualTower_value
#print axioms residualTower_unique
#print axioms residualTower_eq_canonical
#print axioms residualTowerValue_eq_prefix_add_scaled_tail
#print axioms emergentResidualTower_expansion
#print axioms emergentResidualTower_truncate
#print axioms emergentResidualTower_first_residual_preserves_observation
#print axioms residualPrefixTower_bounded
#print axioms residualPrefixTower_tail_eq_zero
#print axioms residualPrefix_value_lt_pow
#print axioms residualTower_tail_eq_zero_of_lt_pow
#print axioms residualPrefixTower_injective
#print axioms residualPrefixDecode_toTower
#print axioms residualPrefix_encode_decode
#print axioms residualPrefix_decode_encode
#print axioms residualPrefixEquivFin
#print axioms residualPrefix_cardinality
#print axioms existsUnique_residualPrefix_for_fin
#print axioms finiteLabelTransposition
#print axioms residualPrefixRelabeling
#print axioms finiteLabel_relabelingInvariant_iff_constant
#print axioms residualPrefix_relabelingInvariant_iff_constant
#print axioms finiteLabelTotal_of_equal
#print axioms finiteLabelTotal_unit
#print axioms finiteCapacity_does_not_force_uniformity
#print axioms finiteLabel_normalization_forces_unitShare
#print axioms finiteLabel_normalizedShare_unique
#print axioms canonicalResidualPrefixCountingShare
#print axioms canonicalResidualPrefixCountingShare_invariant
#print axioms canonicalResidualPrefixCountingShare_eq_unit_over_capacity
#print axioms residualPrefix_normalizedShare_unique
#print axioms truncateResidualPrefix
#print axioms extendResidualPrefix
#print axioms topResidual
#print axioms ResidualPrefixRefinementFiber
#print axioms residualPrefixRefinementChild
#print axioms residualPrefixRefinementEquivFin
#print axioms residualPrefixRefinementAggregateShare
#print axioms repeatCountingShare
#print axioms zeroRefinement_cannot_conserve_unit
#print axioms canonicalResidualDepthMass
#print axioms truncateResidualPrefix_extend
#print axioms topResidual_extend
#print axioms extendResidualPrefix_truncate_top
#print axioms truncateResidualPrefix_of_canonicalTower
#print axioms residualPrefixRefinementChild_top
#print axioms residualPrefixRefinementChild_recovers
#print axioms residualPrefixRefinementChild_injective
#print axioms residualPrefixRefinement_fiber_cardinality
#print axioms residualPrefixValue_extend
#print axioms residualPrefixRefinementAggregateShare_common_denominator
#print axioms residualPrefixRefinementAggregateShare_numerator
#print axioms residualPrefix_refinement_conserves_share
#print axioms canonicalResidualPrefixCountingShare_eq_depthMass
#print axioms residualPrefixRefinementAggregateShare_eq_repeat_depthMass
#print axioms canonicalResidualDepthMass_zero
#print axioms canonicalResidualDepthMass_refinement
#print axioms canonicalResidualDepthMass_eq_unit_over_capacity
#print axioms quadraticExponentEquation_iff_half
#print axioms quadraticCarryCompatibleAt_iff_half
#print axioms quadratic_carry_exponent_iff_half
#print axioms quadraticCarryCompatibleAt_zero

-- Small examples; no positional/carry capstone is asserted.
example : FaithfulRepresentation (fun n : Nat => (0, n)) := by
  intro a b h
  exact congrArg Prod.snd h

example : ¬ FaithfulRepresentation (fun _ : Nat => (0 : Nat)) := by
  intro h
  exact Nat.zero_ne_one (h (a := 0) (b := 1) rfl)

-- The ratio is selected without imposing a reduced numerator/denominator.
example : FormalExponentRepresentsHalf 1 2 := by
  unfold FormalExponentRepresentsHalf
  decide
example : FormalExponentRepresentsHalf 2 4 := by
  unfold FormalExponentRepresentsHalf
  decide
example : ¬ FormalExponentRepresentsHalf 1 3 := by
  unfold FormalExponentRepresentsHalf
  decide
example : ¬ FormalExponentRepresentsHalf 0 0 := by
  unfold FormalExponentRepresentsHalf
  decide
example : QuadraticCarryCompatibleAt 0 7 3 := by
  unfold QuadraticCarryCompatibleAt
  decide
example : QuadraticCarryCompatibleAt 5 2 4 := by
  unfold QuadraticCarryCompatibleAt
  decide
example : ¬ QuadraticCarryCompatibleAt 5 1 3 := by
  unfold QuadraticCarryCompatibleAt
  decide

-- A concrete two-state local dynamics, without quotient/remainder arithmetic.
private def counterTrajectory : UnitTrajectory Nat where
  state := fun n => n
  transition := Nat.succ
  evolves := fun _ => rfl
  state_injective := fun {_ _} h => h

private def toggleObservation : Nat → Bool
  | 0 => false
  | n + 1 => !(toggleObservation n)

private def toggleDynamics : AutonomousLocalDynamics counterTrajectory Bool where
  observe := toggleObservation
  step := Bool.not
  intertwines := fun _ => rfl
  step_injective := by
    intro a b h
    cases a <;> cases b
    · rfl
    · cases h
    · cases h
    · rfl

private def boolPresentation : FiniteLocalPresentation Bool where
  size := 2
  encode := fun b => if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
  encode_injective := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact False.elim (Nat.zero_ne_one (congrArg Fin.val h))
    · exact False.elim (Nat.zero_ne_one (congrArg Fin.val h).symm)
    · rfl

-- The abstract existence theorem produces capacity two for this model.
example : EmergentLocalCapacity counterTrajectory toggleDynamics 2 := by
  have hchange : toggleDynamics.observe (counterTrajectory.state 1) ≠
      toggleDynamics.observe (counterTrajectory.state 0) := by decide
  rcases exists_emergentLocalCapacity_gt_one counterTrajectory toggleDynamics
      boolPresentation hchange with ⟨b, hgt, hbound, hcap⟩
  have hb : b = 2 := Nat.le_antisymm hbound (Nat.succ_le_of_lt hgt)
  exact hb ▸ hcap

-- Singleton coding permits period one; the nontrivial-first-step hypothesis
-- is therefore necessary to derive the stronger lower bound.
example : ∃ b, b ≤ 1 ∧ PositiveLocalReturn counterTrajectory
    { observe := fun _ => (), step := fun x => x,
      intertwines := fun _ => rfl, step_injective := fun {_ _} h => h } b := by
  exact autonomousLocalDynamics_has_positiveReturn counterTrajectory
    { observe := fun _ => (), step := fun x => x,
      intertwines := fun _ => rfl, step_injective := fun {_ _} h => h }
    { size := 1, encode := fun _ => ⟨0, by decide⟩,
      encode_injective := by intro a b _; cases a; cases b; rfl }

-- Cycle coordinates are computed from unit stepping, without division/modulo.
example : cycleCoordinatesRec 3 2 = (0, 2) := by decide
example : cycleCoordinatesRec 3 3 = (1, 0) := by decide
example : cycleCoordinatesRec 3 8 = (2, 2) := by decide
example : cycleCoordinatesRec 3 9 = (3, 0) := by decide
example : cycleCoordinatesRec 1 4 = (4, 0) := by decide

-- Both successor regimes preserve the exact count.
example : completedCycleCount 3 3 = completedCycleCount 3 2 + 1 ∧
    cycleResidual 3 3 = 0 := by
  exact cycle_step_at_boundary (b := 3) (n := 2) (by decide)
example : completedCycleCount 3 5 = completedCycleCount 3 4 ∧
    cycleResidual 3 5 = cycleResidual 3 4 + 1 := by
  exact cycle_step_inside (b := 3) (n := 4) (by decide)

-- The validity theorem excludes zero capacity: no bounded residual exists there.
example (cycles residual : Nat) : ¬ IsCycleDecomposition 0 0 cycles residual := by
  intro h
  exact Nat.not_lt_zero residual h.2

-- The lowest residual is first; the unresolved tail is always retained.
example : emergentResidualTower 3 0 17 = (17 : Nat) := by rfl
example : emergentResidualTower 3 1 17 = (2, (5 : Nat)) := by rfl
example : emergentResidualTower 3 2 17 = (2, 2, (1 : Nat)) := by rfl
example : emergentResidualTower 3 3 17 = (2, 2, 1, (0 : Nat)) := by rfl
example : emergentResidualTower 3 2 8 = (2, 2, (0 : Nat)) := by rfl

-- Same two residuals, different tails: the prefix alone is not the full quantity.
example : residualTowerPrefixValue 3 (depth := 2) (2, 2, (1 : Nat)) = 8 := by decide
example : residualTowerValue 3 (depth := 2) (2, 2, (1 : Nat)) = 17 := by decide
example : truncateResidualTower 3 1 2 (2, 2, 1, (0 : Nat)) = (2, (5 : Nat)) := by rfl

-- With capacity one the tower exists but does not eliminate a nonzero tail.
-- No termination claim is smuggled into the finite-depth theorem.
example : emergentResidualTower 1 3 5 = (0, 0, 0, (5 : Nat)) := by rfl

-- Every bounded tuple is recovered from its reconstructed count.
example : (2, 2, (1 : Nat)) = emergentResidualTower 3 2 17 := by
  apply residualTower_eq_canonical 3 2 17 (by decide)
    (2, 2, (1 : Nat)) (by change 2 < 3 ∧ 2 < 3 ∧ True; decide) (by decide)

-- Resolve only the finite prefix; capacity 3 at depth 2 has codes in Fin 9.
private def twoTwoPrefix : ResidualPrefix 3 2 :=
  (⟨2, by decide⟩, ⟨2, by decide⟩, (PUnit.unit : PUnit))

example : residualPrefixValue 3 twoTwoPrefix = 8 := by rfl
example : residualPrefixTower 3 twoTwoPrefix = (2, 2, (0 : Nat)) := by rfl
example : residualPrefixEncode 3 2 twoTwoPrefix = (⟨8, by decide⟩ : Fin 9) := by rfl
example : residualPrefixDecode 3 2 (by decide) (⟨8, by decide⟩ : Fin 9) =
    twoTwoPrefix := by rfl

-- The same low residuals in 17 do not justify forgetting its nonzero tail.
example : residualTowerTail (emergentResidualTower 3 2 8) = 0 := by
  exact residualTower_tail_eq_zero_of_lt_pow 3 2 8 (by decide) (by decide)
example : residualTowerTail (emergentResidualTower 3 2 9) = 1 := by rfl
example : residualTowerTail (emergentResidualTower 3 2 17) = 1 := by rfl

-- Empty prefix has exactly the one code in Fin (b^0); no empty-case loss of data.
example : residualPrefixEncode 3 0 (PUnit.unit : PUnit) = (⟨0, by decide⟩ : Fin 1) := by rfl
example : residualPrefixDecode 3 0 (by decide) (⟨0, by decide⟩ : Fin 1) =
    (PUnit.unit : PUnit) := by rfl

-- Capacity one also has exactly one prefix at every finite depth.
example : ∀ resolved : ResidualPrefix 1 3,
    residualPrefixEncode 1 3 resolved = (⟨0, by decide⟩ : Fin 1) := by
  intro resolved
  apply Fin.ext
  exact Nat.eq_zero_of_le_zero
    (Nat.le_of_lt_succ (residualPrefix_value_lt_pow 1 3 resolved))

-- No hidden inhabitant at zero capacity and positive depth.
example : ¬ Nonempty (ResidualPrefix 0 1) := by
  intro inhabited
  rcases inhabited with ⟨resolved⟩
  exact Nat.not_lt_zero _ resolved.1.isLt

-- Both inverse laws certify the full finite coding, not just scalar readout values.
example : residualPrefixDecode 3 2 (by decide)
    (residualPrefixEncode 3 2 twoTwoPrefix) = twoTwoPrefix :=
  residualPrefix_decode_encode 3 2 (by decide) twoTwoPrefix

-- Transpositions remain genuine inverse maps when the two labels coincide.
example : (finiteLabelTransposition (⟨1, by decide⟩ : Fin 3) ⟨1, by decide⟩).forward
    ⟨1, by decide⟩ = ⟨1, by decide⟩ := by rfl
example : (finiteLabelTransposition (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩).forward
    ⟨1, by decide⟩ = ⟨1, by decide⟩ := by rfl
example : (finiteLabelTransposition (⟨0, by decide⟩ : Fin 3) ⟨2, by decide⟩).forward
    ⟨0, by decide⟩ = ⟨2, by decide⟩ := by rfl

-- A label change need not preserve reconstructed quantity: it is not a dynamic
-- automorphism. It only preserves the bare resolved state set for counting.
example : (residualPrefixRelabeling 3 2 (by decide)
    (finiteLabelTransposition (⟨0, by decide⟩ : Fin 9) ⟨8, by decide⟩)).forward
    (residualPrefixDecode 3 2 (by decide) ⟨0, by decide⟩) = twoTwoPrefix := by rfl

-- Formal shares need no quotient; the same unit share has multiple presentations.
example : SameCountingShare ⟨2, 18, by decide⟩ ⟨1, 9, by decide⟩ := by
  change 2 * 9 = 1 * 18
  decide
example : ¬ SameCountingShare ⟨1, 3, by decide⟩ ⟨1, 9, by decide⟩ := by
  change ¬ (1 * 9 = 1 * 3)
  decide
example : finiteLabelTotal 9 (fun _ => 2) = 18 := by rfl
example : SameCountingShare ⟨2, 18, by decide⟩
    (canonicalResidualPrefixCountingShare 3 2 (by decide) twoTwoPrefix) := by
  apply residualPrefix_normalizedShare_unique 3 2 18 (by decide) (by decide)
    (fun _ => 2)
  · intro labels x
    rfl
  · rfl

-- Empty resolved prefix and capacity one both receive the whole formal unit.
example : (canonicalResidualPrefixCountingShare 3 0 (by decide) PUnit.unit).denominator = 1 :=
  (canonicalResidualPrefixCountingShare_eq_unit_over_capacity 3 0 (by decide) PUnit.unit).2
example : (canonicalResidualPrefixCountingShare 1 2 (by decide)
    (residualPrefixDecode 1 2 (by decide) ⟨0, by decide⟩)).denominator = 1 :=
  (canonicalResidualPrefixCountingShare_eq_unit_over_capacity 1 2 (by decide) _).2

-- Finite capacity and a positive normalized total alone do NOT select uniformity.
example : ∃ weight : Fin 2 → Nat, finiteLabelTotal 2 weight = 1 ∧
    ¬ RelabelingInvariant weight := finiteCapacity_does_not_force_uniformity

-- Refinement appends at the DEEPEST end; .2 would instead remove the lowest residual.
example : extendResidualPrefix 3 twoTwoPrefix ⟨1, by decide⟩ =
    (⟨2, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, (PUnit.unit : PUnit)) := rfl
example : truncateResidualPrefix 3 (depth := 2)
    (⟨2, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, (PUnit.unit : PUnit)) =
    twoTwoPrefix := rfl
example : topResidual 3 (extendResidualPrefix 3 twoTwoPrefix ⟨1, by decide⟩) =
    ⟨1, by decide⟩ := rfl
example : residualPrefixValue 3 (extendResidualPrefix 3 twoTwoPrefix ⟨1, by decide⟩) =
    17 := rfl
example : residualPrefixValue 3 (extendResidualPrefix 3 twoTwoPrefix ⟨2, by decide⟩) =
    8 + 2 * 3 ^ 2 := residualPrefixValue_extend 3 2 twoTwoPrefix ⟨2, by decide⟩

-- The same truncation operates on the original tower even when a tail remains.
example : truncateResidualPrefix 3
    (residualPrefixOfBoundedTower 3 (emergentResidualTower 3 3 100)
      (emergentResidualTower_bounded 3 3 100 (by decide))) =
    residualPrefixOfBoundedTower 3 (emergentResidualTower 3 2 100)
      (emergentResidualTower_bounded 3 2 100 (by decide)) :=
  truncateResidualPrefix_of_canonicalTower 3 2 100 (by decide)

-- The fiber has one distinct member for each child label.
example : (residualPrefixRefinementEquivFin 3 2 twoTwoPrefix).val.2
    ((residualPrefixRefinementEquivFin 3 2 twoTwoPrefix).val.1 ⟨2, by decide⟩) =
    ⟨2, by decide⟩ :=
  (residualPrefixRefinementEquivFin 3 2 twoTwoPrefix).property.1 _

-- Aggregating actual child shares gives (3,27), equivalent but not equal to (1,9).
example : (residualPrefixRefinementAggregateShare 3 2 (by decide) twoTwoPrefix).numerator =
    3 := residualPrefixRefinementAggregateShare_numerator 3 2 (by decide) twoTwoPrefix
example : (residualPrefixRefinementAggregateShare 3 2 (by decide) twoTwoPrefix).denominator =
    27 := rfl
example : SameCountingShare (residualPrefixRefinementAggregateShare 3 2 (by decide) twoTwoPrefix)
    (canonicalResidualPrefixCountingShare 3 2 (by decide) twoTwoPrefix) :=
  residualPrefix_refinement_conserves_share 3 2 (by decide) twoTwoPrefix
example : residualPrefixRefinementAggregateShare 3 2 (by decide) twoTwoPrefix ≠
    canonicalResidualPrefixCountingShare 3 2 (by decide) twoTwoPrefix := by
  intro heq
  have h := congrArg FormalCountingShare.numerator heq
  exact (by decide : (3 : Nat) ≠ 1) h

-- Depth zero has the one empty parent and exactly b first refinements.
example : truncateResidualPrefix 3 (depth := 0)
    (extendResidualPrefix 3 (depth := 0) (PUnit.unit : PUnit) ⟨2, by decide⟩) =
    (PUnit.unit : PUnit) := truncateResidualPrefix_extend 3 0 _ _
example : canonicalResidualDepthMass 3 0 (by decide) = ⟨1, 1, by decide⟩ :=
  canonicalResidualDepthMass_zero 3 (by decide)

-- Capacity one: there is only one child and aggregation changes no presentation.
example : residualPrefixRefinementAggregateShare 1 2 (by decide)
    (residualPrefixDecode 1 2 (by decide) ⟨0, by decide⟩) =
    canonicalResidualDepthMass 1 2 (by decide) := rfl

-- Capacity zero: the empty parent exists, but its refinement fiber is empty.
-- Structural maps still make sense; no positive-denominator mass is asserted.
example : ¬ Nonempty (ResidualPrefixRefinementFiber 0 0 (PUnit.unit : PUnit)) := by
  intro hexists
  rcases hexists with ⟨refined⟩
  exact Nat.not_lt_zero _ refined.val.1.isLt
example : repeatCountingShare 0 ⟨1, 7, by decide⟩ = ⟨0, 7, by decide⟩ := rfl

end GeometryOfNumbers.Foundation
