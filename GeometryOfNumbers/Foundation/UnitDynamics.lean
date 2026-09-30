import GeometryOfNumbers.Foundation.QuantityRepresentation

/-!
# Unit-step observation and preservation of information

Constructive ports of elementary consequences from
`QuantityRepresentationFoundations/UnitDynamicsLocalRecurrence.lean` and
`FirstLocalReturnCapacity.lean`, source commit
`66f9ab46c6fa2622c5e6d9f5ed2c497040c62374`.

This first layer records the dynamics and consequences of a given return.
`FiniteLocalRecurrence` derives recurrence and positive return from explicit
finite coding; `FirstLocalReturnCapacity` then derives the least return.
These results are not yet a theorem of carry emergence.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false

universe u v w

/-- Natural numbers index unit steps; the quantity type has no assumed arithmetic. -/
structure UnitTrajectory (Q : Type u) where
  state : Nat → Q
  transition : Q → Q
  evolves : ∀ n, state (n + 1) = transition (state n)
  state_injective : FaithfulRepresentation state

/-- Local recurrence is an event, not a positional convention. -/
def LocalRecurrence {Q : Type u} {Local : Type v}
    (trajectory : UnitTrajectory Q) (observe : Q → Local)
    (m n : Nat) : Prop :=
  m < n ∧ observe (trajectory.state m) = observe (trajectory.state n)

/-- The extension distinguishes the two quantities whenever a local recurrence occurs. -/
theorem localRecurrence_forces_extension_difference
    {Q : Type u} {Local : Type v} {Extension : Type w}
    (trajectory : UnitTrajectory Q) (encode : Q → Local × Extension)
    (hfaithful : FaithfulRepresentation encode)
    {m n : Nat}
    (hrec : LocalRecurrence trajectory (fun q => (encode q).1) m n) :
    (encode (trajectory.state m)).2 ≠ (encode (trajectory.state n)).2 := by
  apply sameLocal_forces_extension_difference encode hfaithful _ hrec.2
  intro hstates
  exact Nat.ne_of_lt hrec.1 (trajectory.state_injective hstates)

/-- Autonomous observation, without a base, carry law, or assumed period. -/
structure AutonomousLocalDynamics {Q : Type u}
    (trajectory : UnitTrajectory Q) (Local : Type v) where
  observe : Q → Local
  step : Local → Local
  intertwines : ∀ q, observe (trajectory.transition q) = step (observe q)
  step_injective : FaithfulRepresentation step

/-- A positive return to the initial observation. Existence is not assumed globally. -/
def PositiveLocalReturn {Q : Type u} {Local : Type v}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local) (b : Nat) : Prop :=
  0 < b ∧ model.observe (trajectory.state b) = model.observe (trajectory.state 0)

/-- Autonomy propagates any return to a period of the observed trajectory. -/
theorem positiveLocalReturn_implies_periodic_readout
    {Q : Type u} {Local : Type v}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    {b : Nat} (hreturn : PositiveLocalReturn trajectory model b) :
    ∀ n, model.observe (trajectory.state (n + b)) =
      model.observe (trajectory.state n) := by
  intro n
  induction n with
  | zero =>
    rw [Nat.zero_add]
    exact hreturn.2
  | succ n ih =>
    have hindex : (n + 1) + b = (n + b) + 1 :=
      Nat.add_right_comm n 1 b
    rw [hindex, trajectory.evolves, trajectory.evolves,
      model.intertwines, model.intertwines, ih]

end GeometryOfNumbers.Foundation
