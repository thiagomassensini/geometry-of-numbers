import GeometryOfNumbers.Foundation.FiniteLocalRecurrence

/-!
# The pre-positional capacity interface

Ported from `QuantityRepresentationFoundations/FirstLocalReturnCapacity.lean`
and the elementary capacity bound in `FoundationalCapstone.lean`, source
commit `66f9ab46c6fa2622c5e6d9f5ed2c497040c62374`.

The least positive return is derived by bounded constructive search from an
explicit finite local presentation. Nothing here assumes digits, residual
geometry, or carry.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false

universe u v

/-- Capacity is the least positive return, before any positional interpretation. -/
def EmergentLocalCapacity {Q : Type u} {Local : Type v}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local) (b : Nat) : Prop :=
  PositiveLocalReturn trajectory model b ∧
    ∀ n, PositiveLocalReturn trajectory model n → b ≤ n

/-- Two least positive returns must have the same capacity. This does not prove existence. -/
theorem emergentLocalCapacity_unique
    {Q : Type u} {Local : Type v}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    {b c : Nat}
    (hb : EmergentLocalCapacity trajectory model b)
    (hc : EmergentLocalCapacity trajectory model c) :
    b = c := by
  exact Nat.le_antisymm (hb.2 c hc.1) (hc.2 b hb.1)

/-- A changing first local step excludes return time one; positivity then gives `1 < b`. -/
theorem emergentLocalCapacity_gt_one_of_first_step_changes
    {Q : Type u} {Local : Type v}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    {b : Nat} (hb : EmergentLocalCapacity trajectory model b)
    (hchange : model.observe (trajectory.state 1) ≠
      model.observe (trajectory.state 0)) :
    1 < b := by
  have hbne : 1 ≠ b := by
    intro heq
    have hreturn := hb.1.2
    rw [← heq] at hreturn
    exact hchange hreturn
  exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hb.1.1) hbne

/-- Explicit finite coding, autonomous evolution, and an injective local step
produce a least positive return within the finite coding budget. -/
theorem exists_emergentLocalCapacity
    {Q : Type u} {Local : Type v}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    (presentation : FiniteLocalPresentation Local) :
    ∃ b, b ≤ presentation.size ∧ EmergentLocalCapacity trajectory model b := by
  let code (n : Nat) := (presentation.encode (model.observe (trajectory.state n))).val
  let P (n : Nat) := 0 < n ∧ code n = code 0
  have toCode {n : Nat} (h : PositiveLocalReturn trajectory model n) : P n :=
    ⟨h.1, congrArg (fun x => (presentation.encode x).val) h.2⟩
  have fromCode {n : Nat} (h : P n) : PositiveLocalReturn trajectory model n :=
    ⟨h.1, presentation.encode_injective (Fin.ext h.2)⟩
  rcases autonomousLocalDynamics_has_positiveReturn trajectory model presentation with
    ⟨r, hr, hreturn⟩
  cases boundedLeastOrAbsent P presentation.size with
  | inl found =>
    rcases found with ⟨b, hb, hp, hleast⟩
    exact ⟨b, hb, fromCode hp, fun n hn => hleast n (toCode hn)⟩
  | inr absent => exact False.elim (absent r hr (toCode hreturn))

/-- Existence and uniqueness are both derived, rather than stored as inputs.
Uniqueness is written explicitly to keep the foundation within `Init`. -/
theorem existsUnique_emergentLocalCapacity
    {Q : Type u} {Local : Type v}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    (presentation : FiniteLocalPresentation Local) :
    ∃ b, b ≤ presentation.size ∧ EmergentLocalCapacity trajectory model b ∧
      ∀ c, EmergentLocalCapacity trajectory model c → c = b := by
  rcases exists_emergentLocalCapacity trajectory model presentation with ⟨b, hb, hcap⟩
  exact ⟨b, hb, hcap, fun c hc => emergentLocalCapacity_unique trajectory model hc hcap⟩

/-- A nontrivial first local step makes the produced capacity genuinely larger
than one. No positional or carry hypothesis is used. -/
theorem exists_emergentLocalCapacity_gt_one
    {Q : Type u} {Local : Type v}
    (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    (presentation : FiniteLocalPresentation Local)
    (hchange : model.observe (trajectory.state 1) ≠
      model.observe (trajectory.state 0)) :
    ∃ b, 1 < b ∧ b ≤ presentation.size ∧ EmergentLocalCapacity trajectory model b := by
  rcases exists_emergentLocalCapacity trajectory model presentation with ⟨b, hb, hcap⟩
  exact ⟨b, emergentLocalCapacity_gt_one_of_first_step_changes trajectory model hcap hchange,
    hb, hcap⟩

end GeometryOfNumbers.Foundation
