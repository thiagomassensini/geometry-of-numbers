import GeometryOfNumbers.Foundation.QuadraticMassCompatibility

/-!
# Closing the discrete foundation

Only composition of the existing theorems: the capacity is the first return
of the original trajectory, not an externally selected radix. Finite local
presentation produces that capacity; a changing first step makes it nontrivial.
The previously derived mass then selects half under the explicit quadratic
scale requirement. No numerical amplitude or metric is introduced here.

This is the end of the axiom-free discrete scaling foundation. Analytic
realizations belong to `GeometryOfNumbers.Analysis` and are never imported here.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false
universe u v

/-- The minimal capstone for the same emergent capacity and its derived mass. -/
theorem foundational_half_scaling_capstone
    {Q : Type u} {Local : Type v} (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    {b : Nat} (hcap : EmergentLocalCapacity trajectory model b)
    (hchange : model.observe (trajectory.state 1) ≠ model.observe (trajectory.state 0))
    (k p q : Nat) (hk : 0 < k) :
    QuadraticAmplitudeScaleCompatibleAt b k p q hcap.1.1 ↔
      FormalExponentRepresentsHalf p q :=
  canonicalResidualDepthMass_quadraticCompatibility_iff_half b k p q
    (emergentLocalCapacity_gt_one_of_first_step_changes trajectory model hcap hchange) hk

/-- Finite local data PRODUCE a nontrivial first return with the scaling capstone.
Autonomy, injectivity, finite coding and first-step change remain explicit inputs. -/
theorem exists_foundational_half_scaling_capstone
    {Q : Type u} {Local : Type v} (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    (presentation : FiniteLocalPresentation Local)
    (hchange : model.observe (trajectory.state 1) ≠ model.observe (trajectory.state 0)) :
    ∃ b, ∃ hcap : EmergentLocalCapacity trajectory model b,
      1 < b ∧ b ≤ presentation.size ∧
      ∀ k p q, 0 < k →
        (QuadraticAmplitudeScaleCompatibleAt b k p q hcap.1.1 ↔
          FormalExponentRepresentsHalf p q) := by
  rcases exists_emergentLocalCapacity_gt_one trajectory model presentation hchange with
    ⟨b, hnontrivial, hbound, hcap⟩
  exact ⟨b, hcap, hnontrivial, hbound,
    fun k p q hk => foundational_half_scaling_capstone trajectory model hcap hchange k p q hk⟩

end GeometryOfNumbers.Foundation
