import GeometryOfNumbers.Foundation.UnitDynamics

/-!
# Constructive finite local recurrence

The historical source is `quantity-representation-foundations`, commit
`66f9ab46c6fa2622c5e6d9f5ed2c497040c62374`, modules
`UnitDynamicsLocalRecurrence` and `FirstLocalReturnCapacity`.

Finiteness is supplied as encoding data, not as a classical enumeration.
Bounded search and pigeonhole are proved by induction. No carry, radix,
metric, or numerical realization is assumed.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false
universe u v

/-- An explicit finite coding budget; the encoding need not be surjective. -/
structure FiniteLocalPresentation (Local : Type v) where
  size : Nat
  encode : Local → Fin size
  encode_injective : FaithfulRepresentation encode

/-- Finite search either finds the globally least witness in the budget or
certifies that every index in that budget fails. -/
theorem boundedLeastOrAbsent (P : Nat → Prop) [DecidablePred P] (budget : Nat) :
    (∃ b, b ≤ budget ∧ P b ∧ ∀ n, P n → b ≤ n) ∨
      (∀ n, n ≤ budget → ¬ P n) := by
  induction budget with
  | zero =>
    by_cases h : P 0
    · exact Or.inl ⟨0, Nat.le_refl 0, h, fun _ _ => Nat.zero_le _⟩
    · apply Or.inr
      intro n hn hp
      have heq : n = 0 := Nat.eq_zero_of_le_zero hn
      exact h (heq ▸ hp)
  | succ budget ih =>
    cases ih with
    | inl found =>
      rcases found with ⟨b, hb, hp, hleast⟩
      exact Or.inl ⟨b, Nat.le_trans hb (Nat.le_succ budget), hp, hleast⟩
    | inr absent =>
      by_cases hp : P (budget + 1)
      · apply Or.inl
        refine ⟨budget + 1, Nat.le_refl _, hp, ?_⟩
        intro n hn
        cases Nat.lt_or_ge n (budget + 1) with
        | inl hlt => exact False.elim (absent n (Nat.le_of_lt_succ hlt) hn)
        | inr hge => exact hge
      · apply Or.inr
        intro n hn hpn
        cases Nat.eq_or_lt_of_le hn with
        | inl heq => exact hp (heq ▸ hpn)
        | inr hlt => exact absent n (Nat.le_of_lt_succ hlt) hpn

private def eraseCode (pivot code : Nat) : Nat :=
  if code < pivot then code else code.pred

private theorem eraseCode_lt {pivot code budget : Nat}
    (hp : pivot < budget + 1) (hc : code < budget + 1) (hne : code ≠ pivot) :
    eraseCode pivot code < budget := by
  unfold eraseCode
  split
  · next h => exact Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ hp)
  · next h =>
    have hpc : pivot < code :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt h) (fun heq => hne heq.symm)
    cases code with
    | zero => exact False.elim (Nat.not_lt_zero pivot hpc)
    | succ code => exact Nat.lt_of_succ_lt_succ hc

private theorem eraseCode_injective {pivot a b : Nat}
    (ha : a ≠ pivot) (hb : b ≠ pivot)
    (heq : eraseCode pivot a = eraseCode pivot b) : a = b := by
  unfold eraseCode at heq
  split at heq
  · next hal =>
    split at heq
    · exact heq
    · next hbl =>
      have hpb : pivot < b :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_gt hbl) (fun h => hb h.symm)
      cases b with
      | zero => exact False.elim (Nat.not_lt_zero pivot hpb)
      | succ b =>
        have hp : pivot ≤ b := Nat.le_of_lt_succ hpb
        have hab : a < b := Nat.lt_of_lt_of_le hal hp
        exact False.elim (Nat.ne_of_lt hab heq)
  · next hal =>
    split at heq
    · next hbl =>
      have hpa : pivot < a :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_gt hal) (fun h => ha h.symm)
      cases a with
      | zero => exact False.elim (Nat.not_lt_zero pivot hpa)
      | succ a =>
        have hp : pivot ≤ a := Nat.le_of_lt_succ hpa
        have hba : b < a := Nat.lt_of_lt_of_le hbl hp
        exact False.elim (Nat.ne_of_lt hba heq.symm)
    · next hbl =>
      have hpa : 0 < a := Nat.lt_of_le_of_lt (Nat.zero_le pivot)
        (Nat.lt_of_le_of_ne (Nat.le_of_not_gt hal) (fun h => ha h.symm))
      have hpb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le pivot)
        (Nat.lt_of_le_of_ne (Nat.le_of_not_gt hbl) (fun h => hb h.symm))
      exact (Nat.succ_pred (Nat.ne_of_gt hpa)).symm.trans
        ((congrArg Nat.succ heq).trans (Nat.succ_pred (Nat.ne_of_gt hpb)))

/-- `budget + 1` entries coded by `budget` naturals have an ordered collision. -/
theorem finiteCodeCollision (budget : Nat) (code : Nat → Nat)
    (hbound : ∀ n, n ≤ budget → code n < budget) :
    ∃ m n, m < n ∧ n ≤ budget ∧ code m = code n := by
  induction budget generalizing code with
  | zero => exact False.elim (Nat.not_lt_zero _ (hbound 0 (Nat.le_refl 0)))
  | succ budget ih =>
    cases boundedLeastOrAbsent (fun n => code (n + 1) = code 0) budget with
    | inl found =>
      rcases found with ⟨n, hn, heq, _⟩
      exact ⟨0, n + 1, Nat.zero_lt_succ n, Nat.succ_le_succ hn, heq.symm⟩
    | inr absent =>
      have hp : code 0 < budget + 1 := hbound 0 (Nat.zero_le _)
      have hsmall : ∀ n, n ≤ budget →
          eraseCode (code 0) (code (n + 1)) < budget := by
        intro n hn
        exact eraseCode_lt hp (hbound (n + 1) (Nat.succ_le_succ hn))
          (absent n hn)
      rcases ih (fun n => eraseCode (code 0) (code (n + 1))) hsmall with
        ⟨m, n, hmn, hn, heq⟩
      exact ⟨m + 1, n + 1, Nat.succ_lt_succ hmn, Nat.succ_le_succ hn,
        eraseCode_injective (absent m (Nat.le_trans (Nat.le_of_lt hmn) hn))
          (absent n hn) heq⟩

/-- A finite local presentation forces recurrence within its coding budget. -/
theorem unitTrajectory_forces_localRecurrence
    {Q : Type u} {Local : Type v} (trajectory : UnitTrajectory Q)
    (observe : Q → Local) (presentation : FiniteLocalPresentation Local) :
    ∃ m n, n ≤ presentation.size ∧ LocalRecurrence trajectory observe m n := by
  rcases finiteCodeCollision presentation.size
      (fun n => (presentation.encode (observe (trajectory.state n))).val)
      (fun n _ => (presentation.encode (observe (trajectory.state n))).isLt) with
    ⟨m, n, hmn, hn, heq⟩
  exact ⟨m, n, hn, hmn, presentation.encode_injective (Fin.ext heq)⟩

private theorem cancelLocalPrefix
    {Q : Type u} {Local : Type v} (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local) (m b : Nat)
    (heq : model.observe (trajectory.state (m + b)) =
      model.observe (trajectory.state m)) :
    model.observe (trajectory.state b) = model.observe (trajectory.state 0) := by
  induction m with
  | zero => rw [Nat.zero_add] at heq; exact heq
  | succ m ih =>
    rw [Nat.add_right_comm m 1 b, trajectory.evolves, trajectory.evolves,
      model.intertwines, model.intertwines] at heq
    exact ih (model.step_injective heq)

private theorem positiveGap {m n : Nat} (hlt : m < n) :
    ∃ b, 0 < b ∧ b ≤ n ∧ n = m + b := by
  induction m generalizing n with
  | zero => exact ⟨n, hlt, Nat.le_refl n, (Nat.zero_add n).symm⟩
  | succ m ih =>
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero _ hlt)
    | succ n =>
      rcases ih (Nat.lt_of_succ_lt_succ hlt) with ⟨b, hb, hbn, heq⟩
      exact ⟨b, hb, Nat.le_trans hbn (Nat.le_succ n),
        (congrArg Nat.succ heq).trans (Nat.succ_add m b).symm⟩

/-- Autonomy and injectivity move a finite collision back to time zero. -/
theorem autonomousLocalDynamics_has_positiveReturn
    {Q : Type u} {Local : Type v} (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    (presentation : FiniteLocalPresentation Local) :
    ∃ b, b ≤ presentation.size ∧ PositiveLocalReturn trajectory model b := by
  rcases unitTrajectory_forces_localRecurrence trajectory model.observe presentation with
    ⟨m, n, hn, hmn, heq⟩
  rcases positiveGap hmn with ⟨b, hb, hbn, hindex⟩
  rw [hindex] at heq
  exact ⟨b, Nat.le_trans hbn hn, hb, cancelLocalPrefix trajectory model m b heq.symm⟩

end GeometryOfNumbers.Foundation
