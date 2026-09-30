import GeometryOfNumbers.Foundation.ResidualPrefixRefinement
import GeometryOfNumbers.Foundation.QuadraticAmplitudeExponent

/-!
# From derived depth mass to formal quadratic scale compatibility

The depth mass remains the counting share constructed from the residual tower.
`radixShare` is its subsequent power-scale presentation, not its definition.
Products and powers below operate on presentations of shares, without quotients.

Quadratic compatibility is a NEW explicit semantic requirement on a candidate
formal exponent: its squared, denominator-cleared scale must represent the
`q`-fold product of the actual depth mass. Counting alone does not require a
quadratic observable. Once that requirement is imposed, nontrivial capacity
recovers the exponent equation and the existing arithmetic selects half.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false

-- These elementary proofs avoid the axioms of the general library power API.
private theorem mulAssoc (a c b : Nat) : (a * c) * b = a * (c * b) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_add, ih]

private theorem powAdd (b a c : Nat) : b ^ (a + c) = b ^ a * b ^ c := by
  induction c with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ c ih => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, mulAssoc]

private theorem powMul (b k q : Nat) : b ^ (k * q) = (b ^ k) ^ q := by
  induction q with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ, powAdd, Nat.pow_succ, ih]

private theorem powStep (b n : Nat) (hb : 1 < b) : b ^ n < b ^ (n + 1) := by
  have h := Nat.mul_lt_mul_of_pos_left hb
    (Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one hb) : 0 < b ^ n)
  rw [Nat.mul_one, ← Nat.pow_succ] at h
  exact h

private theorem powStrict (b n m : Nat) (hb : 1 < b) (h : n < m) : b ^ n < b ^ m := by
  induction m generalizing n with
  | zero => exact False.elim (Nat.not_lt_zero n h)
  | succ m ih =>
    by_cases heq : n = m
    · subst n
      exact powStep b m hb
    · have hnm : n < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) heq
      exact Nat.lt_trans (ih n hnm) (powStep b m hb)

private theorem powInjective (b a c : Nat) (hb : 1 < b) (h : b ^ a = b ^ c) : a = c := by
  rcases Nat.lt_trichotomy a c with hlt | heq | hgt
  · exact False.elim (Nat.ne_of_lt (powStrict b a c hb hlt) h)
  · exact heq
  · exact False.elim (Nat.ne_of_lt (powStrict b c a hb hgt) h.symm)

private theorem shareExt (left right : FormalCountingShare)
    (hn : left.numerator = right.numerator)
    (hd : left.denominator = right.denominator) : left = right := by
  cases left
  cases right
  cases hn
  cases hd
  rfl

/-- Power-scale presentation, introduced only after mass has been constructed. -/
def radixShare (b exponent : Nat) (hb : 0 < b) : FormalCountingShare :=
  ⟨1, b ^ exponent, Nat.pow_pos hb⟩

/-- Multiplicative composition of presentations, not finite additive aggregation. -/
def multiplyCountingShares (left right : FormalCountingShare) : FormalCountingShare :=
  ⟨left.numerator * right.numerator, left.denominator * right.denominator,
    Nat.mul_pos left.denominator_positive right.denominator_positive⟩

/-- Repeated multiplicative composition; `repeatCountingShare` instead adds shares. -/
def powerCountingShare (share : FormalCountingShare) (q : Nat) : FormalCountingShare :=
  ⟨share.numerator ^ q, share.denominator ^ q, Nat.pow_pos share.denominator_positive⟩

/-- Zero compositions give the unit share. -/
theorem powerCountingShare_zero (share : FormalCountingShare) :
    powerCountingShare share 0 = ⟨1, 1, Nat.zero_lt_one⟩ := rfl

/-- Natural powers really are repeated multiplicative composition of shares. -/
theorem powerCountingShare_succ (share : FormalCountingShare) (q : Nat) :
    powerCountingShare share (q + 1) =
      multiplyCountingShares (powerCountingShare share q) share := rfl

/-- Literal identification of the previously derived mass with its power scale. -/
theorem canonicalResidualDepthMass_eq_radixShare (b k : Nat) (hb : 0 < b) :
    canonicalResidualDepthMass b k hb = radixShare b k hb := by
  have h := canonicalResidualDepthMass_eq_unit_over_capacity b k hb
  exact shareExt _ _ h.1 h.2

/-- Composition adds scale exponents, as a theorem about presentations. -/
theorem radixShare_multiply (b a c : Nat) (hb : 0 < b) :
    multiplyCountingShares (radixShare b a hb) (radixShare b c hb) =
      radixShare b (a + c) hb := by
  exact shareExt _ _ rfl (powAdd b a c).symm

/-- Denominator clearing scales the exponent of the actual geometric mass by `q`. -/
theorem canonicalResidualDepthMass_power_eq_radixShare (b k q : Nat) (hb : 0 < b) :
    powerCountingShare (canonicalResidualDepthMass b k hb) q =
      radixShare b (k * q) hb := by
  rw [canonicalResidualDepthMass_eq_radixShare]
  exact shareExt _ _ (Nat.one_pow q) (powMul b k q).symm

/-- Unit-numerator shares compare precisely by equality of their capacities. -/
theorem radixShare_same_iff_power_eq (b a c : Nat) (hb : 0 < b) :
    SameCountingShare (radixShare b a hb) (radixShare b c hb) ↔ b ^ a = b ^ c := by
  change 1 * b ^ c = 1 * b ^ a ↔ b ^ a = b ^ c
  rw [Nat.one_mul, Nat.one_mul]
  exact ⟨Eq.symm, Eq.symm⟩

/-- Nontrivial capacity is what makes an exponent recoverable from a scale. -/
theorem radixShare_same_iff_exponent_eq (b a c : Nat) (hb : 1 < b) :
    SameCountingShare (radixShare b a (Nat.lt_trans Nat.zero_lt_one hb))
      (radixShare b c (Nat.lt_trans Nat.zero_lt_one hb)) ↔ a = c := by
  constructor
  · intro h
    exact powInjective b a c hb ((radixShare_same_iff_power_eq b a c _).1 h)
  · intro h
    exact (radixShare_same_iff_power_eq b a c _).2 (congrArg (fun n => b ^ n) h)

/-- Capacity one collapses all scales, even for unequal exponents. -/
theorem radixShare_one_same (a c : Nat) :
    SameCountingShare (radixShare 1 a Nat.zero_lt_one)
      (radixShare 1 c Nat.zero_lt_one) := by
  apply (radixShare_same_iff_power_eq 1 a c Nat.zero_lt_one).2
  rw [Nat.one_pow, Nat.one_pow]

/-- Semantic compatibility, NOT defined by an exponent equation or by half.
The candidate's scale is squared; the actual geometric mass is composed `q`
times to clear the formal denominator. No numerical amplitude is defined. -/
def QuadraticAmplitudeScaleCompatibleAt (b k p q : Nat) (hb : 0 < b) : Prop :=
  0 < q ∧ SameCountingShare
    (multiplyCountingShares (radixShare b (k * p) hb) (radixShare b (k * p) hb))
    (powerCountingShare (canonicalResidualDepthMass b k hb) q)

/-- Normal form of the semantic requirement, still a comparison of scales. -/
theorem quadraticAmplitudeScaleCompatibleAt_iff_scaleComparison
    (b k p q : Nat) (hb : 0 < b) :
    QuadraticAmplitudeScaleCompatibleAt b k p q hb ↔
      0 < q ∧ SameCountingShare (radixShare b (2 * (k * p)) hb)
        (radixShare b (k * q) hb) := by
  unfold QuadraticAmplitudeScaleCompatibleAt
  rw [radixShare_multiply, canonicalResidualDepthMass_power_eq_radixShare, Nat.two_mul]

/-- Scale injectivity derives the arithmetic equation; it is not assumed. -/
theorem quadraticAmplitudeScaleCompatibleAt_iff_exponentEquation
    (b k p q : Nat) (hb : 1 < b) :
    QuadraticAmplitudeScaleCompatibleAt b k p q (Nat.lt_trans Nat.zero_lt_one hb) ↔
      0 < q ∧ 2 * (k * p) = k * q := by
  constructor
  · intro h
    have hscale := (quadraticAmplitudeScaleCompatibleAt_iff_scaleComparison b k p q _).1 h
    exact ⟨hscale.1, (radixShare_same_iff_exponent_eq b _ _ hb).1 hscale.2⟩
  · intro h
    exact (quadraticAmplitudeScaleCompatibleAt_iff_scaleComparison b k p q _).2
      ⟨h.1, (radixShare_same_iff_exponent_eq b _ _ hb).2 h.2⟩

/-- The exact bridge to the already proved arithmetic interface. -/
theorem quadraticAmplitudeScaleCompatibleAt_iff_carryCompatibleAt
    (b k p q : Nat) (hb : 1 < b) :
    QuadraticAmplitudeScaleCompatibleAt b k p q (Nat.lt_trans Nat.zero_lt_one hb) ↔
      QuadraticCarryCompatibleAt k p q :=
  quadraticAmplitudeScaleCompatibleAt_iff_exponentEquation b k p q hb

/-- Derived geometric mass plus quadratic compatibility selects the formal half
ratio, using the existing rigidity theorem without reproving its arithmetic. -/
theorem canonicalResidualDepthMass_quadraticCompatibility_iff_half
    (b k p q : Nat) (hb : 1 < b) (hk : 0 < k) :
    QuadraticAmplitudeScaleCompatibleAt b k p q (Nat.lt_trans Nat.zero_lt_one hb) ↔
      FormalExponentRepresentsHalf p q :=
  (quadraticAmplitudeScaleCompatibleAt_iff_carryCompatibleAt b k p q hb).trans
    (quadraticCarryCompatibleAt_iff_half k p q hk)

/-- All positive depths give the same result; no new all-order hypothesis. -/
theorem canonicalResidualDepthMass_all_positive_quadraticCompatibility_iff_half
    (b p q : Nat) (hb : 1 < b) :
    (∀ k, 0 < k →
      QuadraticAmplitudeScaleCompatibleAt b k p q (Nat.lt_trans Nat.zero_lt_one hb)) ↔
      FormalExponentRepresentsHalf p q := by
  constructor
  · intro h
    exact (canonicalResidualDepthMass_quadraticCompatibility_iff_half b 1 p q hb
      Nat.zero_lt_one).1 (h 1 Nat.zero_lt_one)
  · intro h k hk
    exact (canonicalResidualDepthMass_quadraticCompatibility_iff_half b k p q hb hk).2 h

/-- The capacity used in the scale can be the SAME first return of the original
trajectory. Nontriviality is supplied by its existing pre-carry theorem. -/
theorem emergentResidualDepthMass_quadraticCompatibility_iff_half
    {Q Local : Type} (trajectory : UnitTrajectory Q)
    (model : AutonomousLocalDynamics trajectory Local)
    {b : Nat} (hcap : EmergentLocalCapacity trajectory model b)
    (hchange : model.observe (trajectory.state 1) ≠ model.observe (trajectory.state 0))
    (k p q : Nat) (hk : 0 < k) :
    QuadraticAmplitudeScaleCompatibleAt b k p q hcap.1.1 ↔
      FormalExponentRepresentsHalf p q :=
  canonicalResidualDepthMass_quadraticCompatibility_iff_half b k p q
    (emergentLocalCapacity_gt_one_of_first_step_changes trajectory model hcap hchange) hk

/-- Depth zero carries no scale information, for ANY positive capacity. -/
theorem quadraticAmplitudeScaleCompatibleAt_zero (b p q : Nat) (hb : 0 < b) :
    QuadraticAmplitudeScaleCompatibleAt b 0 p q hb ↔ 0 < q := by
  constructor
  · exact fun h => h.1
  · intro h
    apply (quadraticAmplitudeScaleCompatibleAt_iff_scaleComparison b 0 p q hb).2
    refine ⟨h, ?_⟩
    rw [Nat.zero_mul, Nat.zero_mul, Nat.mul_zero]
    rfl

/-- Capacity one cannot select the half ratio, even at positive depth. -/
theorem quadraticAmplitudeScaleCompatibleAt_one (k p q : Nat) :
    QuadraticAmplitudeScaleCompatibleAt 1 k p q Nat.zero_lt_one ↔ 0 < q := by
  constructor
  · exact fun h => h.1
  · intro h
    exact (quadraticAmplitudeScaleCompatibleAt_iff_scaleComparison 1 k p q _).2
      ⟨h, radixShare_one_same _ _⟩

/-- A zero denominator is invalid independently of capacity and depth. -/
theorem quadraticAmplitudeScaleCompatibleAt_denominator_zero
    (b k p : Nat) (hb : 0 < b) :
    ¬ QuadraticAmplitudeScaleCompatibleAt b k p 0 hb := by
  intro h
  exact Nat.not_lt_zero 0 h.1

end GeometryOfNumbers.Foundation
