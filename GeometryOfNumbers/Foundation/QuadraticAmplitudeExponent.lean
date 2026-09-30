import Init

/-!
# Discrete quadratic exponent rigidity

The nonnegative exponent is presented by a natural numerator `p` and a positive natural
denominator `q`. No rational quotient, real number, power function, or
distinguished amplitude is defined here. Different pairs may represent the
same exponent; uniqueness is of the formal ratio, not of its presentation.

In exponent units, mass at depth `k` has numerator `k*q`, while the square of
an amplitude with exponent `p/q` has numerator `2*(k*p)`. Compatibility is the
explicit equality of these natural numbers. At positive depth, cancellation yields
`2*p = q`, exactly the cross-multiplication specification of the ratio `1/2`.

This isolates the arithmetic part of
`CarryGeometry.deformedAmplitude_sq_eq_carryMass_iff`, source commit
`3a64ccebfa3849251b2d564432d693ed19a4b74b`. The real-power injectivity bridge
and the derivation of the residual counting mass are NOT proved here.
-/

namespace GeometryOfNumbers.Foundation

set_option autoImplicit false

-- The library's general multiplication associativity currently uses `propext`.
-- This specific doubling identity needs only induction and additive arithmetic.
private theorem mul_double (k p : Nat) : k * (p + p) = k * p + k * p := by
  induction k with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_mul]
  | succ k ih =>
    rw [Nat.succ_mul, Nat.succ_mul, ih]
    calc
      (k * p + k * p) + (p + p) = ((k * p + k * p) + p) + p :=
        (Nat.add_assoc (k * p + k * p) p p).symm
      _ = ((k * p + p) + k * p) + p :=
        congrArg (fun n => n + p) (Nat.add_right_comm (k * p) (k * p) p)
      _ = (k * p + p) + (k * p + p) :=
        Nat.add_assoc (k * p + p) (k * p) p

/-- Formal `p/q = 1/2`, stated without forming any quotient. -/
def FormalExponentRepresentsHalf (p q : Nat) : Prop :=
  0 < q ∧ 2 * p = q

/-- Compatibility of the squared amplitude exponent with the mass exponent at depth `k`. -/
def QuadraticCarryCompatibleAt (k p q : Nat) : Prop :=
  0 < q ∧ 2 * (k * p) = k * q

/-- Compatibility is required only at positive depths. -/
def QuadraticCarryCompatible (p q : Nat) : Prop :=
  ∀ k, 0 < k → QuadraticCarryCompatibleAt k p q

/-- The discrete equation selects the half-exponent at any one positive depth. -/
theorem quadraticExponentEquation_iff_half
    (k p q : Nat) (hk : 0 < k) :
    2 * (k * p) = k * q ↔ 2 * p = q := by
  have hcomm : 2 * (k * p) = k * (2 * p) := by
    rw [Nat.two_mul, Nat.two_mul]
    exact (mul_double k p).symm
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left hk (hcomm.symm.trans h)
  · intro h
    exact hcomm.trans (congrArg (fun n => k * n) h)

/-- A valid formal ratio is compatible at positive depth exactly when it represents half. -/
theorem quadraticCarryCompatibleAt_iff_half
    (k p q : Nat) (hk : 0 < k) :
    QuadraticCarryCompatibleAt k p q ↔ FormalExponentRepresentsHalf p q := by
  constructor
  · intro h
    exact ⟨h.1, (quadraticExponentEquation_iff_half k p q hk).1 h.2⟩
  · intro h
    exact ⟨h.1, (quadraticExponentEquation_iff_half k p q hk).2 h.2⟩

/-- All-positive-depth compatibility has the same unique formal exponent. -/
theorem quadratic_carry_exponent_iff_half (p q : Nat) :
    QuadraticCarryCompatible p q ↔ FormalExponentRepresentsHalf p q := by
  constructor
  · intro h
    exact (quadraticCarryCompatibleAt_iff_half 1 p q (Nat.zero_lt_succ 0)).1
      (h 1 (Nat.zero_lt_succ 0))
  · intro h k hk
    exact (quadraticCarryCompatibleAt_iff_half k p q hk).2 h

/-- At zero depth every valid ratio is compatible; no exponent can be selected there. -/
theorem quadraticCarryCompatibleAt_zero (p q : Nat) (hq : 0 < q) :
    QuadraticCarryCompatibleAt 0 p q := by
  refine ⟨hq, ?_⟩
  change 2 * (0 * p) = 0 * q
  rw [Nat.zero_mul, Nat.mul_zero, Nat.zero_mul]

end GeometryOfNumbers.Foundation
