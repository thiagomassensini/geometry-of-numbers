import GeometryOfNumbers.Analysis.QuadraticReflection

/-!
# An explicit semantic compatibility for integer offsets

Composition in the offset domain is required to be transported to multiplication.
This is a NEW specification, not a consequence of the residual tower or of
reflection alone. The positive unit step remains free. Classification uses
discrete induction and integer powers, never an analytic parametrization.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

def IsPositiveMultiplicativeOffsetTransport (Q : Int → ℝ) : Prop :=
  Q 0 = 1 ∧ (∀ a b, Q (a + b) = Q a * Q b) ∧ 0 < Q 1

theorem multiplicativeOffsetTransport_zero {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) : Q 0 = 1 := hQ.1

theorem multiplicativeOffsetTransport_add {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (a b : Int) :
    Q (a + b) = Q a * Q b := hQ.2.1 a b

theorem multiplicativeOffsetTransport_product_neg {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (a : Int) :
    Q a * Q (-a) = 1 := by
  rw [← multiplicativeOffsetTransport_add hQ, add_neg_cancel,
    multiplicativeOffsetTransport_zero hQ]

theorem multiplicativeOffsetTransport_ne_zero {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (a : Int) : Q a ≠ 0 := by
  intro hz
  have hp := multiplicativeOffsetTransport_product_neg hQ a
  rw [hz, zero_mul] at hp
  exact zero_ne_one hp

theorem multiplicativeOffsetTransport_neg {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (a : Int) :
    Q (-a) = (Q a)⁻¹ := by
  apply mul_left_cancel₀ (multiplicativeOffsetTransport_ne_zero hQ a)
  rw [multiplicativeOffsetTransport_product_neg hQ,
    mul_inv_cancel₀ (multiplicativeOffsetTransport_ne_zero hQ a)]

theorem multiplicativeOffsetTransport_natCast {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (r : Nat) :
    Q (r : Int) = (Q 1) ^ r := by
  induction r with
  | zero => simpa using multiplicativeOffsetTransport_zero hQ
  | succ r ih =>
    rw [Nat.cast_succ, multiplicativeOffsetTransport_add hQ, ih, pow_succ]

theorem multiplicativeOffsetTransport_neg_natCast {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (r : Nat) :
    Q (-(r : Int)) = ((Q 1) ^ r)⁻¹ := by
  rw [multiplicativeOffsetTransport_neg hQ, multiplicativeOffsetTransport_natCast hQ]

theorem multiplicativeOffsetTransport_eq_zpow {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (a : Int) :
    Q a = (Q 1) ^ a := by
  cases a with
  | ofNat r => simpa using multiplicativeOffsetTransport_natCast hQ r
  | negSucc r =>
    change Q (-((r + 1 : Nat) : Int)) = _
    rw [multiplicativeOffsetTransport_neg_natCast hQ]
    rfl

theorem multiplicativeOffsetTransport_pos {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (a : Int) : 0 < Q a := by
  cases a with
  | ofNat r =>
    change 0 < Q (r : Int)
    rw [multiplicativeOffsetTransport_natCast hQ]
    exact pow_pos hQ.2.2 r
  | negSucc r =>
    change 0 < Q (-((r + 1 : Nat) : Int))
    rw [multiplicativeOffsetTransport_neg_natCast hQ]
    exact inv_pos.mpr (pow_pos hQ.2.2 (r + 1))

def canonicalMultiplicativeOffsetTransport (rho : ℝ) (a : Int) : ℝ := rho ^ a

theorem canonicalMultiplicativeOffsetTransport_isPositive {rho : ℝ} (hrho : 0 < rho) :
    IsPositiveMultiplicativeOffsetTransport (canonicalMultiplicativeOffsetTransport rho) := by
  refine ⟨?_, ?_, ?_⟩
  · exact zpow_zero rho
  · intro a b
    exact zpow_add₀ (ne_of_gt hrho) a b
  · simpa [canonicalMultiplicativeOffsetTransport] using hrho

theorem canonicalMultiplicativeOffsetTransport_one (rho : ℝ) :
    canonicalMultiplicativeOffsetTransport rho 1 = rho := zpow_one rho

theorem multiplicativeOffsetTransport_eq_canonical {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) :
    Q = canonicalMultiplicativeOffsetTransport (Q 1) := by
  funext a
  exact multiplicativeOffsetTransport_eq_zpow hQ a

theorem multiplicativeOffsetTransport_unique {Q P : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q)
    (hP : IsPositiveMultiplicativeOffsetTransport P) (hstep : Q 1 = P 1) : Q = P := by
  rw [multiplicativeOffsetTransport_eq_canonical hQ,
    multiplicativeOffsetTransport_eq_canonical hP, hstep]

theorem existsUnique_multiplicativeOffsetTransport {rho : ℝ} (hrho : 0 < rho) :
    ∃ Q : Int → ℝ, IsPositiveMultiplicativeOffsetTransport Q ∧ Q 1 = rho ∧
      ∀ P, IsPositiveMultiplicativeOffsetTransport P → P 1 = rho → P = Q := by
  refine ⟨canonicalMultiplicativeOffsetTransport rho,
    canonicalMultiplicativeOffsetTransport_isPositive hrho,
    canonicalMultiplicativeOffsetTransport_one rho, ?_⟩
  intro P hP hstep
  exact multiplicativeOffsetTransport_unique hP
    (canonicalMultiplicativeOffsetTransport_isPositive hrho)
    (hstep.trans (canonicalMultiplicativeOffsetTransport_one rho).symm)

end

end GeometryOfNumbers.Analysis
