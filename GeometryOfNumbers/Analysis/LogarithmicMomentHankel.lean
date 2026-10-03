import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-!
# Logarithmic moments and the exact Hankel tower

Let

`Phi(u) = sum phi_n u^n`

be the even cutoff-completed native characteristic and let

`q(u) = -Phi'(u) / Phi(u) = sum h_n u^n`.

The coefficient identity `q Phi = -Phi'` gives the exact recurrence used by
the reference implementation.  The moments `h_n` then define the Gram and
shifted Hankel matrices.  Their passage from order `N+1` to order `N` is
literal principal-submatrix restriction; no convergence claim or zero-height
input is involved.
-/

open scoped BigOperators

namespace GeometryOfNumbers.Analysis

noncomputable section

/-- Coefficient form of `q * Phi = -Phi'`.  This relation is division-free
and therefore keeps the normalization `phi 0 ≠ 0` separate. -/
def IsLogDerivativeMomentSequence
    (phi moments : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    phi 0 * moments n +
        ∑ k ∈ Finset.range n, moments k * phi (n - k) =
      -(((n + 1 : ℕ) : ℝ) * phi (n + 1))

/-- Solving the division-free coefficient identity reproduces exactly the
recursive formula used by `logarithmic_moments` in the reference script. -/
theorem logarithmicMoment_eq
    {phi moments : ℕ → ℝ}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (n : ℕ) :
    moments n =
      (-(((n + 1 : ℕ) : ℝ) * phi (n + 1)) -
          ∑ k ∈ Finset.range n, moments k * phi (n - k)) /
        phi 0 := by
  apply (eq_div_iff hphi).2
  calc
    moments n * phi 0 = phi 0 * moments n := mul_comm _ _
    _ = -(((n + 1 : ℕ) : ℝ) * phi (n + 1)) -
          ∑ k ∈ Finset.range n, moments k * phi (n - k) := by
      linarith [hrel n]

/-- The completed characteristic leaves no freedom in its logarithmic moment
sequence.  Once `phi 0` is nonzero, any two sequences satisfying the
division-free identity `q * Phi = -Phi'` agree in every order. -/
theorem IsLogDerivativeMomentSequence.unique
    {phi moments moments' : ℕ → ℝ}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (hrel' : IsLogDerivativeMomentSequence phi moments') :
    moments = moments' := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hsum :
          ∑ k ∈ Finset.range n, moments k * phi (n - k) =
            ∑ k ∈ Finset.range n, moments' k * phi (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      have hn : phi 0 * moments n = phi 0 * moments' n := by
        linarith [hrel n, hrel' n]
      exact mul_left_cancel₀ hphi hn

/-- Pointwise form of logarithmic-moment uniqueness. -/
theorem logarithmicMoment_eq_of_two_relations
    {phi moments moments' : ℕ → ℝ}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (hrel' : IsLogDerivativeMomentSequence phi moments')
    (n : ℕ) :
    moments n = moments' n := by
  rw [hrel.unique hphi hrel']

/-- Order-`N` Hankel Gram matrix `G_N = (h_(i+j))`. -/
def hankelGram (moments : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ moments ((i : ℕ) + (j : ℕ))

/-- Shifted order-`N` Hankel matrix `K_N = (h_(i+j+1))`. -/
def shiftedHankel (moments : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ moments ((i : ℕ) + (j : ℕ) + 1)

@[simp] theorem hankelGram_apply
    (moments : ℕ → ℝ) (N : ℕ) (i j : Fin N) :
    hankelGram moments N i j = moments ((i : ℕ) + (j : ℕ)) :=
  rfl

@[simp] theorem shiftedHankel_apply
    (moments : ℕ → ℝ) (N : ℕ) (i j : Fin N) :
    shiftedHankel moments N i j =
      moments ((i : ℕ) + (j : ℕ) + 1) :=
  rfl

/-- Every finite Hankel Gram section is symmetric. -/
theorem hankelGram_isSymm (moments : ℕ → ℝ) (N : ℕ) :
    (hankelGram moments N).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [hankelGram, add_comm]

/-- Every shifted Hankel section is symmetric. -/
theorem shiftedHankel_isSymm (moments : ℕ → ℝ) (N : ℕ) :
    (shiftedHankel moments N).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [shiftedHankel, add_comm]

/-- The order-`N` Gram matrix is literally the leading principal section of
the order-`N+1` Gram matrix. -/
@[simp] theorem hankelGram_succ_principal
    (moments : ℕ → ℝ) (N : ℕ) :
    (hankelGram moments (N + 1)).submatrix
        Fin.castSucc Fin.castSucc =
      hankelGram moments N := by
  rfl

/-- The shifted Hankel matrices obey the same exact projective law. -/
@[simp] theorem shiftedHankel_succ_principal
    (moments : ℕ → ℝ) (N : ℕ) :
    (shiftedHankel moments (N + 1)).submatrix
        Fin.castSucc Fin.castSucc =
      shiftedHankel moments N := by
  rfl

end

end GeometryOfNumbers.Analysis
