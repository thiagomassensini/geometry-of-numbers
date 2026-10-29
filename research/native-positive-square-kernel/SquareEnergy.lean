import GeometryOfNumbers.Analysis.SymmetricKrylovHankel
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace CarryPositiveSquare
open GeometryOfNumbers.Analysis
open scoped InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The ordinary adjoint square of the supplied operator, in its old metric. -/
def gramOperator (B : H →L[ℝ] K) : H →L[ℝ] H := B.adjoint.comp B

/-- Source-weighted moments proposed in the question; no native equality is assumed. -/
def weightedMoment (A : H →L[ℝ] H) (v : H) (n : ℕ) : ℝ :=
  inner ℝ v ((A.toLinearMap^(n+1)) v)

theorem gramOperator_pairing (B : H →L[ℝ] K) (x y : H) :
    inner ℝ (gramOperator B x) y = inner ℝ (B x) (B y) :=
  B.adjoint_inner_left _ _

theorem gramOperator_symmetric (B : H →L[ℝ] K) : (gramOperator B).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (gramOperator B x) y = inner ℝ x (gramOperator B y)
  calc
    _ = inner ℝ (B x) (B y) := gramOperator_pairing B x y
    _ = inner ℝ (B y) (B x) := real_inner_comm _ _
    _ = inner ℝ (gramOperator B y) x := (gramOperator_pairing B y x).symm
    _ = _ := real_inner_comm _ _

/-- Both arguments come from the same existing B and source. -/
theorem weighted_even_pairing (B : H →L[ℝ] K) (v : H) (i j : ℕ) :
    inner ℝ (B (((gramOperator B).toLinearMap^i) v)) (B (((gramOperator B).toLinearMap^j) v)) =
      weightedMoment (gramOperator B) v (i+j) := by
  rw [← gramOperator_pairing]
  have hs := symmetricKrylov_inner_add (gramOperator B).toLinearMap
    (gramOperator_symmetric B) v (i+1) j
  rw [pow_succ', Module.End.mul_apply] at hs
  simpa [weightedMoment, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

theorem weighted_odd_pairing (B : H →L[ℝ] K) (v : H) (i j : ℕ) :
    inner ℝ (((gramOperator B).toLinearMap^(i+1)) v) (((gramOperator B).toLinearMap^(j+1)) v) =
      weightedMoment (gramOperator B) v (i+j+1) := by
  have hs := symmetricKrylov_inner_add (gramOperator B).toLinearMap
    (gramOperator_symmetric B) v (i+1) (j+1)
  simpa [weightedMoment, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

theorem weighted_even_gram (B : H →L[ℝ] K) (v : H) :
    IsMomentGramRepresentation (weightedMoment (gramOperator B) v)
      (fun i => B (((gramOperator B).toLinearMap^i) v)) := by
  intro i j
  exact (weighted_even_pairing B v i j).symm

theorem weighted_odd_gram (B : H →L[ℝ] K) (v : H) :
    IsShiftedMomentGramRepresentation (weightedMoment (gramOperator B) v)
      (fun i => ((gramOperator B).toLinearMap^(i+1)) v) := by
  intro i j
  exact (weighted_odd_pairing B v i j).symm

/-- An actual lower frame bound forces a low-moment inequality, independently
of any normalization of v and without introducing spectral inputs. -/
theorem weighted_moment_gap (B : H →L[ℝ] K) (v : H) (a : ℝ)
    (hb : ∀ x : H, a*‖x‖^2 ≤ ‖B x‖^2) :
    a*weightedMoment (gramOperator B) v 1 ≤ weightedMoment (gramOperator B) v 2 := by
  have h1 := weighted_odd_pairing B v 0 0
  have h2 := weighted_even_pairing B v 1 1
  norm_num only [Nat.zero_add, Nat.reduceAdd, pow_one] at h1 h2
  rw [real_inner_self_eq_norm_sq] at h1 h2
  rw [← h1, ← h2]
  exact hb (gramOperator B v)

end
end CarryPositiveSquare
