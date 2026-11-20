import Mathlib

/-!
Generic, source-independent theorem: a previously positive shifted prefix
controls the lower Euler residual. This does not assume any new Hankel pivot
or completed native positivity in all orders.
-/
namespace TiltSchurPrefix
open Matrix
open scoped BigOperators
noncomputable section

def momentMatrix (m : ℕ → ℝ) (s n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => m (s + i.val + j.val)

def residual (n : ℕ) (v : Fin (n+2) → ℝ) : Fin (n+1) → ℝ :=
  fun i => ((i.val:ℝ) - ((n+1:ℕ):ℝ))*v i.castSucc

def R (m : ℕ → ℝ) (s n : ℕ) (v : Fin (n+2) → ℝ) : ℝ :=
  residual n v ⬝ᵥ (momentMatrix m (s+1) (n+1) *ᵥ residual n v)

theorem R_nonneg (m : ℕ → ℝ) (s n : ℕ)
    (v : Fin (n+2) → ℝ)
    (h : (momentMatrix m (s+1) (n+1)).PosSemidef) :
    0 ≤ R m s n v := by
  exact h.dotProduct_mulVec_nonneg (residual n v)

theorem residual_last (n : ℕ) (v : Fin (n+2) → ℝ) :
    residual n v (Fin.last n) = -v (Fin.last n).castSucc := by
  simp [residual, Fin.val_last]

theorem residual_ne_zero_of_penultimate_ne_zero
    (n : ℕ) (v : Fin (n+2) → ℝ)
    (h : v (Fin.last n).castSucc ≠ 0) :
    residual n v ≠ 0 := by
  intro hz
  have heq : residual n v (Fin.last n) = 0 := by
    rw [hz]
    rfl
  rw [residual_last] at heq
  exact h (neg_eq_zero.mp heq)

theorem R_pos (m : ℕ → ℝ) (s n : ℕ)
    (v : Fin (n+2) → ℝ)
    (h : (momentMatrix m (s+1) (n+1)).PosDef)
    (hv : v (Fin.last n).castSucc ≠ 0) :
    0 < R m s n v := by
  exact h.dotProduct_mulVec_pos (residual_ne_zero_of_penultimate_ne_zero n v hv)


/-- The critical residual is nonzero without a sign assumption on the
penultimate coefficient. Only the first Schur orthogonality row and a
nonzero source moment are needed. -/
theorem residual_ne_zero_of_first_schur_row
    (m : ℕ → ℝ) (s n : ℕ) (v : Fin (n+2) → ℝ)
    (hrow : (∑ i : Fin (n+1), m (s+i.val) * v i.castSucc) +
      m (s+n+1) = 0)
    (hm : m (s+n+1) ≠ 0) :
    residual n v ≠ 0 := by
  intro hz
  have hvzero (i : Fin (n+1)) : v i.castSucc = 0 := by
    have heq : residual n v i = 0 := by rw [hz]; rfl
    change (((i.val:ℝ) - ((n+1:ℕ):ℝ))*v i.castSucc) = 0 at heq
    have hi : (i.val:ℝ) < ((n+1:ℕ):ℝ) := by exact_mod_cast i.isLt
    have hfac : ((i.val:ℝ) - ((n+1:ℕ):ℝ)) ≠ 0 :=
      ne_of_lt (sub_neg.mpr hi)
    exact (mul_eq_zero.mp heq).resolve_left hfac
  have hs : (∑ i : Fin (n+1), m (s+i.val) * v i.castSucc) = 0 := by
    simp [hvzero]
  rw [hs, zero_add] at hrow
  exact hm hrow

theorem R_pos_of_shifted_prefix_and_first_schur_row
    (m : ℕ → ℝ) (s n : ℕ) (v : Fin (n+2) → ℝ)
    (hPrefix : (momentMatrix m (s+1) (n+1)).PosDef)
    (hrow : (∑ i : Fin (n+1), m (s+i.val)*v i.castSucc) +
      m (s+n+1) = 0)
    (hm : m (s+n+1) ≠ 0) :
    0 < R m s n v := by
  exact hPrefix.dotProduct_mulVec_pos
    (residual_ne_zero_of_first_schur_row m s n v hrow hm)

end
end TiltSchurPrefix