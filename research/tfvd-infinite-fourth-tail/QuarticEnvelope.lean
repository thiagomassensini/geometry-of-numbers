import TailAcceleration

namespace CarryFourthTail
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem quartic_reciprocal_step (x : ℝ) (hx : 4 < x) :
    1/x^4 ≤ 1/(12*(x-4)^3)-1/(12*x^3) := by
  have hx0 : 0 < x := by linarith
  have hx4 : 0 < x-4 := by linarith
  have he : 1/(12*(x-4)^3)-1/(12*x^3) =
      (3*x^2-12*x+16)/(3*(x-4)^3*x^3) := by
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hx0 4) (by positivity)).2
  have hp : 3*(x-4)^3 ≤ (3*x^2-12*x+16)*x := by
    nlinarith [sq_nonneg (x-4)]
  convert mul_le_mul_of_nonneg_right hp (pow_nonneg hx0.le 3) using 1 <;> ring

theorem quartic_cell_summable (M : ℕ) :
    Summable (fun k : ℕ => (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^4) :=
  (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (4:ℕ))).comp_injective
    (by intro i j h; dsimp at h; omega)

/-- A cubic tail envelope, obtained by exact rational telescoping. -/
theorem quartic_cell_tail (M : ℕ) (hM : 0 < M) :
    ∑' k : ℕ, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^4 ≤ 1/(12*(4*(M:ℝ)-1)^3) := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : 0 < 12*(4*(M:ℝ)-1)^3 := by
    have hp : 0 < 4*(M:ℝ)-1 := by linarith
    positivity
  apply tsum_le_of_sum_le' (le_of_lt (one_div_pos.mpr hm0))
  intro s
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range s
  have hsum : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^4 ≤
      1/(12*(4*(M:ℝ)-1)^3)-1/(12*(4*(N+M:ℕ)-1)^3) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have he := quartic_reciprocal_step (4*((N:ℝ)+M)+3) (by
        have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
        linarith)
      push_cast at ih ⊢
      rw [show 4*((N:ℝ)+M)+3-4=4*((N:ℝ)+M)-1 by ring] at he
      rw [show 4*((N:ℝ)+1+M)-1=4*((N:ℝ)+M)+3 by ring]
      linarith
  have hb := hsum N
  have hc : (0:ℝ) ≤ 1/(12*(4*(N+M:ℕ)-1)^3) := by
    apply one_div_nonneg.mpr
    have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
    push_cast
    have hp : 0 ≤ 4*((N:ℝ)+M)-1 := by linarith
    positivity
  calc
    ∑ k ∈ s, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^4 ≤
        ∑ k ∈ Finset.range N, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^4 :=
      Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
    _ ≤ 1/(12*(4*(M:ℝ)-1)^3) := by linarith
end
end CarryFourthTail
