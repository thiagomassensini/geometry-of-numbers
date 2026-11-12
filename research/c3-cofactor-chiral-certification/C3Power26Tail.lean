import C3Power26Step

namespace CarryC3Tail

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

theorem c3_power26_summable (M : ℕ) :
    Summable (fun k : ℕ => (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^26) :=
  (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (26:ℕ))).comp_injective
    (by intro i j h; dsimp at h; omega)

/-- Rational envelope on the original step-three address lattice for order 26. -/
theorem c3_power26_tail (M : ℕ) (hM : 0 < M) :
    ∑' k : ℕ, (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^26 ≤ 1/(3*(M:ℝ)-1)^25 := by
  have hy : 0 < 3*(M:ℝ)-1 := by
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
    linarith
  apply tsum_le_of_sum_le' (by positivity : (0:ℝ)≤1/(3*(M:ℝ)-1)^25)
  intro s
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range s
  have hsum : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^26) ≤
        1/(3*(M:ℝ)-1)^25-1/(3*((N+M:ℕ):ℝ)-1)^25 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hh := reciprocal_twenty_sixth_step (3*((N:ℝ)+M)+2) (by
        linarith [Nat.cast_nonneg (α:=ℝ) N])
      push_cast at ih ⊢
      rw [show 3*((N:ℝ)+M)+2-3=3*((N:ℝ)+M)-1 by ring] at hh
      rw [show 3*((N:ℝ)+1+M)-1=3*((N:ℝ)+M)+2 by ring]
      calc
        _ ≤ (1/(3*(M:ℝ)-1)^25-1/(3*((N:ℝ)+M)-1)^25) +
            (1/(3*((N:ℝ)+M)-1)^25-1/(3*((N:ℝ)+M)+2)^25) := add_le_add ih hh
        _ = _ := by ring
  have hb := hsum N
  have hc : 0 ≤ 1/(3*((N+M:ℕ):ℝ)-1)^25 := by
    have hp : 0 < 3*((N+M:ℕ):ℝ)-1 := by
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) N]
    positivity
  calc
    _ ≤ ∑ k ∈ Finset.range N, (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^26 :=
      Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
    _ ≤ _ := by linarith

end
end CarryC3Tail
