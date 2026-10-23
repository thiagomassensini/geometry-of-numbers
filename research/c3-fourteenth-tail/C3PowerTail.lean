import DifferenceBounds

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem reciprocal_fourteenth_step (x : ℝ) (hx : 3 < x) :
    1/x^14 ≤ 1/(x-3)^13-1/x^13 := by
  have hx0 : 0 < x := by linarith
  have hy : 0 < x-3 := by linarith
  have hp : (x-3)^13 ≤ (x-3)*x^12 := by
    rw [pow_succ]
    have h := pow_le_pow_left₀ hy.le (show x-3 ≤ x by linarith) 12
    nlinarith
  have hq : 1/x^14 ≤ 3/((x-3)*x^13) := by
    apply (div_le_div_iff₀ (pow_pos hx0 14) (by positivity)).2
    have h := mul_le_mul_of_nonneg_right (show x-3 ≤ 3*x by linarith) (pow_nonneg hx0.le 13)
    convert h using 1 <;> ring
  calc
    1/x^14 ≤ 3/((x-3)*x^13) := hq
    _ = 1/((x-3)*x^12)-1/x^13 := by field_simp; ring
    _ ≤ 1/(x-3)^13-1/x^13 := sub_le_sub_right
      (one_div_le_one_div_of_le (by positivity) hp) _

theorem c3_power14_summable (M : ℕ) :
    Summable (fun k : ℕ => (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^14) :=
  (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (14:ℕ))).comp_injective
    (by intro i j h; dsimp at h; omega)

/-- Rational envelope on the literal step-three C3 address lattice. -/
theorem c3_power14_tail (M : ℕ) (hM : 0 < M) :
    ∑' k : ℕ, (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^14 ≤ 1/(3*(M:ℝ)-1)^13 := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hy : 0 < 3*(M:ℝ)-1 := by linarith
  apply tsum_le_of_sum_le' (by positivity : (0:ℝ)≤1/(3*(M:ℝ)-1)^13)
  intro s
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range s
  have hsum : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^14) ≤
        1/(3*(M:ℝ)-1)^13-1/(3*((N+M:ℕ):ℝ)-1)^13 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hh := reciprocal_fourteenth_step (3*((N:ℝ)+M)+2) (by
        linarith [Nat.cast_nonneg (α:=ℝ) N])
      push_cast at ih ⊢
      rw [show 3*((N:ℝ)+M)+2-3=3*((N:ℝ)+M)-1 by ring] at hh
      rw [show 3*((N:ℝ)+1+M)-1=3*((N:ℝ)+M)+2 by ring]
      linarith
  have hb := hsum N
  have hc : 0 ≤ 1/(3*((N+M:ℕ):ℝ)-1)^13 := by
    have hp : 0 < 3*((N+M:ℕ):ℝ)-1 := by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) N]
    positivity
  calc
    _ ≤ ∑ k ∈ Finset.range N, (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^14 :=
      Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
    _ ≤ _ := by linarith

theorem c3_fourteenth_summable (M : ℕ) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    Summable (fun k : ℕ => ‖fd 14 (fun n => c3Sample n w) (3*(k+M)+2)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => by simpa only [mul_one_div] using native_fd_bound 14 (3*(k+M)+2) (by omega) w hw)
    ((c3_power14_summable M).mul_left (Nat.factorial 14:ℝ))

theorem c3_fourteenth_series_bound (M : ℕ) (hM : 0 < M)
    (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖∑' k : ℕ, fd 14 (fun n => c3Sample n w) (3*(k+M)+2)‖ ≤
      (Nat.factorial 14:ℝ)/(3*(M:ℝ)-1)^13 := by
  apply (norm_tsum_le_tsum_norm (c3_fourteenth_summable M w hw)).trans
  calc
    _ ≤ ∑' k : ℕ, (Nat.factorial 14:ℝ)*((1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^14) :=
      (c3_fourteenth_summable M w hw).tsum_le_tsum
        (fun k => by simpa only [mul_one_div] using native_fd_bound 14 _ (by omega) w hw)
        ((c3_power14_summable M).mul_left _)
    _ = (Nat.factorial 14:ℝ)*(∑' k : ℕ, (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^14) := tsum_mul_left
    _ ≤ (Nat.factorial 14:ℝ)/(3*(M:ℝ)-1)^13 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (c3_power14_tail M hM) (by positivity : (0:ℝ)≤Nat.factorial 14)

theorem native_fd_at_infinity (n M : ℕ) (hn : 0 < n)
    (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    Tendsto (fun N : ℕ => fd n (fun k => c3Sample k w) (3*M+2+3*N)) atTop (nhds 0) := by
  have hnat : Tendsto (fun N : ℕ => 3*M+2+3*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have hc : Tendsto (fun N : ℕ => ((3*M+2+3*N:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnat
  have hpow := (tendsto_inv_atTop_zero.comp hc).pow n
  have hb : Tendsto (fun N : ℕ => (n.factorial:ℝ)/((3*M+2+3*N:ℕ):ℝ)^n) atTop (nhds 0) := by
    simpa only [zero_pow hn.ne',div_eq_mul_inv,inv_pow,mul_zero,Function.comp_def] using hpow.const_mul (n.factorial:ℝ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun N => native_fd_bound n _ (by omega) w hw) hb

theorem c3_boundary_at_infinity (M : ℕ) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    Tendsto (fun N : ℕ => c3Boundary (fun k => c3Sample k w) (3*M+2+3*N)) atTop (nhds 0) := by
  have h (n : ℕ) (hn : 0 < n) := native_fd_at_infinity n M hn w hw
  have h1 := (h 1 (by norm_num)).const_mul (-(1/3:ℂ))
  have h2 := h1.add ((h 2 (by norm_num)).const_mul (1/3:ℂ))
  have h3 := h2.sub ((h 3 (by norm_num)).const_mul (2/9:ℂ))
  have h4 := h3.add ((h 4 (by norm_num)).const_mul (1/9:ℂ))
  have h5 := h4.sub ((h 5 (by norm_num)).const_mul (1/27:ℂ))
  have h7 := h5.add ((h 7 (by norm_num)).const_mul (1/81:ℂ))
  have h8 := h7.sub ((h 8 (by norm_num)).const_mul (1/81:ℂ))
  have h9 := h8.add ((h 9 (by norm_num)).const_mul (2/243:ℂ))
  have h10 := h9.sub ((h 10 (by norm_num)).const_mul (1/243:ℂ))
  have hh := h10.add ((h 11 (by norm_num)).const_mul (1/729:ℂ))
  simpa only [c3Boundary,mul_zero,add_zero,sub_zero] using hh

end
end CarryC3Tail
