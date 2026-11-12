import C3Power26Tail

namespace CarryC3Tail

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem c3_twenty_sixth_summable (M : ℕ) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    Summable (fun k : ℕ => ‖fd 26 (fun n => c3Sample n w) (3*(k+M)+2)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => by simpa only [mul_one_div] using
      native_fd_bound 26 (3*(k+M)+2) (by omega) w hw)
    ((c3_power26_summable M).mul_left (Nat.factorial 26:ℝ))

theorem c3_twenty_sixth_series_bound (M : ℕ) (hM : 0 < M)
    (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖∑' k : ℕ, fd 26 (fun n => c3Sample n w) (3*(k+M)+2)‖ ≤
      (Nat.factorial 26:ℝ)/(3*(M:ℝ)-1)^25 := by
  apply (norm_tsum_le_tsum_norm (c3_twenty_sixth_summable M w hw)).trans
  calc
    _ ≤ ∑' k : ℕ, (Nat.factorial 26:ℝ)*
        ((1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^26) :=
      (c3_twenty_sixth_summable M w hw).tsum_le_tsum
        (fun k => by simpa only [mul_one_div] using
          native_fd_bound 26 _ (by omega) w hw)
        ((c3_power26_summable M).mul_left _)
    _ = (Nat.factorial 26:ℝ)*
        (∑' k : ℕ, (1:ℝ)/((3*(k+M)+2:ℕ):ℝ)^26) := tsum_mul_left
    _ ≤ (Nat.factorial 26:ℝ)/(3*(M:ℝ)-1)^25 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (c3_power26_tail M hM) (by positivity : (0:ℝ)≤Nat.factorial 26)

/-- Rational budget for the order-26 series after the original completion
multiplier and Cauchy factor at 48 cells, through coefficient c₆. -/
theorem c3_power26_tail48_budget (k : ℕ) (hk : k ≤ 6) :
    (96*(Nat.factorial 26:ℝ)*4^(2*k))/(729^2*(143:ℝ)^25) ≤ (1/10^20:ℝ) := by
  have hp : (4:ℝ)^(2*k) ≤ 4^12 := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ (96*(Nat.factorial 26:ℝ)*4^12)/(729^2*(143:ℝ)^25) := by
      apply div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (1/10^20:ℝ) := by norm_num [Nat.factorial]

end
end CarryC3Tail
