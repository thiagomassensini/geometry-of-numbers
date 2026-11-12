import C3Acceleration48

namespace CarryC3Tail

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Telescoping step for the 26th-difference power tail. -/
theorem reciprocal_twenty_sixth_step (x : ℝ) (hx : 3 < x) :
    1/x^26 ≤ 1/(x-3)^25 - 1/x^25 := by
  have hx0 : 0 < x := by linarith
  have hpow : (x-3)^25 ≤ (x-3)*x^24 := by
    calc
      (x-3)^25 = (x-3)^24*(x-3) := by rw [pow_succ]
      _ = (x-3)*(x-3)^24 := by ring
      _ ≤ (x-3)*x^24 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ x-3) (by linarith) 24) (by linarith)
  have hscale : (x-3)*x^25 ≤ 3*x^26 := by
    have hlin : x-3 ≤ 3*x := by linarith
    have hmul := mul_le_mul_of_nonneg_right hlin (pow_nonneg hx0.le 25)
    calc
      (x-3)*x^25 ≤ (3*x)*x^25 := hmul
      _ = 3*x^26 := by rw [pow_succ]; ring
  have hfirst : 1/x^26 ≤ 3/((x-3)*x^25) := by
    apply (div_le_div_iff₀ (pow_pos hx0 26) (by positivity)).2
    simpa only [one_mul] using hscale
  calc
    1/x^26 ≤ 3/((x-3)*x^25) := hfirst
    _ = 1/((x-3)*x^24)-1/x^25 := by
      field_simp [ne_of_gt (by linarith : (0:ℝ)<x-3)]
      ring
    _ ≤ 1/(x-3)^25-1/x^25 := by
      exact sub_le_sub_right
        (one_div_le_one_div_of_le (by positivity) hpow) _

end
end CarryC3Tail
