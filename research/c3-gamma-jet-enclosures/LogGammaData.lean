import RationalGammaData
namespace CarryC3Gamma
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
def logApprox : ℚ := ∑ k ∈ Finset.range 256, (2/3:ℚ)^(k+1)/(k+1)
def logReference : ℚ := 27465307216702742284881130923063/25000000000000000000000000000000
theorem log_rational_box : |logApprox-logReference| ≤ (1/10^32:ℚ) := by
  decide +kernel
theorem rat_abs_cast_le {a b : ℚ} (h : |a| ≤ b) : |(a:ℝ)| ≤ (b:ℝ) := by
  rw [abs_le] at h ⊢
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2
theorem log_three_box : |Real.log 3-(logReference:ℝ)| ≤ (1/10^30:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (by norm_num : |(2/3:ℝ)|<1) 256
  have he : Real.log (1-(2/3:ℝ)) = -Real.log 3 := by
    rw [show 1-(2/3:ℝ)=(3:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he] at h
  have hh : |(logApprox:ℝ)-Real.log 3| ≤ (2/3:ℝ)^257/(1-2/3) := by
    simpa [logApprox,sub_eq_add_neg,abs_of_pos (by norm_num : (0:ℝ)<2/3)] using h
  have hr : |(logApprox:ℝ)-(logReference:ℝ)| ≤ (1/10^32:ℝ) := by
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using
      rat_abs_cast_le log_rational_box
  have hb := (abs_sub_le (Real.log 3) (logApprox:ℝ) (logReference:ℝ)).trans
    (add_le_add (by simpa only [abs_sub_comm] using hh) hr)
  exact hb.trans (by norm_num)
def gammaRealReference : Fin 7 → ℚ := ![36256099082219083119306851/10000000000000000000000000,-76635487085783518164820007/10000000000000000000000000,158931748887619764984312977/10000000000000000000000000,-79873097946774442787554079/2500000000000000000000000,319901465960465041149239047/5000000000000000000000000,-1279918916464207390365214969/10000000000000000000000000,1279983765153172208991458851/5000000000000000000000000]
def gammaRationalPolynomial (r : Fin 7) : ℚ := 3*∑ j ∈ Finset.range (r.val+1),
  (2*logReference)^j/(j.factorial:ℚ)*(-1/2:ℚ)^(r.val-j)*coefficientReference ⟨r.val-j,by omega⟩
theorem gamma_rational_boxes : ∀ r : Fin 7,
    |gammaRationalPolynomial r-gammaRealReference r| ≤ (1/10^25:ℚ) := by
  decide +kernel
theorem coefficient_reference_bound : ∀ r : Fin 7, |coefficientReference r| ≤ (20000:ℚ) := by
  decide +kernel
end CarryC3Gamma
