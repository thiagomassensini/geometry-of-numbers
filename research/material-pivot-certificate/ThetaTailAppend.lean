namespace CarryMaterialThetaCertificate
open CarrySelfAdjointOperator Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact exponential enclosure used by the rational certificate. -/
def theta_certificate_exp_lower (x : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 40, (x/1024)^i/i.factorial)^1024

def theta_certificate_exp_upper (x : ℝ) : ℝ :=
  ((∑ i ∈ Finset.range 40, (x/1024)^i/i.factorial)+
    (x/1024)^40*41/(Nat.factorial 40*40))^1024

theorem theta_certificate_exp_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1024) :
    theta_certificate_exp_lower x ≤ exp x ∧ exp x ≤ theta_certificate_exp_upper x := by
  have hy : 0 ≤ x/1024 := by positivity
  have hy1 : x/1024 ≤ 1 := by linarith
  have hl := Real.sum_le_exp_of_nonneg hy 40
  have hu := Real.exp_bound' hy hy1 (n := 40) (by norm_num)
  have hu' : exp (x/1024) ≤ (∑ i ∈ Finset.range 40, (x/1024)^i/i.factorial)+
      (x/1024)^40*41/(Nat.factorial 40*40) := by
    convert hu using 1
    norm_num
  have he : exp x = (exp (x/1024))^1024 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  constructor
  · apply pow_le_pow_left₀ _ hl
    exact Finset.sum_nonneg (fun i _ => by positivity)
  · exact pow_le_pow_left₀ (exp_nonneg _) hu' 1024

/-- The omitted fourth and later modes of the original theta source.
No finite-mode replacement of the source is made. -/
theorem theta_mode_after_three_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    XiThetaCosine.thetaTailMode (n+3) u ≤
      exp (-48)*(exp (-24))^n*exp (-95*u) := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hs : (16+8*(n:ℝ)) ≤ (((n+4:ℕ):ℝ)^2) := by
    norm_num only [Nat.cast_add,Nat.cast_ofNat]
    nlinarith [sq_nonneg (n:ℝ)]
  have he : 1+2*u ≤ exp (2*u) := by linarith [Real.add_one_le_exp (2*u)]
  have hp : (3:ℝ)*(16+8*(n:ℝ))*(1+2*u) ≤
      Real.pi*(((n+4:ℕ):ℝ)^2)*exp (2*u) := by
    gcongr
    exact Real.pi_gt_three.le
  have hbound : 48+24*(n:ℝ)+96*u ≤
      Real.pi*(((n+4:ℕ):ℝ)^2)*exp (2*u) := by
    nlinarith [mul_nonneg hn hu]
  unfold XiThetaCosine.thetaTailMode
  rw [← exp_nat_mul,← exp_add,← exp_add,← exp_add]
  apply exp_le_exp.mpr
  have heq : n+3+1=n+4 := by omega
  rw [heq]
  nlinarith

private theorem exp48_lower : (400000000000000000000:ℝ) < exp 48 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 48) 90
  have hr : (400000000000000000000:ℝ) < ∑ i ∈ Finset.range 90,
      (48:ℝ)^i/i.factorial := by norm_num [Finset.sum_range_succ]
  exact hr.trans_le he

/-- Fully kernel-checked pointwise bound for the infinite omitted modes. -/
theorem theta_tail_after_three_le {u : ℝ} (hu : 0 ≤ u) :
    2*(∑' n : ℕ, XiThetaCosine.thetaTailMode (n+3) u) ≤
      (1/100000000000000000000:ℝ)*exp (-95*u) := by
  have hg0 : 0 ≤ exp (-24:ℝ) := (exp_pos _).le
  have hg1 : exp (-24:ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
  have hsum := ((summable_nat_add_iff 3).2 (XiThetaCosine.summable_thetaTailMode u)).tsum_le_tsum
    (theta_mode_after_three_le hu)
    (((summable_geometric_of_lt_one hg0 hg1).mul_left (exp (-48:ℝ))).mul_right (exp (-95*u)))
  rw [tsum_mul_right,tsum_mul_left,tsum_geometric_of_lt_one hg0 hg1] at hsum
  have h24 : exp (-24:ℝ) ≤ 1/2 := by
    rw [exp_neg]
    apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
    linarith [Real.add_one_le_exp (24:ℝ)]
  have hinv : 1/(1-exp (-24:ℝ)) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-exp (-24:ℝ))).mpr
    linarith
  have h48 : 4*exp (-48:ℝ) ≤ (1/100000000000000000000:ℝ) := by
    rw [exp_neg]
    apply (mul_inv_le_iff₀ (exp_pos _)).mpr
    linarith [exp48_lower]
  calc
    _ ≤ 2*(exp (-48:ℝ)*(1/(1-exp (-24:ℝ)))*exp (-95*u)) :=
      by simpa only [one_div] using mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 2)
    _ ≤ (4*exp (-48:ℝ))*exp (-95*u) := by
      have hh := mul_le_mul_of_nonneg_left hinv (exp_pos (-48:ℝ)).le
      nlinarith [mul_nonneg (exp_pos (-95*u)).le (show 0 ≤ 2*exp (-48:ℝ)-exp (-48:ℝ)*(1/(1-exp (-24:ℝ))) by linarith)]
    _ ≤ _ := mul_le_mul_of_nonneg_right h48 (exp_pos _).le

/-- Literal source = the retained three modes + the bounded infinite tail. -/
theorem theta_three_mode_split (u : ℝ) :
    XiThetaCosine.thetaTail u =
      2*(∑ n ∈ Finset.range 3, XiThetaCosine.thetaTailMode n u)+
      2*(∑' n : ℕ, XiThetaCosine.thetaTailMode (n+3) u) := by
  rw [XiThetaCosine.thetaTail_eq_two_mul_tsum]
  have he := Summable.sum_add_tsum_nat_add 3 (XiThetaCosine.summable_thetaTailMode u)
  rw [← he]
  ring

end
end CarryMaterialThetaCertificate
