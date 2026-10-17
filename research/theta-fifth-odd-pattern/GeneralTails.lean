import ThetaTwenty

/-! Order-dependent estimates for the actual infinite source. The number
of theta modes and a mode's integration cutoff are independent parameters.
These tail bounds do not imply dominance over the source Schur couplings. -/
namespace CarryThetaPattern
open CarryIntegralCertificate CarrySelfAdjointOperator Real Set Filter MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def omittedMajorantRate (M : ℕ) : ℝ := 6*((M+1:ℕ):ℝ)^2-1/2
def omittedMajorantConstant (M : ℕ) : ℝ :=
  2*exp (-3*((M+1:ℕ):ℝ)^2)/(1-exp (-6*((M+1:ℕ):ℝ)))

theorem omittedMajorantRate_pos (M : ℕ) : 0 < omittedMajorantRate M := by
  have hm : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
  unfold omittedMajorantRate
  push_cast
  nlinarith [sq_nonneg (M:ℝ)]

theorem omittedMajorantConstant_pos (M : ℕ) : 0 < omittedMajorantConstant M := by
  apply div_pos (mul_pos (by norm_num) (exp_pos _))
  apply sub_pos.mpr
  exact exp_lt_one_iff.mpr (by
    have hk : (0:ℝ) < ((M+1:ℕ):ℝ) := by positivity
    nlinarith)

theorem theta_mode_after_prefix_le (M n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    XiThetaCosine.thetaTailMode (n+M) u ≤
      exp (-3*((M+1:ℕ):ℝ)^2)*(exp (-6*((M+1:ℕ):ℝ)))^n*
        exp (-omittedMajorantRate M*u) := by
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hK : (0:ℝ) ≤ ((M+1:ℕ):ℝ) := by positivity
  have hs : ((M+1:ℕ):ℝ)^2+2*((M+1:ℕ):ℝ)*(n:ℝ) ≤ ((n+M+1:ℕ):ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg (n:ℝ)]
  have he : 1+2*u ≤ exp (2*u) := by linarith [Real.add_one_le_exp (2*u)]
  have hb : 3*(((M+1:ℕ):ℝ)^2+2*((M+1:ℕ):ℝ)*(n:ℝ))*(1+2*u) ≤
      Real.pi*((n+M+1:ℕ):ℝ)^2*exp (2*u) := by
    gcongr
    exact Real.pi_gt_three.le
  have hc : 0 ≤ ((M+1:ℕ):ℝ)*(n:ℝ)*u := by positivity
  have hbound : 3*((M+1:ℕ):ℝ)^2+6*((M+1:ℕ):ℝ)*(n:ℝ)+
      6*((M+1:ℕ):ℝ)^2*u ≤ Real.pi*((n+M+1:ℕ):ℝ)^2*exp (2*u) := by
    nlinarith only [hb,hc]
  unfold XiThetaCosine.thetaTailMode omittedMajorantRate
  rw [← exp_nat_mul,← exp_add,← exp_add,← exp_add]
  apply exp_le_exp.mpr
  nlinarith only [hbound]

theorem theta_tail_after_prefix_le (M : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    2*(∑' n : ℕ, XiThetaCosine.thetaTailMode (n+M) u) ≤
      omittedMajorantConstant M*exp (-omittedMajorantRate M*u) := by
  have hq0 : 0 ≤ exp (-6*((M+1:ℕ):ℝ)) := (exp_pos _).le
  have hq1 : exp (-6*((M+1:ℕ):ℝ)) < 1 := exp_lt_one_iff.mpr (by
    have hk : (0:ℝ) < ((M+1:ℕ):ℝ) := by positivity
    nlinarith)
  have hh := ((summable_nat_add_iff M).2 (XiThetaCosine.summable_thetaTailMode u)).tsum_le_tsum
    (theta_mode_after_prefix_le M · hu)
    (((summable_geometric_of_lt_one hq0 hq1).mul_left
      (exp (-3*((M+1:ℕ):ℝ)^2))).mul_right (exp (-omittedMajorantRate M*u)))
  rw [tsum_mul_right,tsum_mul_left,tsum_geometric_of_lt_one hq0 hq1] at hh
  calc
    _ ≤ 2*(exp (-3*((M+1:ℕ):ℝ)^2)*(1/(1-exp (-6*((M+1:ℕ):ℝ))))*
        exp (-omittedMajorantRate M*u)) := by
      simpa only [one_div] using mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)
    _ = _ := by unfold omittedMajorantConstant; ring

theorem theta_prefix_split (M : ℕ) (u : ℝ) :
    XiThetaCosine.thetaTail u =
      2*(∑ n ∈ Finset.range M, XiThetaCosine.thetaTailMode n u)+
      2*(∑' n : ℕ, XiThetaCosine.thetaTailMode (n+M) u) := by
  rw [XiThetaCosine.thetaTail_eq_two_mul_tsum]
  have he := Summable.sum_add_tsum_nat_add M (XiThetaCosine.summable_thetaTailMode u)
  rw [← he]
  ring

/-- Actual omitted source, not an independently chosen tail. -/
def weightedOmittedPrefix (M p : ℕ) (u : ℝ) : ℝ :=
  u^p*XiThetaCosine.thetaTail u-∑ m ∈ Finset.range M, u^p*thetaMode m u

theorem weightedOmittedPrefix_eq_tail (M p : ℕ) (u : ℝ) :
    weightedOmittedPrefix M p u = u^p*(2*∑' n : ℕ, XiThetaCosine.thetaTailMode (n+M) u) := by
  unfold weightedOmittedPrefix thetaMode
  rw [theta_prefix_split M]
  simp only [mul_add,Finset.mul_sum]
  ring

theorem weightedOmittedPrefix_bounds (M p : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ weightedOmittedPrefix M p u ∧
      weightedOmittedPrefix M p u ≤ omittedMajorantConstant M*(u^p*exp (-omittedMajorantRate M*u)) := by
  rw [weightedOmittedPrefix_eq_tail]
  constructor
  · apply mul_nonneg (pow_nonneg hu p)
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg (fun n => by unfold XiThetaCosine.thetaTailMode; positivity)
  · exact (mul_le_mul_of_nonneg_left (theta_tail_after_prefix_le M hu)
      (pow_nonneg hu p)).trans_eq (by ring)

theorem integrableOn_weightedOmittedPrefix (M p : ℕ) :
    IntegrableOn (weightedOmittedPrefix M p) (Ioi 0) :=
  (integrableOn_pow_mul_thetaTail p).sub
    (integrable_finsetSum _ (fun m _ => integrableOn_weighted_thetaMode m p))

private theorem power_exp_integral (p : ℕ) (r : ℝ) (hr : 0 < r) :
    (∫ u in Ioi (0:ℝ), u^p*exp (-r*u)) = (p.factorial:ℝ)/r^(p+1) := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (p:ℝ)+1) (r := r) (by positivity) hr
  simp only [add_sub_cancel_right,rpow_natCast] at hh
  rw [Real.Gamma_nat_eq_factorial] at hh
  rw [show (p:ℝ)+1=((p+1:ℕ):ℝ) by push_cast; rfl,rpow_natCast] at hh
  simpa [one_div,inv_pow,div_eq_mul_inv,mul_comm,neg_mul] using hh

/-- All modes beyond ANY prefix, with every order and the infinite tail. -/
theorem integral_weightedOmittedPrefix_bounds (M p : ℕ) :
    0 ≤ (∫ u in Ioi 0, weightedOmittedPrefix M p u) ∧
      (∫ u in Ioi 0, weightedOmittedPrefix M p u) ≤
        omittedMajorantConstant M*(p.factorial:ℝ)/omittedMajorantRate M^(p+1) := by
  have hr := omittedMajorantRate_pos M
  have he : IntegrableOn (fun u : ℝ => u^p*exp (-omittedMajorantRate M*u)) (Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ)) (s := (p:ℝ))
      (b := omittedMajorantRate M)
      (show -1 < (p:ℝ) by have hp := Nat.cast_nonneg (α:=ℝ) p; linarith) (by norm_num) hr
    simpa only [rpow_natCast,rpow_one] using hh
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (weightedOmittedPrefix_bounds M p hu.le).1
  · have hh := integral_mono_ae (integrableOn_weightedOmittedPrefix M p)
      (he.const_mul (omittedMajorantConstant M)) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact (weightedOmittedPrefix_bounds M p hu.le).2)
    rw [integral_const_mul,power_exp_integral p _ hr] at hh
    exact hh.trans_eq (by ring)

/-- A prescribed cutoff, depending on the moment order, makes the retained
mode decay denominator positive in EVERY order. -/
theorem retained_decay_all_orders (m p : ℕ) :
    (33/2:ℝ)+12*(p:ℝ) ≤
      2*thetaArgument m ((p:ℝ)+1)-1/2-(p:ℝ)/((p:ℝ)+1) := by
  have hp : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg p
  have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hs : (1:ℝ) ≤ ((m+1:ℕ):ℝ)^2 := by push_cast; nlinarith [sq_nonneg (m:ℝ)]
  have ha := thetaArgument_coarse_lower m (show (0:ℝ) ≤ (p:ℝ)+1 by positivity)
  have hx := mul_le_mul_of_nonneg_right hs (by positivity : (0:ℝ) ≤ 3*(1+2*((p:ℝ)+1)))
  have hd : (p:ℝ)/((p:ℝ)+1) ≤ 1 :=
    (div_le_iff₀ (by positivity : (0:ℝ) < (p:ℝ)+1)).mpr (by linarith)
  nlinarith only [ha,hx,hd]

theorem retained_tail_bound_all_orders (m p : ℕ) :
    0 ≤ (∫ u in Ioi ((p:ℝ)+1), u^p*thetaMode m u) ∧
      (∫ u in Ioi ((p:ℝ)+1), u^p*thetaMode m u) ≤
        thetaMode m ((p:ℝ)+1)*((p:ℝ)+1)^p/((33/2:ℝ)+12*(p:ℝ)) := by
  have hd := retained_decay_all_orders m p
  have hc : (0:ℝ) < (33/2:ℝ)+12*(p:ℝ) := by positivity
  have hh := thetaMode_weighted_tail_bound m p (by positivity : (0:ℝ) < (p:ℝ)+1)
    (hc.trans_le hd)
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact div_le_div_of_nonneg_left
    (mul_nonneg (thetaMode_nonneg m _) (by positivity)) hc hd

end
end CarryThetaPattern
