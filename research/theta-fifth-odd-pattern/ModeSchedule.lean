import GeneralTails

/-! Actual omitted-source control with order-dependent mode counts. A
prescribed positive tolerance is numerical accuracy data, not a source
positivity margin. No uniform fixed count for all orders is asserted. -/
namespace CarryThetaPattern
open CarryIntegralCertificate CarrySelfAdjointOperator Real Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem omittedMajorantConstant_geometric (M : ℕ) :
    omittedMajorantConstant M ≤ 4*exp (-3*((M+1:ℕ):ℝ)) := by
  have hk : (1:ℝ) ≤ ((M+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  have hq : exp (-6*((M+1:ℕ):ℝ)) ≤ 1/2 := by
    rw [show (-6:ℝ)*((M+1:ℕ):ℝ) = -(6*((M+1:ℕ):ℝ)) by ring,exp_neg]
    apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
    nlinarith [Real.add_one_le_exp (6*((M+1:ℕ):ℝ))]
  have he : exp (-3*((M+1:ℕ):ℝ)^2) ≤ exp (-3*((M+1:ℕ):ℝ)) := by
    apply exp_le_exp.mpr
    nlinarith [sq_nonneg (((M+1:ℕ):ℝ)-1)]
  calc
    _ ≤ (2*exp (-3*((M+1:ℕ):ℝ)^2))/(1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ = 4*exp (-3*((M+1:ℕ):ℝ)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by norm_num)

theorem omittedPrefix_geometric_bound (M p : ℕ) :
    (∫ u in Ioi 0, weightedOmittedPrefix M p u) ≤
      4*(p.factorial:ℝ)*(exp (-3:ℝ))^(M+1) := by
  have hr : (1:ℝ) ≤ omittedMajorantRate M := by
    have hm : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
    unfold omittedMajorantRate
    push_cast
    nlinarith [sq_nonneg (M:ℝ)]
  have hd : (1:ℝ) ≤ omittedMajorantRate M^(p+1) := one_le_pow₀ hr
  have hn : (0:ℝ) ≤ omittedMajorantConstant M*(p.factorial:ℝ) :=
    mul_nonneg (omittedMajorantConstant_pos M).le (by positivity)
  have he : exp (-3*((M+1:ℕ):ℝ)) = (exp (-3:ℝ))^(M+1) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ omittedMajorantConstant M*(p.factorial:ℝ)/omittedMajorantRate M^(p+1) :=
      (integral_weightedOmittedPrefix_bounds M p).2
    _ ≤ omittedMajorantConstant M*(p.factorial:ℝ) :=
      (div_le_iff₀ (pow_pos (omittedMajorantRate_pos M) _)).mpr (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hn)
    _ ≤ (4*exp (-3*((M+1:ℕ):ℝ)))*(p.factorial:ℝ) :=
      mul_le_mul_of_nonneg_right (omittedMajorantConstant_geometric M) (by positivity)
    _ = _ := by rw [he]; ring

theorem omittedPrefix_integral_tendsto_zero (p : ℕ) :
    Tendsto (fun M => ∫ u in Ioi 0, weightedOmittedPrefix M p u) atTop (nhds 0) := by
  have hq0 : (0:ℝ) ≤ exp (-3:ℝ) := (exp_pos _).le
  have hq1 : exp (-3:ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hb : Tendsto (fun M : ℕ => 4*(p.factorial:ℝ)*(exp (-3:ℝ))^(M+1)) atTop (nhds 0) := by
    simpa only [pow_succ,zero_mul,mul_zero] using
      (ht.mul_const (exp (-3:ℝ))).const_mul (4*(p.factorial:ℝ))
  exact squeeze_zero (fun M => (integral_weightedOmittedPrefix_bounds M p).1)
    (fun M => omittedPrefix_geometric_bound M p) hb

/-- Each order has its own desired accuracy and an increasing mode count.
This does NOT produce the missing positive Schur margins. -/
theorem exists_monotone_common_mode_schedule (tol : ℕ → ℝ) (htol : ∀ n, 0 < tol n) :
    ∃ K : ℕ → ℕ, StrictMono K ∧ ∀ n j, j ≤ n →
      (∫ u in Ioi 0, weightedOmittedPrefix (K n) (2*j) u) < tol j := by
  have he (n : ℕ) : ∃ J : ℕ, ∀ M ≥ J,
      (∫ u in Ioi 0, weightedOmittedPrefix M (2*n) u) < tol n :=
    eventually_atTop.mp ((tendsto_order.mp (omittedPrefix_integral_tendsto_zero (2*n))).2
      (tol n) (htol n))
  choose J hJ using he
  let K : ℕ → ℕ := fun n => n+Finset.sup (Finset.range (n+1)) J
  have hK : StrictMono K := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hs : Finset.sup (Finset.range (n+1)) J ≤ Finset.sup (Finset.range (n+1+1)) J :=
      Finset.sup_mono (Finset.range_mono (by omega))
    dsimp [K]
    omega
  refine ⟨K,hK,?_⟩
  intro n j hj
  apply hJ j (K n)
  have hh : J j ≤ Finset.sup (Finset.range (n+1)) J :=
    Finset.le_sup (f := J) (by simp only [Finset.mem_range]; omega)
  dsimp [K]
  omega

theorem exists_monotone_mode_schedule (tol : ℕ → ℝ) (htol : ∀ n, 0 < tol n) :
    ∃ K : ℕ → ℕ, StrictMono K ∧ ∀ n,
      (∫ u in Ioi 0, weightedOmittedPrefix (K n) (2*n) u) < tol n := by
  obtain ⟨K,hK,hB⟩ := exists_monotone_common_mode_schedule tol htol
  exact ⟨K,hK,fun n => hB n n le_rfl⟩

end
end CarryThetaPattern
