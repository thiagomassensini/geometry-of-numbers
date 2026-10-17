import ThetaDerivatives

/-! Exact weighted Taylor quadrature for the unchanged source modes. -/
namespace CarryIntegralCertificate
open CarrySelfAdjointOperator Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Positive-coordinate formula for ∫ x^p (x-a)^r. -/
def weightedPowerMass (p r : ℕ) (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p+1),
    (p.choose k:ℝ)*a^(p-k)*(b-a)^(k+r+1)/(k+r+1)

theorem integral_weightedPowerMass (p r : ℕ) (a b : ℝ) :
    (∫ x in a..b, x^p*(x-a)^r) = weightedPowerMass p r a b := by
  have he (x : ℝ) : x^p*(x-a)^r =
      ∑ k ∈ Finset.range (p+1), (p.choose k:ℝ)*a^(p-k)*(x-a)^(k+r) := by
    have h := add_pow (x-a) a p
    rw [show x-a+a=x by ring] at h
    rw [h,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (by apply Continuous.intervalIntegrable; fun_prop))]
  unfold weightedPowerMass
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^(k+r)),integral_pow]
  simp only [sub_self,zero_pow (by omega : k+r+1 ≠ 0),sub_zero]
  push_cast
  ring

theorem weightedPowerMass_nonneg (p r : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : 0 ≤ weightedPowerMass p r a b := by
  unfold weightedPowerMass
  apply Finset.sum_nonneg
  intro k _
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha _))
    (pow_nonneg (sub_nonneg.mpr hab) _)) (by positivity)

def weightedTaylorMass (m n p : ℕ) (a b : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (n+1),
    thetaModeDerivative m r a/(r.factorial:ℝ)*weightedPowerMass p r a b

theorem integral_weightedTaylor (m n p : ℕ) (a b : ℝ) (hab : a < b) :
    (∫ x in a..b, x^p*taylorWithinEval (thetaMode m) n (Icc a b) a x) =
      weightedTaylorMass m n p a b := by
  simp_rw [thetaMode_taylor_eq_sum m n a b _ hab,Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun r _ =>
    (by apply Continuous.intervalIntegrable; fun_prop))]
  unfold weightedTaylorMass
  apply Finset.sum_congr rfl
  intro r _
  rw [show (fun x : ℝ => x^p*(thetaModeDerivative m r a/(r.factorial:ℝ)*(x-a)^r)) =
    (fun x => (thetaModeDerivative m r a/(r.factorial:ℝ))*(x^p*(x-a)^r)) by
      funext x; ring,intervalIntegral.integral_const_mul,integral_weightedPowerMass]

/-- The source integral is enclosed by its signed Taylor mass plus/minus
an explicit, conservatively normalized error. -/
theorem thetaMode_weighted_cell_bounds (m n p : ℕ) (a b C : ℝ)
    (ha : 0 ≤ a) (hab : a < b)
    (hC : ∀ x ∈ Icc a b, |thetaModeDerivative m (n+1) x| ≤ C) :
    weightedTaylorMass m n p a b-C/(n.factorial:ℝ)*weightedPowerMass p (n+1) a b ≤
      (∫ x in a..b, x^p*thetaMode m x) ∧
    (∫ x in a..b, x^p*thetaMode m x) ≤
      weightedTaylorMass m n p a b+C/(n.factorial:ℝ)*weightedPowerMass p (n+1) a b := by
  have hf : Continuous (thetaMode m) := (contDiff_thetaMode m (n+1)).continuous
  have ht : Continuous (fun x => taylorWithinEval (thetaMode m) n (Icc a b) a x) := by
    simp_rw [thetaMode_taylor_eq_sum m n a b _ hab]
    fun_prop
  have hi : IntervalIntegrable (fun x => x^p*thetaMode m x) volume a b :=
    (continuous_id.pow p |>.mul hf).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun x => x^p*taylorWithinEval (thetaMode m) n (Icc a b) a x)
      volume a b := (continuous_id.pow p |>.mul ht).intervalIntegrable _ _
  have hk : IntervalIntegrable (fun x : ℝ => C/(n.factorial:ℝ)*(x^p*(x-a)^(n+1)))
      volume a b := by apply Continuous.intervalIntegrable; fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :=
    mul_le_mul_of_nonneg_left (abs_le.mp (thetaMode_taylor_remainder m n a b C x hab hx hC)).1
      (pow_nonneg (ha.trans hx.1) p)
  have hpoint' (x : ℝ) (hx : x ∈ Icc a b) :=
    mul_le_mul_of_nonneg_left (abs_le.mp (thetaMode_taylor_remainder m n a b C x hab hx hC)).2
      (pow_nonneg (ha.trans hx.1) p)
  have he : (∫ x in a..b, C/(n.factorial:ℝ)*(x^p*(x-a)^(n+1))) =
      C/(n.factorial:ℝ)*weightedPowerMass p (n+1) a b := by
    rw [intervalIntegral.integral_const_mul,integral_weightedPowerMass]
  constructor
  · rw [← integral_weightedTaylor m n p a b hab,← he,← intervalIntegral.integral_sub hj hk]
    apply intervalIntegral.integral_mono_on hab.le (hj.sub hk) hi
    intro x hx
    have h := hpoint x hx
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  · rw [← integral_weightedTaylor m n p a b hab,← he,← intervalIntegral.integral_add hj hk]
    apply intervalIntegral.integral_mono_on hab.le hi (hj.add hk)
    intro x hx
    have h := hpoint' x hx
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]

end
end CarryIntegralCertificate
