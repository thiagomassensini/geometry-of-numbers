import WeightedQuadrature
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Infinite tails of the retained theta modes, with the source normalization
and all weighted moments preserved. -/
namespace CarryIntegralCertificate
open CarrySelfAdjointOperator Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem thetaMode_eq_exp (m : ℕ) (u : ℝ) :
    thetaMode m u = 2*exp (u/2-thetaArgument m u) := by
  unfold thetaMode XiThetaCosine.thetaTailMode thetaArgument
  rw [mul_assoc,← exp_add]
  congr 2
  ring

theorem thetaArgument_add (m : ℕ) (L v : ℝ) :
    thetaArgument m (L+v) = thetaArgument m L*exp (2*v) := by
  unfold thetaArgument
  rw [show 2*(L+v)=2*L+2*v by ring,exp_add]
  ring

/-- Decay from a genuine source endpoint, with no new tail amplitude. -/
theorem thetaMode_shift_le (m : ℕ) (L v : ℝ) (_hv : 0 ≤ v) :
    thetaMode m (L+v) ≤ thetaMode m L*exp (-(2*thetaArgument m L-1/2)*v) := by
  rw [thetaMode_eq_exp,thetaMode_eq_exp,thetaArgument_add,mul_assoc,← exp_add]
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num : (0:ℝ) ≤ 2)
  have hq : 0 ≤ thetaArgument m L := by unfold thetaArgument; positivity
  have he : 1+2*v ≤ exp (2*v) := by linarith [Real.add_one_le_exp (2*v)]
  nlinarith [mul_le_mul_of_nonneg_left he hq]

theorem shifted_power_le (p : ℕ) {L v : ℝ} (hL : 0 < L) (hv : 0 ≤ v) :
    (L+v)^p ≤ L^p*exp ((p:ℝ)/L*v) := by
  have he : L+v ≤ L*exp (v/L) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v/L)) hL.le
    field_simp at h
    nlinarith
  have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ L+v) he p
  rw [mul_pow,← Real.exp_nat_mul] at h
  convert h using 1
  congr 2
  ring

/-- Full moment-weighted tail majorant. -/
theorem thetaMode_weighted_shift_le (m p : ℕ) {L v : ℝ}
    (hL : 0 < L) (hv : 0 ≤ v) :
    (L+v)^p*thetaMode m (L+v) ≤
      (thetaMode m L*L^p)*exp (-(2*thetaArgument m L-1/2-(p:ℝ)/L)*v) := by
  have h := mul_le_mul (shifted_power_le p hL hv) (thetaMode_shift_le m L v hv)
    (thetaMode_nonneg m (L+v)) (by positivity : (0:ℝ) ≤ L^p*exp ((p:ℝ)/L*v))
  calc
    _ ≤ L^p*exp ((p:ℝ)/L*v)*(thetaMode m L*exp (-(2*thetaArgument m L-1/2)*v)) := h
    _ = _ := by
      rw [mul_mul_mul_comm,← exp_add]
      congr 1
      · ring
      · congr 1; ring

/-- Integral of the majorant, for the actual infinite half-line. -/
theorem thetaMode_weighted_tail_bound (m p : ℕ) {L : ℝ} (hL : 0 < L)
    (hd : 0 < 2*thetaArgument m L-1/2-(p:ℝ)/L) :
    0 ≤ (∫ u in Ioi L, u^p*thetaMode m u) ∧
    (∫ u in Ioi L, u^p*thetaMode m u) ≤
      thetaMode m L*L^p/(2*thetaArgument m L-1/2-(p:ℝ)/L) := by
  let d := 2*thetaArgument m L-1/2-(p:ℝ)/L
  let A := thetaMode m L*L^p
  have hd' : 0 < d := hd
  have hib : IntegrableOn (fun u => (A*exp (d*L))*exp (-d*u)) (Ioi L) :=
    (integrableOn_exp_mul_Ioi (by linarith : -d < 0) L).const_mul _
  have hpoint (u : ℝ) (hu : L < u) :
      u^p*thetaMode m u ≤ (A*exp (d*L))*exp (-d*u) := by
    have h := thetaMode_weighted_shift_le m p hL (by linarith : 0 ≤ u-L)
    rw [show L+(u-L)=u by ring] at h
    convert h using 1
    dsimp [d,A]
    rw [mul_assoc,← exp_add]
    congr 1
    congr 1
    ring
  have hi : IntegrableOn (fun u => u^p*thetaMode m u) (Ioi L) := by
    apply hib.mono' (by
      apply Continuous.aestronglyMeasurable
      exact (continuous_id.pow p).mul ((contDiff_thetaMode m 1).continuous))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (hL.le.trans hu.le) p)
      (thetaMode_nonneg m u))]
    exact hpoint u hu
  have hb := integral_mono_ae hi hib (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpoint u hu)
  have he : (∫ u in Ioi L, (A*exp (d*L))*exp (-d*u)) = A/d := by
    rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : -d < 0)]
    rw [neg_div_neg_eq]
    have hecancel : exp (d*L)*exp (-d*L) = 1 := by
      rw [← exp_add,show d*L+-d*L=0 by ring,exp_zero]
    calc
      _ = A*(exp (d*L)*exp (-d*L))/d := by ring
      _ = A/d := by rw [hecancel,mul_one]

  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (pow_nonneg (hL.le.trans hu.le) p) (thetaMode_nonneg m u)
  · exact hb.trans_eq he

end
end CarryIntegralCertificate
