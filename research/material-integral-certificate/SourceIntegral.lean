import ThetaRetainedTail
import CanonicalPivotCertificate

/-! Integral-level comparison with the original infinite theta source. -/
namespace CarryIntegralCertificate
open CarrySelfAdjointOperator CarryMaterialThetaCertificate Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem thetaMode_le_thetaTail (m : ℕ) (u : ℝ) :
    thetaMode m u ≤ XiThetaCosine.thetaTail u := by
  rw [XiThetaCosine.thetaTail_eq_two_mul_tsum]
  exact mul_le_mul_of_nonneg_left ((XiThetaCosine.summable_thetaTailMode u).le_tsum m
    (fun n _ => by unfold XiThetaCosine.thetaTailMode; positivity)) (by norm_num)

theorem integrableOn_weighted_thetaMode (m p : ℕ) :
    IntegrableOn (fun u : ℝ => u^p*thetaMode m u) (Ioi 0) := by
  apply (integrableOn_pow_mul_thetaTail p).mono'
    ((continuous_id.pow p).mul ((contDiff_thetaMode m 1).continuous)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change |u^p*thetaMode m u| ≤ u^p*XiThetaCosine.thetaTail u
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg hu.le p) (thetaMode_nonneg m u))]
  exact mul_le_mul_of_nonneg_left (thetaMode_le_thetaTail m u) (pow_nonneg hu.le p)

def weightedThreeModes (p : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 3, u^p*thetaMode m u

theorem integrableOn_weightedThreeModes (p : ℕ) :
    IntegrableOn (weightedThreeModes p) (Ioi 0) :=
  integrable_finsetSum _ (fun m _ => integrableOn_weighted_thetaMode m p)

/-- This is the actual signed difference from the infinite source; its
nonnegativity below follows from the existing theta decomposition. -/
def weightedOmittedModes (p : ℕ) (u : ℝ) : ℝ :=
  u^p*XiThetaCosine.thetaTail u-weightedThreeModes p u

theorem integrableOn_weightedOmittedModes (p : ℕ) :
    IntegrableOn (weightedOmittedModes p) (Ioi 0) :=
  (integrableOn_pow_mul_thetaTail p).sub (integrableOn_weightedThreeModes p)

theorem weightedOmittedModes_bounds (p : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ weightedOmittedModes p u ∧
      weightedOmittedModes p u ≤ (1/10^20:ℝ)*(u^p*exp (-95*u)) := by
  have he : weightedOmittedModes p u =
      u^p*(2*∑' n : ℕ, XiThetaCosine.thetaTailMode (n+3) u) := by
    unfold weightedOmittedModes weightedThreeModes thetaMode
    rw [theta_three_mode_split]
    simp only [mul_add,Finset.mul_sum]
    ring
  rw [he]
  constructor
  · apply mul_nonneg (pow_nonneg hu p)
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg (fun n => by unfold XiThetaCosine.thetaTailMode; positivity)
  · have h := mul_le_mul_of_nonneg_left (theta_tail_after_three_le hu) (pow_nonneg hu p)
    exact h.trans_eq (by ring)

theorem integral_weighted_exp95 (p : ℕ) :
    (∫ u in Ioi (0:ℝ), u^p*exp (-95*u)) = (p.factorial:ℝ)/95^(p+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (p:ℝ)+1) (r := (95:ℝ)) (by positivity) (by norm_num)
  simp only [add_sub_cancel_right,rpow_natCast] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [show (p:ℝ)+1 = ((p+1:ℕ):ℝ) by push_cast; rfl,rpow_natCast] at h
  simpa [one_div,inv_pow,div_eq_mul_inv,mul_comm,neg_mul] using h

theorem integral_weightedOmittedModes_bounds (p : ℕ) :
    0 ≤ (∫ u in Ioi 0, weightedOmittedModes p u) ∧
      (∫ u in Ioi 0, weightedOmittedModes p u) ≤
        (p.factorial:ℝ)/(10^20*95^(p+1)) := by
  have he : IntegrableOn (fun u : ℝ => u^p*exp (-95*u)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ))
      (s := (p:ℝ)) (b := (95:ℝ))
      (show -1 < (p:ℝ) by have h := Nat.cast_nonneg (α:=ℝ) p; linarith)
      (by norm_num) (by norm_num)
    simpa only [rpow_natCast,rpow_one] using h
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (weightedOmittedModes_bounds p hu.le).1
  · have h := integral_mono_ae (integrableOn_weightedOmittedModes p)
      (he.const_mul (1/10^20:ℝ)) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact (weightedOmittedModes_bounds p hu.le).2)
    rw [integral_const_mul,integral_weighted_exp95] at h
    exact h.trans_eq (by ring)

/-- Exact source = three complete retained integrals + the controlled
infinite remainder. The latter is preserved rather than dropped. -/
theorem completedNativeThetaTailMoment_eq_three_and_remainder (p : ℕ) :
    completedNativeThetaTailMoment p =
      (∑ m ∈ Finset.range 3, ∫ u in Ioi 0, u^p*thetaMode m u)+
        ∫ u in Ioi 0, weightedOmittedModes p u := by
  have h : (fun u => u^p*XiThetaCosine.thetaTail u) =
      fun u => weightedThreeModes p u+weightedOmittedModes p u := by
    funext u
    unfold weightedOmittedModes
    ring
  unfold completedNativeThetaTailMoment
  rw [h,integral_add (integrableOn_weightedThreeModes p)
    (integrableOn_weightedOmittedModes p)]
  congr 1
  exact integral_finsetSum _ (fun m _ => integrableOn_weighted_thetaMode m p)

end
end CarryIntegralCertificate
