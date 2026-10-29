import CriticalRelative
import SchurLogic

namespace CarryCriticalRelative
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn CarryCriticalSource
open Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000

def physicalGrowth (k m : ℕ) : ℝ := ((k:ℝ)+1)^(2*m+1)

theorem physicalGrowth_pos (k m : ℕ) : 0 < physicalGrowth k m := by
  unfold physicalGrowth
  positivity

theorem step_norm (k : ℕ) : ‖step k‖ = ((k:ℝ)+1)⁻¹ := by
  change ‖Complex.I * canonicalGreenJetStep k‖ = _
  have he : canonicalGreenJetStep k = ((((k:ℝ)+1)⁻¹ : ℝ) : ℂ) :=
    (canonicalGreenJetRealStep_coe k).symm
  rw [norm_mul, Complex.norm_I, one_mul, he, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem observationScale_norm_sq (k m : ℕ) :
    ‖observationScale k m‖^2 = (physicalGrowth k m)⁻¹ := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hsq := Real.sq_sqrt hk.le
  simp only [observationScale, norm_mul, norm_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), step_norm, mul_pow, inv_pow]
  rw [hsq]
  unfold physicalGrowth
  have hg : ((k:ℝ)+1)^(2*m+1) = (((k:ℝ)+1)^m)^2 * ((k:ℝ)+1) := by
    rw [show 2*m+1 = m*2+1 by omega, pow_succ, pow_mul]
  rw [hg]
  simp only [mul_inv_rev]
  ring

theorem critical_incident_growth (s : Fin 2) (n : ℕ) :
    Tendsto (fun k => ‖criticalIncident s n k‖^2 / physicalGrowth k (criticalOrder s n))
      atTop (nhds (‖criticalLeadingState s n‖^2)) := by
  have h := (scaled_incident_tendsto (n+1) (criticalOrder s n)
    (criticalCoordinates s n) (criticalOrder_lt s n) (criticalCoordinates_above s n)).norm.pow 2
  simpa only [critical_pair_exact, critical_leading_eq, norm_smul, mul_pow,
    observationScale_norm_sq, Submodule.norm_coe, div_eq_mul_inv, mul_comm] using h

theorem critical_returned_growth (s : Fin 2) (n : ℕ) :
    Tendsto (fun k => ‖criticalReturned s n k‖^2 / physicalGrowth k (criticalOrder s n))
      atTop (nhds (‖criticalLeadingState s n‖^2)) := by
  have h := (scaled_returned_tendsto (n+1) (criticalOrder s n)
    (criticalCoordinates s n) (criticalOrder_lt s n) (criticalCoordinates_above s n)).norm.pow 2
  simpa only [critical_pair_exact, critical_leading_eq, norm_smul, mul_pow,
    observationScale_norm_sq, norm_neg, div_eq_mul_inv, mul_comm] using h

theorem critical_incident_diverges (s : Fin 2) (n : ℕ) :
    Tendsto (fun k => ‖criticalIncident s n k‖^2) atTop atTop := by
  have ht := critical_incident_growth s n
  have hc : 0 < ‖criticalLeadingState s n‖^2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (criticalLeadingState_ne s n))
  have hg : Tendsto (fun k => physicalGrowth k (criticalOrder s n)) atTop atTop := by
    have hk : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
    exact (tendsto_pow_atTop (by omega : 2*criticalOrder s n+1 ≠ 0)).comp hk
  have h := hg.atTop_mul_pos hc ht
  have he (k : ℕ) :
      physicalGrowth k (criticalOrder s n) *
        (‖criticalIncident s n k‖^2 / physicalGrowth k (criticalOrder s n)) =
        ‖criticalIncident s n k‖^2 := by
    field_simp [(physicalGrowth_pos k (criticalOrder s n)).ne']
  simpa only [he] using h

def relativeDeficit (s : Fin 2) (n k : ℕ) : ℝ :=
  1 - ‖criticalReturned s n k‖^2 / ‖criticalIncident s n k‖^2

def criticalGapCoefficient (s : Fin 2) (n : ℕ) : ℝ :=
  2*sourceMomentSchur h s.val n / ‖criticalLeadingState s n‖^2

/-- Algebraic identification needs an invertible old prefix, not its sign. -/
theorem critical_boundary_of_isUnit (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s.val n)) :
    nativeSourceFiniteBoundaryEnergy (2*(n+1)) (criticalCoordinates s n) =
      4*sourceMomentSchur h s.val n := by
  rw [criticalCoordinates, parityCoordinates_boundary]
  exact congrArg (4*·)
    (NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit h s.val n hA)

/-- Full physical balance with no old or new sign premise. -/
theorem critical_balance_tendsto_of_isUnit (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s.val n)) :
    Tendsto (criticalBalance s n) atTop (nhds (2*sourceMomentSchur h s.val n)) := by
  have ht : Tendsto (fun k => 2*(storage k (criticalInput s n k) 1).re)
      atTop (nhds (nativeSourceFiniteBoundaryEnergy (2*(n+1))
        (criticalCoordinates s n))) := by
    simpa only [criticalInput, nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage]
      using nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto
        (n+1) (criticalCoordinates s n)
  rw [critical_boundary_of_isUnit s n hA] at ht
  have hh := ht.div_const 2
  have he : 4*sourceMomentSchur h s.val n/2 = 2*sourceMomentSchur h s.val n := by ring
  rw [he] at hh
  simpa only [← criticalBalance_eq_storage,
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hh

/-- The first surviving relative coefficient retains the exact canonical
pivot. Only old-prefix invertibility is needed; no pivot sign is used. -/
theorem critical_scaled_relative_deficit (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s.val n)) :
    Tendsto (fun k => physicalGrowth k (criticalOrder s n) * relativeDeficit s n k)
      atTop (nhds (criticalGapCoefficient s n)) := by
  have hc : ‖criticalLeadingState s n‖^2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (criticalLeadingState_ne s n))
  have ht := (critical_balance_tendsto_of_isUnit s n hA).div (critical_incident_growth s n) hc
  change Tendsto (fun k => criticalBalance s n k /
      (‖criticalIncident s n k‖^2 / physicalGrowth k (criticalOrder s n)))
    atTop (nhds (criticalGapCoefficient s n)) at ht
  apply ht.congr'
  filter_upwards [incident_eventually_ne_zero (n+1) (criticalOrder s n)
    (criticalCoordinates s n) (criticalOrder_lt s n)
      (criticalCoordinates_above s n) (criticalCoordinates_top_ne s n)] with k hk
  rw [critical_pair_exact] at hk
  have hn : ‖criticalIncident s n k‖^2 ≠ 0 := by
    exact pow_ne_zero 2 (by simpa only [Submodule.norm_coe] using norm_ne_zero_iff.mpr hk)
  unfold relativeDeficit criticalBalance
  have hnorm : ‖criticalIncident s n k‖ ≠ 0 := fun hz => hn (by rw [hz]; norm_num)
  field_simp [hn, hnorm, (physicalGrowth_pos k (criticalOrder s n)).ne']

/-- Quantitative relative corridor at the forced physical scale, with a
threshold depending on sector, order and tolerance. No uniform margin. -/
theorem critical_relative_corridor (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s.val n)) (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      (criticalGapCoefficient s n - epsilon) / physicalGrowth k (criticalOrder s n) <
        relativeDeficit s n k ∧
      relativeDeficit s n k <
        (criticalGapCoefficient s n + epsilon) / physicalGrowth k (criticalOrder s n) := by
  have ht := critical_scaled_relative_deficit s n hA
  have hlo := (tendsto_order.mp ht).1 (criticalGapCoefficient s n-epsilon) (by linarith)
  have hhi := (tendsto_order.mp ht).2 (criticalGapCoefficient s n+epsilon) (by linarith)
  filter_upwards [hlo,hhi] with k hklo hkhi
  constructor
  · exact (div_lt_iff₀ (physicalGrowth_pos k _)).mpr (by nlinarith)
  · exact (lt_div_iff₀ (physicalGrowth_pos k _)).mpr (by nlinarith)

theorem critical_gap_coefficient_pos_iff (s : Fin 2) (n : ℕ) :
    0 < criticalGapCoefficient s n ↔ 0 < sourceMomentSchur h s.val n := by
  unfold criticalGapCoefficient
  rw [div_pos_iff_of_pos_right (sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr (criticalLeadingState_ne s n)))]
  exact mul_pos_iff_of_pos_left (by norm_num : (0:ℝ) < 2)

end
end CarryCriticalRelative
