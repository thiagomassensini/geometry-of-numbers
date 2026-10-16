import GeometryOfNumbers.Analysis.CarryMaterialCentralProjection
import Mathlib.Analysis.Complex.ExponentialBounds

namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion FiniteClockJets
open scoped InnerProductSpace BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem reciprocal_square_sum_le_two :
    (∑' n : ℕ, 1 / ((n+1 : ℕ) : ℝ)^2) ≤ 2 := by
  have hsum (N : ℕ) : (∑ n ∈ Finset.range N, 1 / ((n+1 : ℕ) : ℝ)^2) ≤
      2 - 2 / ((N+1 : ℕ) : ℝ) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hp : (0 : ℝ) < ((N+1 : ℕ) : ℝ) := by positivity
      have hq : (0 : ℝ) < ((N+2 : ℕ) : ℝ) := by positivity
      have hd : 1 / ((N+1 : ℕ) : ℝ)^2 ≤
          2 / ((N+1 : ℕ) : ℝ) - 2 / ((N+2 : ℕ) : ℝ) := by
        apply (le_sub_iff_add_le).mpr
        field_simp
        norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
        nlinarith
      change (∑ n ∈ Finset.range N, 1 / ((n+1 : ℕ) : ℝ)^2) + 1 / ((N+1 : ℕ) : ℝ)^2 ≤
        2 - 2 / ((N+2 : ℕ) : ℝ)
      linarith
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  exact (hsum N).trans (sub_le_self _ (by positivity))

/-- A coarse rigorous bound, obtained from the existing complete-cell
second-difference majorant and a telescoping reciprocal-square comparison. -/
theorem carryMaterial_signal_zero_norm_le : ‖baseTwoCriticalCompleteSignal 0‖ ≤ 5/2 := by
  have hs : Summable (fun n : ℕ => 1 / ((n+1 : ℕ) : ℝ)^2) := by
    have h : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-2 : ℝ)) :=
      (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num))
    simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, one_div] using h
  have hcell (n : ℕ) : ‖baseTwoCriticalCenterCell 0 n‖ ≤
      (3/4 : ℝ) * (1 / ((n+1 : ℕ) : ℝ)^2) := by
    have h := baseTwoCriticalCenterCell_norm_le 0 n
    have he : ‖criticalMaterialExponent 0 * (criticalMaterialExponent 0 - 1)‖ = (3/4 : ℝ) := by
      norm_num [criticalMaterialExponent, Complex.norm_real]
    rw [he] at h
    have hr := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      (by norm_num : (-5/2 : ℝ) ≤ -2)
    simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, one_div] using
      h.trans (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 3/4))
  have hb := (summable_norm_baseTwoCriticalCenterCell 0).tsum_le_tsum hcell (hs.mul_left (3/4 : ℝ))
  rw [tsum_mul_left] at hb
  have hn := norm_tsum_le_tsum_norm (summable_norm_baseTwoCriticalCenterCell 0)
  have ha := norm_add_le (criticalMaterialSample 0 1) (∑' n, baseTwoCriticalCenterCell 0 n)
  rw [baseTwoCriticalCompleteSignal, show criticalMaterialSample 0 1 = 1 by simp [criticalMaterialSample]]
  have hseed : criticalMaterialSample 0 1 = 1 := by simp [criticalMaterialSample]
  rw [hseed, norm_one] at ha
  nlinarith [reciprocal_square_sum_le_two]

/-- A source-derived two-coordinate annihilator. Its coefficient is the
actual edge-zero gradient of Y0; no moment or desired norm is an input. -/
def carryMaterialCentralEdgeContrast (y : MaterialCarrier) : ℂ :=
  y.snd.fst 0 - (baseTwoCompletedMaterialGradientL2 0) 0 * y.fst

theorem carryMaterialCentralEdgeContrast_unit : carryMaterialCentralEdgeContrast carryMaterialCentralUnit = 0 := by
  simp [carryMaterialCentralEdgeContrast, carryMaterialCentralUnit,
    baseTwoCompletedBoundaryHilbertState_interior, mul_comm]

theorem carryMaterialCentralEdgeContrast_complement (y : MaterialCarrier) :
    carryMaterialCentralEdgeContrast (carryMaterialCentralComplement y) = carryMaterialCentralEdgeContrast y := by
  have h := carryMaterialCentralEdgeContrast_unit
  simp only [carryMaterialCentralComplement_apply, carryMaterialCentralEdgeContrast,
    WithLp.sub_fst, WithLp.sub_snd, WithLp.smul_fst, WithLp.smul_snd, lp.coeFn_sub,
    lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
  linear_combination -(inner ℂ carryMaterialCentralUnit y) * h

theorem carryMaterialCentralEdgeContrast_norm_le (y : MaterialCarrier) :
    ‖carryMaterialCentralEdgeContrast y‖ ≤ 2*‖y‖ := by
  have hg := criticalMaterialGradient_norm_le 0 0
  norm_num [criticalMaterialExponent] at hg
  have hc : ‖(baseTwoCompletedMaterialGradientL2 0) 0‖ ≤ 1 := by
    simpa only [baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply] using
      hg.trans (by norm_num)
  have hseed : ‖y.fst‖ ≤ ‖y‖ := WithLp.norm_fst_le (p := 2) ℂ y
  have hedge : ‖y.snd.fst 0‖ ≤ ‖y‖ :=
    (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) y.snd.fst 0).trans
      ((WithLp.norm_fst_le (p := 2) MaterialEdgeL2 y.snd).trans (WithLp.norm_snd_le (p := 2) _ y))
  have hn := norm_sub_le (y.snd.fst 0) ((baseTwoCompletedMaterialGradientL2 0) 0 * y.fst)
  rw [norm_mul] at hn
  exact hn.trans (by nlinarith [mul_le_mul hc hseed (norm_nonneg y.fst) (by norm_num : (0 : ℝ) ≤ 1)])

/-- Existing clock applied to the actual center, with its full global return. -/
def carryMaterialCentralClock : MaterialCarrier :=
  completedBoundaryTransportedClock
    ⟨baseTwoCompletedBoundaryHilbertState 0, baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0⟩

theorem carryMaterialCentralEdgeContrast_clock :
    carryMaterialCentralEdgeContrast carryMaterialCentralClock =
      ((Real.log 2 / Real.sqrt 2 : ℝ) : ℂ) := by
  unfold carryMaterialCentralEdgeContrast carryMaterialCentralClock
  rw [completedBoundaryTransportedClock_seed, mul_zero, sub_zero,
    completedBoundaryTransportedClock_interior, baseTwoCompletedBoundaryHilbertClockCoordinate_eq]
  norm_num [criticalMaterialSample, div_eq_mul_inv]

/-- A fixed source coordinate survives central-plane removal. -/
theorem carryMaterialCentralClock_complement_norm_lower :
    (1/32 : ℝ) < ‖carryMaterialCentralComplement carryMaterialCentralClock‖^2 := by
  have h := carryMaterialCentralEdgeContrast_norm_le
    (carryMaterialCentralComplement carryMaterialCentralClock)
  rw [carryMaterialCentralEdgeContrast_complement, carryMaterialCentralEdgeContrast_clock,
    Complex.norm_real, Real.norm_eq_abs] at h
  have hl : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hs := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [abs_of_pos (div_pos (by linarith) hs)] at h
  have hp := (div_le_iff₀ hs).mp h
  have hq := norm_nonneg (carryMaterialCentralComplement carryMaterialCentralClock)
  have hpow := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ Real.log 2) hp 2
  rw [mul_pow, mul_pow, hs2] at hpow
  nlinarith

/-- Rigorous separation margin for this fixed candidate's first real jet. -/
theorem carryMaterialCenteredState_firstJet_energy_gt :
    (1/512 : ℝ) < ‖deriv carryMaterialCenteredState 0‖^2 := by
  have hk := carryMaterialCentralClock_complement_norm_lower
  have hs := carryMaterial_signal_zero_norm_le
  have hspos : 0 < ‖baseTwoCriticalCompleteSignal 0‖ :=
    norm_pos_iff.mpr carryMaterial_origin_signal_ne_zero
  have he := carryMaterialCenteredState_firstJet_energy
  change ‖deriv carryMaterialCenteredState 0‖^2 =
    (‖carryMaterialCentralClock‖^2 - ‖inner ℂ carryMaterialCentralUnit carryMaterialCentralClock‖^2) /
      (2*‖baseTwoCriticalCompleteSignal 0‖^2) at he
  rw [← carryMaterialCentralComplement_norm_sq] at he
  rw [he]
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith [norm_nonneg (baseTwoCriticalCompleteSignal 0)]

/-- The actual material clock leaves the central plane; projecting that
plane alone is not a dynamical intertwiner. -/
theorem carryMaterialCentralComplement_clock_center_ne :
    carryMaterialCentralComplement carryMaterialCentralClock ≠
      completedBoundaryTransportedClock
        ⟨carryMaterialCentralComplement (baseTwoCompletedBoundaryHilbertState 0),
          carryMaterialCentralComplement_mem_clockDomain _
            (baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0)⟩ := by
  have hz : (⟨carryMaterialCentralComplement (baseTwoCompletedBoundaryHilbertState 0),
      carryMaterialCentralComplement_mem_clockDomain _
        (baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0)⟩ :
      completedBoundaryTransportedClock.domain) = 0 := by
    apply Subtype.ext
    exact carryMaterialCentralComplement_center
  rw [hz]
  change carryMaterialCentralComplement carryMaterialCentralClock ≠ completedBoundaryTransportedClock.toFun 0
  rw [map_zero]
  intro he
  have hp := carryMaterialCentralClock_complement_norm_lower
  rw [he, norm_zero] at hp
  norm_num at hp

end
end GeometryOfNumbers.Analysis
