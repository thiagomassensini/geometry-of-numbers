import MixedInfinite
import TiltBounds
import Mathlib.Analysis.Normed.Group.Tannery

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem tilt_ratio_bound (c d : ℝ) (hc : 2 ≤ c) (hdlo : -(1/4:ℝ) < d)
    (hdhi : d < 1/4) (hd : d ≠ 0) :
    |cpTilt 3 d c| / |d| ≤ 2 * (c-1)^(-1:ℝ) := by
  have hb := abs_cpTilt_three_upper_bound (show -(1:ℝ)/2 < d by linarith)
    (show d < (1:ℝ)/2 by linarith) hd (show 1<c by linarith)
  have hp : (c-1)^(-d-2) ≤ (c-1)^(-1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hpos : 0 ≤ (c-1)^(-d-2) := Real.rpow_nonneg (by linarith) _
  have hdplus : |d+1| ≤ 2 := by
    rw [abs_of_pos (by linarith : 0 < d+1)]
    linarith
  have hcoef : |d*(d+1)| ≤ |d| * 2 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdplus (abs_nonneg d)
  have hb2 : |cpTilt 3 d c| ≤ (|d| * 2)*(c-1)^(-1:ℝ) :=
    hb.trans (mul_le_mul hcoef hp hpos (by positivity))
  apply (div_le_iff₀ (abs_pos.mpr hd)).2
  nlinarith [hb2]

theorem critical_carrier_norm (k : ℕ) (t : ℝ) :
    ‖localCriticalLineCarrier (criticalParameter t) (canonicalRealCpCenter k) 0‖ =
      canonicalRealCpCenter k ^ (-(1/2:ℝ)) := by
  rw [critical_carrier_phase,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one (center_gt_one k))) _),
    Complex.norm_exp,tilt_exp_arg_re_zero,Real.exp_zero,mul_one]

def transverseSlope (k : ℕ) (t d : ℝ) : ℂ :=
  d⁻¹ • (canonicalCriticalWeightedTiltBlock k (displacedParameter d t) -
    canonicalCriticalWeightedTiltBlock k (displacedParameter 0 t))

theorem transverseSlope_norm_le (k : ℕ) (t d : ℝ) (hdlo : -(1/4:ℝ) < d)
    (hdhi : d < 1/4) (hd : d ≠ 0) :
    ‖transverseSlope k t d‖ ≤ 2 * (((k+1:ℕ):ℝ)^(-(3/2):ℝ)) := by
  let c : ℝ := canonicalRealCpCenter k
  let j : ℝ := ((k+1:ℕ):ℝ)
  have hj : 0 < j := by dsimp [j]; positivity
  have hj1 : 1 ≤ j := by dsimp [j]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have heq : c = 3*j := by simp [c,j,canonicalRealCpCenter]
  have hc2 : 2 ≤ c := by rw [heq]; nlinarith
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) hc2
  have hjc : j ≤ c := by rw [heq]; linarith
  have hjleft : j ≤ c-1 := by rw [heq]; linarith
  have hw : 0 ≤ c^(-(1/2:ℝ)) := Real.rpow_nonneg hc.le _
  have hjw : 0 ≤ j^(-(1/2:ℝ)) := Real.rpow_nonneg hj.le _
  have hwl : c^(-(1/2:ℝ)) ≤ j^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hj hjc (by norm_num)
  have hpl : (c-1)^(-1:ℝ) ≤ j^(-1:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hj hjleft (by norm_num)
  have hratio := tilt_ratio_bound c d hc2 hdlo hdhi hd
  have hnorm : ‖transverseSlope k t d‖ = c^(-(1/2:ℝ)) * (|cpTilt 3 d c|/|d|) := by
    unfold transverseSlope
    rw [tilted_cell_displaced,tilted_cell_displaced]
    simp only [cpTilt_zero 3 (by norm_num),Complex.ofReal_zero,mul_zero,sub_zero]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,norm_mul,critical_carrier_norm,Complex.norm_real]
    simp only [Real.norm_eq_abs]
    dsimp only [c]
    ring
  rw [hnorm]
  calc
    _ ≤ c^(-(1/2:ℝ)) * (2*(c-1)^(-1:ℝ)) := mul_le_mul_of_nonneg_left hratio hw
    _ ≤ j^(-(1/2:ℝ)) * (2*j^(-1:ℝ)) := by
      have hleft : 0 ≤ 2*(c-1)^(-1:ℝ) := mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
      exact mul_le_mul hwl (mul_le_mul_of_nonneg_left hpl (by norm_num)) hleft hjw
    _ = 2 * (j^(-(1/2:ℝ))*j^(-1:ℝ)) := by ring
    _ = 2 * j^(-(3/2):ℝ) := by
      rw [← Real.rpow_add hj]
      congr 1
      norm_num


#print axioms transverseSlope_norm_le
end
end CarryTiltSlice
