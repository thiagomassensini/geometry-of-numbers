import SigmaSourceBezout

/-!
# Analytic domain for the C5 displaced source

This module records the exact open disk on which the original displaced
product is analytic. It does not replace the source or assert the numerical
modulus bound needed for coefficient-box inclusion.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator
open CarrySelfAdjointOperator.CompletedNativeRealHPCarrierCertificate
open scoped Topology

noncomputable section

/-- For both C5 displacements, the original shifted characteristic factors stay
inside their proved centered-height strip throughout the open disk of radius
`2/5`. -/
theorem displacedProductC_shiftedFactors_mem_completedNativeHeightDomain
    (d : ℝ) (hd : |d| ≤ (1 / 10 : ℝ)) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (2 / 5 : ℝ)) :
    z - Complex.I * (d : ℂ) ∈ completedNativeHeightDomain ∧
      z + Complex.I * (d : ℂ) ∈ completedNativeHeightDomain := by
  have hnorm : ‖z‖ < (2 / 5 : ℝ) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have him : |z.im| < (2 / 5 : ℝ) := (Complex.abs_im_le_norm z).trans_lt hnorm
  have hminus : |(z - Complex.I * (d : ℂ)).im| < (1 / 2 : ℝ) := by
    calc
      |(z - Complex.I * (d : ℂ)).im| = |z.im - d| := by simp
      _ ≤ |z.im| + |d| := abs_sub _ _
      _ < (2 / 5 : ℝ) + (1 / 10 : ℝ) := add_lt_add_of_lt_of_le him hd
      _ = (1 / 2 : ℝ) := by norm_num
  have hplus : |(z + Complex.I * (d : ℂ)).im| < (1 / 2 : ℝ) := by
    calc
      |(z + Complex.I * (d : ℂ)).im| = |z.im + d| := by simp
      _ ≤ |z.im| + |d| := abs_add_le _ _
      _ < (2 / 5 : ℝ) + (1 / 10 : ℝ) := add_lt_add_of_lt_of_le him hd
      _ = (1 / 2 : ℝ) := by norm_num
  constructor <;> rw [mem_completedNativeHeightDomain_iff_im_bounds]
  · exact (abs_lt.mp hminus)
  · exact (abs_lt.mp hplus)

/-- The exact original C5 displaced product is analytic on the open disk of
radius `2/5` for either target displacement. -/
theorem displacedProductC_analyticOnNhd_ball
    (d : ℝ) (hd : |d| ≤ (1 / 10 : ℝ)) :
    AnalyticOnNhd ℂ (displacedProductC d) (Metric.ball 0 (2 / 5 : ℝ)) := by
  intro z hz
  obtain ⟨hminus, hplus⟩ :=
    displacedProductC_shiftedFactors_mem_completedNativeHeightDomain d hd hz
  have hminusAnalytic := completedNativeOperatorCharacteristic_analyticAt hminus
  have hplusAnalytic := completedNativeOperatorCharacteristic_analyticAt hplus
  have hminusMap : AnalyticAt ℂ (fun w : ℂ => w - Complex.I * (d : ℂ)) z := by
    fun_prop
  have hplusMap : AnalyticAt ℂ (fun w : ℂ => w + Complex.I * (d : ℂ)) z := by
    fun_prop
  have hminusComp : AnalyticAt ℂ
      (fun w : ℂ => completedNativeOperatorCharacteristic
        (w - Complex.I * (d : ℂ))) z :=
    AnalyticAt.comp (f := fun w : ℂ => w - Complex.I * (d : ℂ))
      hminusAnalytic hminusMap
  have hplusComp : AnalyticAt ℂ
      (fun w : ℂ => completedNativeOperatorCharacteristic
        (w + Complex.I * (d : ℂ))) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + Complex.I * (d : ℂ))
      hplusAnalytic hplusMap
  change AnalyticAt ℂ
    (fun w : ℂ => completedNativeOperatorCharacteristic
      (w - Complex.I * (d : ℂ)) *
      completedNativeOperatorCharacteristic (w + Complex.I * (d : ℂ))) z
  exact hminusComp.mul hplusComp

theorem displacedProductC_analyticOnNhd_ball_00495 :
    AnalyticOnNhd ℂ (displacedProductC (99 / 2000 : ℝ))
      (Metric.ball 0 (2 / 5 : ℝ)) := by
  apply displacedProductC_analyticOnNhd_ball
  norm_num

theorem displacedProductC_analyticOnNhd_ball_01 :
    AnalyticOnNhd ℂ (displacedProductC (1 / 10 : ℝ))
      (Metric.ball 0 (2 / 5 : ℝ)) := by
  apply displacedProductC_analyticOnNhd_ball
  norm_num

#print axioms displacedProductC_shiftedFactors_mem_completedNativeHeightDomain
#print axioms displacedProductC_analyticOnNhd_ball
#print axioms displacedProductC_analyticOnNhd_ball_00495
#print axioms displacedProductC_analyticOnNhd_ball_01

end
end CarrySigmaObstruction
