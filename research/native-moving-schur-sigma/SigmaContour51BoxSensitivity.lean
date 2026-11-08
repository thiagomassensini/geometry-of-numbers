import SigmaContour51SourceTail
import SigmaSourceBezout
import Mathlib.Tactic

/-!
# Exact width of the ten-mode boxes for the six contour residuals

The B2 height intervals give a rational interval for each comparison power sum
`P_n = sum_i (gamma_i^(-2))^(n+1)`.  This module records exact rational upper
bounds for the widths of those intervals and the source-jet margin that would
be sufficient to certify a residual sign.  It does not assert any sign for the
original residuals.
-/

namespace CarrySigmaObstruction

open CarrySigmaCentral CarrySigmaSource CarrySourceBezout
open CarrySelfAdjointOperator
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Width of the current B2-box enclosure for the ten-mode power sum `P_n`. -/
def contour51TenModeBoxWidth (n : ℕ) : ℝ := highMoment n - lowMoment n

/-- Exact rational budgets strictly containing the current power-sum box widths for `n≤5`.
The budgets are coarse rational upper bounds; no residual sign is encoded here. -/
def contour51TenModeBoxWidthBudget (n : ℕ) : ℝ :=
  if n = 0 then 14 / 1000000
  else if n = 1 then 9 / 100000000
  else if n = 2 then 6 / 10000000000
  else if n = 3 then 4 / 1000000000000
  else if n = 4 then 3 / 100000000000000
  else 2 / 10000000000000000

/-- At zero displacement, C5's original product is exactly the square of the original
completed characteristic; the source itself is not defined from its roots. -/
theorem c5CentralDisplacedProduct_eq_characteristic_square (z : ℂ) :
    displacedProductC 0 z = completedNativeOperatorCharacteristic z ^ 2 := by
  simp [displacedProductC]
  ring

/-- On the original native strip, the zero-displacement C5 product agrees with the square
of the entire continuation used by the radius-51 contour argument. The domain condition is
explicit because the native/continuation identification is proved on this strip. -/
theorem c5CentralDisplacedProduct_eq_continuation_square
    {z : ℂ} (hs : operatorHeightParameter z ∈ CPFormal.Analytic.Cp.genuineCriticalStrip) :
    displacedProductC 0 z = completedNativeCharacteristicContinuation z ^ 2 := by
  rw [c5CentralDisplacedProduct_eq_characteristic_square,
    ← completedNativeCharacteristicContinuation_eq_native hs]

/-- C5's source recurrence at `d=0` returns the twice-scaled original central moments. This is
the explicit center specialization needed before any displaced-source interval can be reused. -/
theorem c5CentralSource_log_derivative_eq_twice_original_jets :
    -(PowerSeries.derivative ℝ (completedSigmaDisplacedSourceSeries 0)) *
        (completedSigmaDisplacedSourceSeries 0)⁻¹ =
      momentSeries (fun n => 2 * completedSigmaLogJet 0 n) := by
  calc
    _ = momentSeries (completedSigmaDisplacedMoment 0) :=
      completedSigmaDisplacedSource_log_derivative_eq_moments 0
        (by norm_num : -(1 / 2 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1 / 2)
    _ = momentSeries (fun n => 2 * completedSigmaLogJet 0 n) := by
      rfl

/-- Coefficient form of the exact zero-displacement transport: every C5 source quotient
coefficient equals `2 H_n` from the original central C2 source. -/
theorem c5CentralSource_log_derivative_coeff_eq_twice_original_jet (n : ℕ) :
    PowerSeries.coeff n
        (-(PowerSeries.derivative ℝ (completedSigmaDisplacedSourceSeries 0)) *
          (completedSigmaDisplacedSourceSeries 0)⁻¹) =
      2 * completedSigmaLogJet 0 n := by
  have h := congrArg (fun S : PowerSeries ℝ => PowerSeries.coeff n S)
    c5CentralSource_log_derivative_eq_twice_original_jets
  simpa [momentSeries] using h

/-- The central ten-mode residual is half the C5 zero-displacement source moment minus the
comparison power sum. This exact relation does not transport boxes from nonzero displacement. -/
theorem c5CentralResidual_eq_half_source_moment_sub_modes
    (ts : Fin 10 → ℝ) (n : ℕ) :
    completedNativeContour51Residual ts n =
      (completedSigmaDisplacedMoment 0 n) / 2 -
        tenModeMoment (fun i => ((ts i) ^ 2)⁻¹) n := by
  simp [completedNativeContour51Residual, completedSigmaDisplacedMoment]

theorem contour51TenModeBoxWidth_lt_budget (n : ℕ) (hn : n ≤ 5) :
    contour51TenModeBoxWidth n < contour51TenModeBoxWidthBudget n := by
  interval_cases n <;>
    norm_num [contour51TenModeBoxWidth, contour51TenModeBoxWidthBudget,
      highMoment, lowMoment, tenModeMoment, finitePowerMoment,
      scaleLower, scaleUpper, ordinateLower, ordinateUpper,
      Fin.sum_univ_succ]

/-- If an original-source jet lower bound clears the rational width budget, then
the residual is nonnegative for every exact height list inside the B2 boxes. -/
theorem completedNativeContour51Residual_nonneg_of_jet_margin
    (ts : Fin 10 → ℝ) (n : ℕ)
    (hboxes : ∀ i : Fin 10,
      ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i))
    (hjet : lowMoment n + contour51TenModeBoxWidthBudget n ≤
      completedSigmaLogJet 0 n)
    (hn : n ≤ 5) :
    0 ≤ completedNativeContour51Residual ts n := by
  let a : Fin 10 → ℝ := fun i => ((ts i) ^ 2)⁻¹
  have hbox : ∀ i : Fin 10, scaleLower i ≤ a i ∧ a i ≤ scaleUpper i :=
    contour51_scales_in_rational_boxes ts hboxes
  have hmode : tenModeMoment a n ≤ highMoment n :=
    tenModeMoment_le_highMoment_of_box_bounds a hbox n
  have hwidth := contour51TenModeBoxWidth_lt_budget n hn
  have hsource : highMoment n ≤ completedSigmaLogJet 0 n := by
    dsimp [contour51TenModeBoxWidth] at hwidth
    linarith
  unfold completedNativeContour51Residual
  dsimp [a] at hmode
  linarith

theorem contour51TenModeBoxWidth_zero_lt :
    contour51TenModeBoxWidth 0 < 14 / 1000000 := by
  simpa [contour51TenModeBoxWidthBudget] using
    contour51TenModeBoxWidth_lt_budget 0 (by norm_num)

theorem contour51TenModeBoxWidth_one_lt :
    contour51TenModeBoxWidth 1 < 9 / 100000000 := by
  simpa [contour51TenModeBoxWidthBudget] using
    contour51TenModeBoxWidth_lt_budget 1 (by norm_num)

theorem contour51TenModeBoxWidth_two_lt :
    contour51TenModeBoxWidth 2 < 6 / 10000000000 := by
  simpa [contour51TenModeBoxWidthBudget] using
    contour51TenModeBoxWidth_lt_budget 2 (by norm_num)

theorem contour51TenModeBoxWidth_three_lt :
    contour51TenModeBoxWidth 3 < 4 / 1000000000000 := by
  simpa [contour51TenModeBoxWidthBudget] using
    contour51TenModeBoxWidth_lt_budget 3 (by norm_num)

theorem contour51TenModeBoxWidth_four_lt :
    contour51TenModeBoxWidth 4 < 3 / 100000000000000 := by
  simpa [contour51TenModeBoxWidthBudget] using
    contour51TenModeBoxWidth_lt_budget 4 (by norm_num)

theorem contour51TenModeBoxWidth_five_lt :
    contour51TenModeBoxWidth 5 < 2 / 10000000000000000 := by
  simpa [contour51TenModeBoxWidthBudget] using
    contour51TenModeBoxWidth_lt_budget 5 (by norm_num)

#print axioms contour51TenModeBoxWidth_lt_budget
#print axioms completedNativeContour51Residual_nonneg_of_jet_margin
#print axioms c5CentralDisplacedProduct_eq_characteristic_square
#print axioms c5CentralDisplacedProduct_eq_continuation_square
#print axioms c5CentralSource_log_derivative_eq_twice_original_jets
#print axioms c5CentralSource_log_derivative_coeff_eq_twice_original_jet
#print axioms c5CentralResidual_eq_half_source_moment_sub_modes

end
end CarrySigmaObstruction
