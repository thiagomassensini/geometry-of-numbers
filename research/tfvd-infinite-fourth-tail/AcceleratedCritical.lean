import AcceleratedClock

/-! Quantitative acceleration on the SAME canonical readout and exact PR41
critical coefficients. The complete denominator, dressing and derivative
are never recomputed from a truncated characteristic. -/
namespace CarryFourthTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryMaterialParts CarrySelfAdjointOperator NativeMomentOrthogonalization CarryForcingResidual
open CarryMaterialMixedSchurComparison
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local notation "h" => canonicalCompletedNativeLogDerivativeMoment

def acceleratedResponseObservation (M : ℕ) (t : ℝ) : ℂ :=
  ordinaryMultiplier t*(1+acceleratedOrdinaryHead M t)+clockMultiplier t*acceleratedClockHead M t

theorem accelerated_response_analytic (M : ℕ) :
    AnalyticAt ℝ (acceleratedResponseObservation M) 0 :=
  (ordinary_multiplier_analytic.mul (analyticAt_const.add (accelerated_ordinary_head_analytic M))).add
    (clock_multiplier_analytic.mul (accelerated_clock_head_analytic M))

theorem accelerated_response_tail_exact (M : ℕ) :
    (fun t => carryMaterialNormalizedResponse t-acceleratedResponseObservation M t) =
      fun t => ordinaryMultiplier t*acceleratedOrdinaryTail M t+clockMultiplier t*acceleratedClockTail M t := by
  funext t
  rw [normalized_response_channels]
  simp only [acceleratedResponseObservation, acceleratedOrdinaryTail, acceleratedClockTail]
  ring

def acceleratedResponseBudget (r M : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (r+1), ‖rJet j ordinaryMultiplier‖*acceleratedOrdinaryBudget (r-j) M)+
    ∑ j ∈ Finset.range (r+1), ‖rJet j clockMultiplier‖*acceleratedClockBudget (r-j) M

theorem accelerated_response_jet_error (r M : ℕ) (hM : 0 < M) :
    ‖rJet r carryMaterialNormalizedResponse-rJet r (acceleratedResponseObservation M)‖ ≤
      acceleratedResponseBudget r M := by
  rw [← rJet_sub material_response_real_analytic (accelerated_response_analytic M),
    accelerated_response_tail_exact,
    rJet_add (f:=fun t => ordinaryMultiplier t*acceleratedOrdinaryTail M t)
      (g:=fun t => clockMultiplier t*acceleratedClockTail M t)
      (ordinary_multiplier_analytic.mul (accelerated_ordinary_tail_analytic M))
      (clock_multiplier_analytic.mul (accelerated_clock_tail_analytic M))]
  exact (norm_add_le _ _).trans (add_le_add
    (rJet_mul_bound ordinary_multiplier_analytic (accelerated_ordinary_tail_analytic M) _
      (fun j => accelerated_ordinary_jet_bound j M hM) r)
    (rJet_mul_bound clock_multiplier_analytic (accelerated_clock_tail_analytic M) _
      (fun j => accelerated_clock_jet_bound j M hM) r))

theorem accelerated_response_budget_rate (r M : ℕ) :
    acceleratedResponseBudget r M = 5*responseErrorConstant r/(4*(4*(M:ℝ)-1)^3) := by
  have ha : 4*(M:ℝ)-1 ≠ 0 := by
    by_cases hz : M=0
    · norm_num [hz]
    · have hmN : 1 ≤ M := by omega
      have hm : (1:ℝ) ≤ M := by exact_mod_cast hmN
      linarith
  have ho (j : ℕ) : acceleratedOrdinaryBudget j M =
      (5/(4*(4*(M:ℝ)-1)^3))*2^(j+1) := by
    unfold acceleratedOrdinaryBudget
    rw [pow_succ]
    field_simp [ha]
    ring
  have hc (j : ℕ) : acceleratedClockBudget j M =
      (5/(4*(4*(M:ℝ)-1)^3))*((j+1:ℕ):ℝ)*2^(j+2) := by
    unfold acceleratedClockBudget
    rw [show j+2=(j+1)+1 by omega, pow_succ]
    field_simp [ha]
    ring
  unfold acceleratedResponseBudget
  simp_rw [ho, hc]
  rw [show (5*responseErrorConstant r/(4*(4*(M:ℝ)-1)^3)) =
      (5/(4*(4*(M:ℝ)-1)^3))*responseErrorConstant r by ring]
  simp only [responseErrorConstant, mul_add, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

def acceleratedObservedMoment (M n : ℕ) : ℝ :=
  (rJet (2*n+1) (acceleratedResponseObservation M)).re

theorem accelerated_native_moment_error (M : ℕ) (hM : 0 < M) (n : ℕ) :
    |h n-acceleratedObservedMoment M n| ≤
      5*responseErrorConstant (2*n+1)/(4*(4*(M:ℝ)-1)^3) := by
  have he := accelerated_response_jet_error (2*n+1) M hM
  rw [native_moment_jet, accelerated_response_budget_rate] at he
  exact (Complex.abs_re_le_norm _).trans he

def observedBilinear (s : Fin 2) {N : ℕ} (a b : Fin N → ℝ) (M : ℕ) : ℝ :=
  ∑ i, ∑ j, acceleratedObservedMoment M (i.val+j.val+s.val)*a i*b j

def bilinearErrorConstant (s : Fin 2) {N : ℕ} (a b : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, responseErrorConstant (2*(i.val+j.val+s.val)+1)*|a i| * |b j|

/-- Two independent arguments, not merely diagonal norm control. -/
theorem accelerated_bilinear_error (s : Fin 2) {N : ℕ} (a b : Fin N → ℝ)
    (M : ℕ) (hM : 0 < M) :
    |(∑ i, ∑ j, h (i.val+j.val+s.val)*a i*b j)-observedBilinear s a b M| ≤
      5*bilinearErrorConstant s a b/(4*(4*(M:ℝ)-1)^3) := by
  unfold observedBilinear
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ∑ j, (5*responseErrorConstant (2*(i.val+j.val+s.val)+1)/(4*(4*(M:ℝ)-1)^3))*|a i| * |b j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [← sub_mul, ← sub_mul, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (accelerated_native_moment_error M hM _) (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by
      simp only [bilinearErrorConstant, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

def acceleratedCriticalObservation (s : Fin 2) (n M : ℕ) : ℝ :=
  observedBilinear s (criticalCoefficients s n) (criticalCoefficients s n) M

theorem accelerated_critical_error (s : Fin 2) (n M : ℕ) (hM : 0 < M) :
    |carryPairingPivot (hankelPairing (fun k => h (k+s.val))) n-
      acceleratedCriticalObservation s n M| ≤ 5*criticalErrorConstant s n/(4*(4*(M:ℝ)-1)^3) := by
  rw [critical_pivot_coefficients]
  exact accelerated_bilinear_error s _ _ M hM

/-- Exact gain of the error envelope. This is independent of the pivot sign. -/
theorem critical_budget_improvement (s : Fin 2) (n M : ℕ) (hM : 0 < M) :
    5*criticalErrorConstant s n/(4*(4*(M:ℝ)-1)^3) =
      (5/(4*(M:ℝ)-1)^2)*criticalErrorBudget s n M := by
  rw [critical_budget_rate]
  have ha : 4*(M:ℝ)-1 ≠ 0 := by
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
    linarith
  field_simp

theorem accelerated_critical_cutoff_suffices (s : Fin 2) (n M : ℕ) (hM : 0 < M) (ε : ℝ)
    (hcut : 5*criticalErrorConstant s n ≤ ε*(4*(4*(M:ℝ)-1)^3)) :
    |carryPairingPivot (hankelPairing (fun k => h (k+s.val))) n-
      acceleratedCriticalObservation s n M| ≤ ε := by
  apply (accelerated_critical_error s n M hM).trans
  apply (div_le_iff₀ ?_).2 hcut
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have ha : 0 < 4*(M:ℝ)-1 := by linarith
  positivity
end
end CarryFourthTail
