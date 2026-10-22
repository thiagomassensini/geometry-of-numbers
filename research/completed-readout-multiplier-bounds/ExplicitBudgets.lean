import MultiplierBounds

namespace CarryReadoutBounds
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryFourthTail CarryMaterialParts CarryForcingResidual
open CarrySelfAdjointOperator NativeMomentOrthogonalization
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
local notation "h" => canonicalCompletedNativeLogDerivativeMoment

/-- Computable rational envelope replacing the previously unknown multiplier jets. -/
def explicitResponseConstant (r : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (r+1), (8192*8^j)*2^(r-j+1))+
  ∑ j ∈ Finset.range (r+1), (4:ℝ)^j*((r-j+1:ℕ):ℝ)*2^(r-j+2)

theorem response_constant_le (r : ℕ) : responseErrorConstant r ≤ explicitResponseConstant r := by
  unfold responseErrorConstant explicitResponseConstant
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (ordinary_multiplier_jet_bound j) (by positivity)
  · apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (clock_multiplier_jet_bound j)
      (Nat.cast_nonneg _)) (by positivity)

theorem explicit_moment_error (M : ℕ) (hM : 0 < M) (n : ℕ) :
    |h n-acceleratedObservedMoment M n| ≤
      5*explicitResponseConstant (2*n+1)/(4*(4*(M:ℝ)-1)^3) := by
  apply (accelerated_native_moment_error M hM n).trans
  apply div_le_div_of_nonneg_right _ (by
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
    have : 0 ≤ 4*(M:ℝ)-1 := by linarith
    positivity)
  exact mul_le_mul_of_nonneg_left (response_constant_le _) (by norm_num)

def explicitBilinearConstant (s : Fin 2) {N : ℕ} (a b : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, explicitResponseConstant (2*(i.val+j.val+s.val)+1)*|a i| * |b j|

theorem bilinear_constant_le (s : Fin 2) {N : ℕ} (a b : Fin N → ℝ) :
    bilinearErrorConstant s a b ≤ explicitBilinearConstant s a b := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (response_constant_le _)
    (abs_nonneg _)) (abs_nonneg _)

/-- Two independent inputs are controlled before specialization to the critical vector. -/
theorem explicit_bilinear_error (s : Fin 2) {N : ℕ} (a b : Fin N → ℝ)
    (M : ℕ) (hM : 0 < M) :
    |(∑ i, ∑ j, h (i.val+j.val+s.val)*a i*b j)-observedBilinear s a b M| ≤
      5*explicitBilinearConstant s a b/(4*(4*(M:ℝ)-1)^3) := by
  apply (accelerated_bilinear_error s a b M hM).trans
  apply div_le_div_of_nonneg_right _ (by
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
    have : 0 ≤ 4*(M:ℝ)-1 := by linarith
    positivity)
  exact mul_le_mul_of_nonneg_left (bilinear_constant_le s a b) (by norm_num)

theorem explicit_critical_error (s : Fin 2) (n M : ℕ) (hM : 0 < M) :
    |carryPairingPivot (hankelPairing (fun k => h (k+s.val))) n-
      acceleratedCriticalObservation s n M| ≤
      5*explicitBilinearConstant s (criticalCoefficients s n) (criticalCoefficients s n)/
        (4*(4*(M:ℝ)-1)^3) := by
  rw [critical_pivot_coefficients]
  exact explicit_bilinear_error s _ _ M hM

def secondEvenResidual (a : ℝ) : ℝ := h 2-2*a*h 1+a^2*h 0
def secondEvenObservation (a : ℝ) (M : ℕ) : ℝ :=
  acceleratedObservedMoment M 2-2*a*acceleratedObservedMoment M 1+a^2*acceleratedObservedMoment M 0

theorem second_even_residual_error (a : ℝ) (M : ℕ) (hM : 0 < M) :
    |secondEvenResidual a-secondEvenObservation a M| ≤
      5*(explicitResponseConstant 5+2*|a| * explicitResponseConstant 3+
          |a|^2*explicitResponseConstant 1)/(4*(4*(M:ℝ)-1)^3) := by
  have e0 := explicit_moment_error M hM 0
  have e1 := explicit_moment_error M hM 1
  have e2 := explicit_moment_error M hM 2
  norm_num only [mul_zero, zero_add, mul_one, show 2*2+1=5 by norm_num] at e0 e1 e2
  unfold secondEvenResidual secondEvenObservation
  rw [show h 2-2*a*h 1+a^2*h 0-(acceleratedObservedMoment M 2-
      2*a*acceleratedObservedMoment M 1+a^2*acceleratedObservedMoment M 0) =
    (h 2-acceleratedObservedMoment M 2)-2*a*(h 1-acceleratedObservedMoment M 1)+
      a^2*(h 0-acceleratedObservedMoment M 0) by ring]
  calc
    _ ≤ |h 2-acceleratedObservedMoment M 2|+2*|a| * |h 1-acceleratedObservedMoment M 1|+
        |a|^2*|h 0-acceleratedObservedMoment M 0| := by
      apply (abs_add_le _ _).trans
      have ht := norm_sub_le (h 2-acceleratedObservedMoment M 2) (2*a*(h 1-acceleratedObservedMoment M 1))
      norm_num only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ)<2)] at ht ⊢
      linarith
    _ ≤ (5*explicitResponseConstant 5/(4*(4*(M:ℝ)-1)^3))+
        2*|a| * (5*explicitResponseConstant 3/(4*(4*(M:ℝ)-1)^3))+
        |a|^2*(5*explicitResponseConstant 1/(4*(4*(M:ℝ)-1)^3)) := by
      gcongr
    _ = _ := by ring

end
end CarryReadoutBounds
