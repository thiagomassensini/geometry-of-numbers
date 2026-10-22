import ResponseTails
import CriticalGreen

/-! A tail budget on the EXACT original PR41 monic direction. No sign of
its pivot, no replacement Gram and no spectral data occur as inputs. -/
namespace CarryCellTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialParts CarrySelfAdjointOperator NativeMomentOrthogonalization CarryForcingResidual
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local notation "h" => canonicalCompletedNativeLogDerivativeMoment

/-- Finite observation on the unchanged PR41 direction, retaining all i,j. -/
def criticalObservation (s : Fin 2) (n M : ℕ) : ℝ :=
  ∑ i : Fin (n+1), ∑ j : Fin (n+1),
    observedMoment M (i.val+j.val+s.val)*criticalCoefficients s n i*criticalCoefficients s n j

def criticalErrorBudget (s : Fin 2) (n M : ℕ) : ℝ :=
  ∑ i : Fin (n+1), ∑ j : Fin (n+1),
    responseBudget (2*(i.val+j.val+s.val)+1) M*
      |criticalCoefficients s n i| * |criticalCoefficients s n j|

/-- Algebraic identity from PR41, valid even when some pivots are zero or
negative. Only interpreting this as a norm would require a sign premise. -/
theorem critical_pivot_coefficients (s : Fin 2) (n : ℕ) :
    carryPairingPivot (hankelPairing (fun k => h (k+s.val))) n =
      ∑ i : Fin (n+1), ∑ j : Fin (n+1),
        h (i.val+j.val+s.val)*criticalCoefficients s n i*criticalCoefficients s n j := by
  rw [← orthogonalPolynomial_self, ← criticalPolynomial_exact s n,
    momentForm_coefficients]
  rfl

theorem exact_critical_error (s : Fin 2) (n M : ℕ) (hM : 0 < M) :
    |carryPairingPivot (hankelPairing (fun k => h (k+s.val))) n-criticalObservation s n M| ≤
      criticalErrorBudget s n M := by
  rw [critical_pivot_coefficients]
  unfold criticalObservation criticalErrorBudget
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [← sub_mul, ← sub_mul, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (native_moment_error M hM _) (abs_nonneg _)) (abs_nonneg _)

/-- Dependence on the cell cutoff has been isolated from every native
coefficient. The constant is exact and may be poorly conditioned in n. -/
def responseErrorConstant (r : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (r+1), ‖rJet j ordinaryMultiplier‖*2^(r-j+1))+
    ∑ j ∈ Finset.range (r+1), ‖rJet j clockMultiplier‖*((r-j+1:ℕ):ℝ)*2^(r-j+2)

theorem response_budget_rate (r M : ℕ) :
    responseBudget r M = responseErrorConstant r/(4*(4*(M:ℝ)-1)) := by
  simp only [responseBudget, responseErrorConstant, ordinaryBudget, clockBudget,
    add_div, Finset.sum_div, mul_div_assoc, mul_assoc]

def criticalErrorConstant (s : Fin 2) (n : ℕ) : ℝ :=
  ∑ i : Fin (n+1), ∑ j : Fin (n+1),
    responseErrorConstant (2*(i.val+j.val+s.val)+1)*
      |criticalCoefficients s n i| * |criticalCoefficients s n j|

theorem critical_budget_rate (s : Fin 2) (n M : ℕ) :
    criticalErrorBudget s n M = criticalErrorConstant s n/(4*(4*(M:ℝ)-1)) := by
  simp only [criticalErrorBudget, criticalErrorConstant, response_budget_rate,
    Finset.sum_div, div_mul_eq_mul_div]

/-- An explicit precision test on the original residual, independent of its
sign. This is not an assertion that the required cutoff is economical. -/
theorem critical_cutoff_suffices (s : Fin 2) (n M : ℕ) (hM : 0 < M) (ε : ℝ)
    (hcut : criticalErrorConstant s n ≤ ε*(4*(4*(M:ℝ)-1))) :
    |carryPairingPivot (hankelPairing (fun k => h (k+s.val))) n-criticalObservation s n M| ≤ ε := by
  apply (exact_critical_error s n M hM).trans
  rw [critical_budget_rate]
  apply (div_le_iff₀ ?_).2 hcut
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  linarith

/-- Second even direction is a regression, not a new positivity premise. -/
theorem second_even_error (M : ℕ) (hM : 0 < M) :
    |(h 2-h 1^2/h 0)-criticalObservation 0 1 M| ≤
      criticalErrorConstant 0 1/(4*(4*(M:ℝ)-1)) := by
  have he := exact_critical_error 0 1 M hM
  rw [critical_budget_rate] at he
  convert he using 1
  simp [carryPairingPivot, hankelPairing, carryPairingRemainder]
  ring
end
end CarryCellTail
