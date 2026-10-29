import SourceBalance37

namespace CarryForcingResidual
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCompletedGreenBalance CarryMaterialClockCouplingComparison
open CarryMaterialGreenPairComparison CarryMaterialResponseComparison
open CarryMaterialPositiveResidualComparison
open CarrySelfAdjointOperator
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem forcing_scalar_zero_ne : carryMaterialClockForcingScalar 0 ≠ 0 := by
  intro h
  have hv := carryMaterialForcingVector_origin_ne_zero
  apply hv
  simp [carryMaterialForcingVector, carryMaterialClockForcingPair, h]

def centeredCoefficients {N : ℕ} (c : Fin N → ℂ) (t : Fin N → ℝ) : Fin (N+1) → ℂ :=
  Fin.cons (-(∑ i, c i*carryMaterialClockForcingScalar (t i))/carryMaterialClockForcingScalar 0) c
def centeredParameters {N : ℕ} (t : Fin N → ℝ) : Fin (N+1) → ℝ := Fin.cons 0 t

theorem centeredCoefficients_injective {N : ℕ} (t : Fin N → ℝ) :
    Function.Injective (fun c : Fin N → ℂ => centeredCoefficients c t) := by
  intro c d h
  funext i
  exact congrFun h i.succ

/-- Exact vector cancellation of the coefficient Gram's forcing channel.
The complete reduced forcing PAIR is deliberately kept separate below. -/
theorem forcing_vector_centered {N : ℕ} (c : Fin N → ℂ) (t : Fin N → ℝ) :
    (∑ i, centeredCoefficients c t i • carryMaterialForcingVector (centeredParameters t i)) = 0 := by
  simp only [carryMaterialForcingVector, carryMaterialClockForcingPair,
    Fin.sum_univ_succ, centeredCoefficients, centeredParameters, Fin.cons_zero, Fin.cons_succ,
    smul_smul]
  rw [← Finset.sum_smul]
  rw [← add_smul]
  have h := forcing_scalar_zero_ne
  rw [div_mul_cancel₀ _ h, neg_add_cancel, zero_smul]

/-- Same two independently synthesized families in the original forcing
coefficient form. Zero here is not a statement that the physical pair is zero. -/
theorem forcing_kernel_centered {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ) :
    (∑ i, ∑ j, conj (centeredCoefficients c t i)*
      carryMaterialForcingGreenKernel (centeredParameters t i) (centeredParameters u j)*
        centeredCoefficients d u j) = 0 := by
  rw [carryMaterialForcingGreen_bilinear, forcing_vector_centered, forcing_vector_centered,
    inner_zero_left, mul_zero]

theorem completed_centered {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ) :
    (∑ i, ∑ j, conj (centeredCoefficients c t i)*
      completedCoefficient (centeredParameters t i) (centeredParameters u j)*centeredCoefficients d u j) =
      ∑ i, ∑ j, conj (c i)*completedCoefficient (t i) (u j)*d j := by
  rw [Fin.sum_univ_succ]
  simp only [centeredCoefficients, centeredParameters, Fin.cons_zero, Fin.cons_succ,
    completedCoefficient, mul_zero, zero_mul, Complex.ofReal_zero,
    Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp

/-- Pullback of the WHOLE PR37 remainder. All forcing crosses and the
hidden readout complement remain in the physically defined remainder. -/
theorem remainder_centered_bilinear {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ) :
    (∑ i, ∑ j, conj (centeredCoefficients c t i)*
      remainderCoefficient (centeredParameters t i) (centeredParameters u j)*centeredCoefficients d u j) =
      ∑ i, ∑ j, conj (c i)*completedCoefficient (t i) (u j)*d j := by
  simp only [remainderCoefficient, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [forcing_kernel_centered, sub_zero, completed_centered]

/-- This chart divides only the LITERAL factors of the original Green
identity. It changes the input coefficients, not the source or metric. -/
def regularInput {N : ℕ} (c : Fin N → ℂ) (t : Fin N → ℝ) : Fin N → ℂ :=
  fun i => c i/((t i:ℂ)*baseTwoCanonicalResponse (t i))

theorem regularInput_exact {N : ℕ} (c : Fin N → ℂ) (t : Fin N → ℝ)
    (ht : ∀ i, t i ≠ 0) (hF : ∀ i, baseTwoCanonicalResponse (t i) ≠ 0) (i : Fin N) :
    regularInput c t i*(t i:ℂ)*baseTwoCanonicalResponse (t i) = c i := by
  have hi : (t i:ℂ) ≠ 0 := by exact_mod_cast ht i
  unfold regularInput
  field_simp [hF i]

theorem physical_pullback_exact {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ)
    (ht : ∀ i, t i ≠ 0) (hu : ∀ j, u j ≠ 0)
    (hFt : ∀ i, baseTwoCanonicalResponse (t i) ≠ 0)
    (hFu : ∀ j, baseTwoCanonicalResponse (u j) ≠ 0) :
    (∑ i, ∑ j, conj (centeredCoefficients (regularInput c t) t i)*
      remainderCoefficient (centeredParameters t i) (centeredParameters u j)*
        centeredCoefficients (regularInput d u) u j) =
      (2:ℂ)*(carryMaterialResponseScale:ℂ)^2*
        ∑ i, ∑ j, conj (c i)*(carryMaterialRealResidual (t i) (u j):ℂ)*d j := by
  rw [remainder_centered_bilinear, completed_coefficient_bilinear]
  simp_rw [regularInput_exact c t ht hFt, regularInput_exact d u hu hFu]

end
end CarryForcingResidual
