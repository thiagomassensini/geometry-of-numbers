import SourceBlocks
import NativeRepartition64

namespace CarrySourceDimensionThree
open CarrySourceBezout CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem even_last_entry (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c false) 3 2 2 =
      -5*c 0*c 5 - 3*c 1*c 4 - c 2*c 3 := by
  norm_num [coefficientBlock, sourceKernel, bezout, right, divided, sourceSeries,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_derivative, PowerSeries.coeff_X, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_X_mul, Finset.sum_range_succ]
  ring

theorem odd_last_entry (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c true) 3 2 2 =
      -6*c 0*c 6 - 4*c 1*c 5 - 2*c 2*c 4 + 3*(c 3)^2 := by
  have hd : PowerSeries.constantCoeff (PowerSeries.derivative ℝ (PowerSeries.mk c)) = c 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [PowerSeries.coeff_derivative]
  norm_num [coefficientBlock, sourceKernel, bezout, right, divided, sourceSeries,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_derivative, Finset.sum_range_succ, hd]
  ring

def perturb (c : ℕ → ℝ) (n : ℕ) (d : ℝ) : ℕ → ℝ :=
  fun j => if j=n then c j+d else c j

theorem even_last_perturb (c : ℕ → ℝ) (d : ℝ) :
    coefficientBlock (sourceKernel (perturb c 5 d) false) 3 2 2 =
      coefficientBlock (sourceKernel c false) 3 2 2 - 5*c 0*d := by
  rw [even_last_entry,even_last_entry]
  simp [perturb]
  ring

theorem odd_last_perturb (c : ℕ → ℝ) (d : ℝ) :
    coefficientBlock (sourceKernel (perturb c 6 d) true) 3 2 2 =
      coefficientBlock (sourceKernel c true) 3 2 2 - 6*c 0*d := by
  rw [odd_last_entry,odd_last_entry]
  simp [perturb]
  ring

theorem even_source_data_insufficient (c : ℕ → ℝ) (hc : c 0 ≠ 0) :
    ∃ dPos dNeg : ℕ → ℝ,
      (∀ j < 5, dPos j = c j ∧ dNeg j = c j) ∧
      0 < coefficientBlock (sourceKernel dPos false) 3 2 2 ∧
      coefficientBlock (sourceKernel dNeg false) 3 2 2 < 0 := by
  let E := coefficientBlock (sourceKernel c false) 3 2 2
  let a := (E-1)/(5*c 0)
  let b := (E+1)/(5*c 0)
  refine ⟨perturb c 5 a,perturb c 5 b,?_,?_,?_⟩
  · intro j hj
    simp [perturb, Nat.ne_of_lt hj]
  · rw [even_last_perturb]
    dsimp [a,E]
    field_simp [hc]
    ring_nf
    norm_num
  · rw [even_last_perturb]
    dsimp [b,E]
    field_simp [hc]
    ring_nf
    norm_num

theorem odd_source_data_insufficient (c : ℕ → ℝ) (hc : c 0 ≠ 0) :
    ∃ dPos dNeg : ℕ → ℝ,
      (∀ j < 6, dPos j = c j ∧ dNeg j = c j) ∧
      0 < coefficientBlock (sourceKernel dPos true) 3 2 2 ∧
      coefficientBlock (sourceKernel dNeg true) 3 2 2 < 0 := by
  let E := coefficientBlock (sourceKernel c true) 3 2 2
  let a := (E-1)/(6*c 0)
  let b := (E+1)/(6*c 0)
  refine ⟨perturb c 6 a,perturb c 6 b,?_,?_,?_⟩
  · intro j hj
    simp [perturb, Nat.ne_of_lt hj]
  · rw [odd_last_perturb]
    dsimp [a,E]
    field_simp [hc]
    ring_nf
    norm_num
  · rw [odd_last_perturb]
    dsimp [b,E]
    field_simp [hc]
    ring_nf
    norm_num

#print axioms even_last_entry
#print axioms odd_last_entry
#print axioms even_source_data_insufficient
#print axioms odd_source_data_insufficient
end
end CarrySourceDimensionThree
