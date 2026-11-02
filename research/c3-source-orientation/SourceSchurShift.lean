import SourceDependency

namespace CarrySourceDimensionThree
open CarrySourceBezout CarrySelfAdjointOperator
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

theorem even_three (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c false) 3 =
      !![-c 0*c 1, -2*c 0*c 2, -3*c 0*c 3;
         -2*c 0*c 2, -3*c 0*c 3-c 1*c 2, -4*c 0*c 4-2*c 1*c 3;
         -3*c 0*c 3, -4*c 0*c 4-2*c 1*c 3, -5*c 0*c 5-3*c 1*c 4-c 2*c 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coefficientBlock, sourceKernel, bezout, right, divided, sourceSeries,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      PowerSeries.coeff_derivative, PowerSeries.coeff_X, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_X_mul, Finset.sum_range_succ] <;> ring

theorem odd_three (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c true) 3 =
      !![c 1^2-2*c 0*c 2, c 1*c 2-3*c 0*c 3, c 1*c 3-4*c 0*c 4;
         c 1*c 2-3*c 0*c 3, 2*c 2^2-2*c 1*c 3-4*c 0*c 4, -5*c 0*c 5-3*c 1*c 4+2*c 2*c 3;
         c 1*c 3-4*c 0*c 4, -5*c 0*c 5-3*c 1*c 4+2*c 2*c 3, -6*c 0*c 6-4*c 1*c 5-2*c 2*c 4+3*(c 3)^2] := by
  have hd : PowerSeries.constantCoeff (PowerSeries.derivative ℝ (PowerSeries.mk c)) = c 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [PowerSeries.coeff_derivative]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coefficientBlock, sourceKernel, bezout, right, divided, sourceSeries,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      PowerSeries.coeff_derivative, Finset.sum_range_succ, hd] <;> ring

theorem even_prefix_unchanged (c : ℕ → ℝ) (d : ℝ) :
    coefficientBlock (sourceKernel (perturb c 5 d) false) 2 =
      coefficientBlock (sourceKernel c false) 2 := by
  rw [source_even_two,source_even_two]
  simp [perturb]

theorem odd_prefix_unchanged (c : ℕ → ℝ) (d : ℝ) :
    coefficientBlock (sourceKernel (perturb c 6 d) true) 2 =
      coefficientBlock (sourceKernel c true) 2 := by
  rw [source_odd_two,source_odd_two]
  simp [perturb]

theorem even_coupling_unchanged (c : ℕ → ℝ) (d : ℝ) :
    sourceCoupling (perturb c 5 d) false 2 = sourceCoupling c false 2 := by
  funext i
  fin_cases i <;> simp [sourceCoupling,even_three,perturb]

theorem odd_coupling_unchanged (c : ℕ → ℝ) (d : ℝ) :
    sourceCoupling (perturb c 6 d) true 2 = sourceCoupling c true 2 := by
  funext i
  fin_cases i <;> simp [sourceCoupling,odd_three,perturb]

theorem even_schur_shift (c : ℕ → ℝ) (d : ℝ) :
    sourceSchur (perturb c 5 d) false 2 = sourceSchur c false 2 - 5*c 0*d := by
  unfold sourceSchur
  rw [even_prefix_unchanged, even_coupling_unchanged]
  have h := even_last_perturb c d
  change coefficientBlock (sourceKernel (perturb c 5 d) false) (2+1) (Fin.last 2) (Fin.last 2) = coefficientBlock (sourceKernel c false) (2+1) (Fin.last 2) (Fin.last 2) - 5*c 0*d at h
  rw [h]
  ring

theorem odd_schur_shift (c : ℕ → ℝ) (d : ℝ) :
    sourceSchur (perturb c 6 d) true 2 = sourceSchur c true 2 - 6*c 0*d := by
  unfold sourceSchur
  rw [odd_prefix_unchanged, odd_coupling_unchanged]
  have h := odd_last_perturb c d
  change coefficientBlock (sourceKernel (perturb c 6 d) true) (2+1) (Fin.last 2) (Fin.last 2) = coefficientBlock (sourceKernel c true) (2+1) (Fin.last 2) (Fin.last 2) - 6*c 0*d at h
  rw [h]
  ring

#print axioms even_three
#print axioms odd_three
#print axioms even_schur_shift
#print axioms odd_schur_shift
/-- Algebraic control only: no assertion that the modified sequences are
physical C3 sources. The full preceding block and coupling are unchanged. -/
theorem even_schur_data_insufficient (c : ℕ → ℝ) (hc : c 0 ≠ 0) :
    ∃ dPos dNeg : ℕ → ℝ,
      (∀ j < 5, dPos j = c j ∧ dNeg j = c j) ∧
      coefficientBlock (sourceKernel dPos false) 2 = coefficientBlock (sourceKernel c false) 2 ∧
      coefficientBlock (sourceKernel dNeg false) 2 = coefficientBlock (sourceKernel c false) 2 ∧
      sourceCoupling dPos false 2 = sourceCoupling c false 2 ∧
      sourceCoupling dNeg false 2 = sourceCoupling c false 2 ∧
      0 < sourceSchur dPos false 2 ∧ sourceSchur dNeg false 2 < 0 := by
  let E := sourceSchur c false 2
  let a := (E-1)/(5*c 0)
  let b := (E+1)/(5*c 0)
  refine ⟨perturb c 5 a,perturb c 5 b,?_,even_prefix_unchanged _ _,even_prefix_unchanged _ _,
    even_coupling_unchanged _ _,even_coupling_unchanged _ _,?_,?_⟩
  · intro j hj
    simp [perturb, Nat.ne_of_lt hj]
  · rw [even_schur_shift]
    dsimp [a,E]
    field_simp [hc]
    ring_nf
    norm_num
  · rw [even_schur_shift]
    dsimp [b,E]
    field_simp [hc]
    ring_nf
    norm_num

theorem odd_schur_data_insufficient (c : ℕ → ℝ) (hc : c 0 ≠ 0) :
    ∃ dPos dNeg : ℕ → ℝ,
      (∀ j < 6, dPos j = c j ∧ dNeg j = c j) ∧
      coefficientBlock (sourceKernel dPos true) 2 = coefficientBlock (sourceKernel c true) 2 ∧
      coefficientBlock (sourceKernel dNeg true) 2 = coefficientBlock (sourceKernel c true) 2 ∧
      sourceCoupling dPos true 2 = sourceCoupling c true 2 ∧
      sourceCoupling dNeg true 2 = sourceCoupling c true 2 ∧
      0 < sourceSchur dPos true 2 ∧ sourceSchur dNeg true 2 < 0 := by
  let E := sourceSchur c true 2
  let a := (E-1)/(6*c 0)
  let b := (E+1)/(6*c 0)
  refine ⟨perturb c 6 a,perturb c 6 b,?_,odd_prefix_unchanged _ _,odd_prefix_unchanged _ _,
    odd_coupling_unchanged _ _,odd_coupling_unchanged _ _,?_,?_⟩
  · intro j hj
    simp [perturb, Nat.ne_of_lt hj]
  · rw [odd_schur_shift]
    dsimp [a,E]
    field_simp [hc]
    ring_nf
    norm_num
  · rw [odd_schur_shift]
    dsimp [b,E]
    field_simp [hc]
    ring_nf
    norm_num

#print axioms even_schur_data_insufficient
#print axioms odd_schur_data_insufficient

end
end CarrySourceDimensionThree
