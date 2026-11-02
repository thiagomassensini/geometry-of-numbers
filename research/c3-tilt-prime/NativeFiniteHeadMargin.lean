import NativeProductTransport
import C3UniformRegression

/-!
# Margem eventual da cabeça literal: regressão par de dimensão dois

Reutiliza a cota já certificada da fonte C3 completa na PR70 e a convergência
uniforme dos orçamentos de cauda da PR143. A margem é demonstrada para uma
família de direções, antes de selecionar a direção crítica. Não se reclama um
novo sinal canônico ou uma lei de ordem arbitrária: a cota anterior para a fonte
completa já implica o sinal finito pela ponte crítica.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator CarryUniformSource Filter Matrix
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem c3_original_pair_lower (t : ℝ) (ht : |t| ≤ 1) :
    (1/10^8-1/10^13:ℝ) <
      matrixPair (coefficientBlock (sourceKernel nativeC false) 2) (twoMonic t) (twoMonic t) := by
  have h := native_regrouped64_total_lower t ht
  have he : regroupedHead64 + regroupedTail64 = fun n => (nativeC n : ℂ) := by
    funext n
    exact regrouped_source n
  rw [he] at h
  have hm := sourceKernel_map Complex.ofRealHom nativeC false
  change sourceKernel (fun n => (nativeC n : ℂ)) false = _ at hm
  have hp : coefficientPair (fun n => (nativeC n : ℂ)) (fun n => (nativeC n : ℂ)) false 2
      (twoMonic t) (twoMonic t) =
        (matrixPair (coefficientBlock (sourceKernel nativeC false) 2) (twoMonic t) (twoMonic t) : ℂ) := by
    unfold coefficientPair
    change complexPair (coefficientBlock (sourceKernel (fun n => (nativeC n : ℂ)) false) 2) _ _ = _
    rw [hm, coefficientBlock_map, complexPair_real]
  rw [hp] at h
  simpa only [Complex.ofReal_re] using h

theorem twoMonic_coordMass_le (t : ℝ) (ht : |t| ≤ 1) : coordMass (twoMonic t) ≤ 2 := by
  simp only [coordMass, Fin.sum_univ_two, twoMonic, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, abs_one]
  linarith

theorem c3_literal_monic_margin_eventually :
    ∀ᶠ M : ℕ in atTop, ∀ t : ℝ, |t| ≤ 1 →
      literalHead M 0 ≠ 0 ∧
      (9/10^9:ℝ) < (literalTerm M M true true false 2 (twoMonic t) (twoMonic t)).re ∧
      20 * literalErrorBudget M M false 2 (twoMonic t) (twoMonic t) <
        (literalTerm M M true true false 2 (twoMonic t) (twoMonic t)).re := by
  have hE : ∀ᶠ M : ℕ in atTop, normalizedError M M false 2 < (1/10^10:ℝ) :=
    (normalizedError_tendsto_zero false 2).eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hE, literal_head_constant_eventually_ne] with M hM hunit
  intro t ht
  let z := twoMonic t
  have hmass : coordMass z ≤ 2 := twoMonic_coordMass_le t ht
  have hmass0 : 0 ≤ coordMass z := coordMass_nonneg z
  have hsq : coordMass z * coordMass z ≤ 4 := by nlinarith
  have hp : normalizedError M M false 2 * (coordMass z * coordMass z) ≤ (1/10^10:ℝ) * 4 :=
    mul_le_mul hM.le hsq (mul_self_nonneg _) (by norm_num)
  have hbudget0 := literalErrorBudget_normed M M false 2 z z
  have hbudget : literalErrorBudget M M false 2 z z ≤ (4/10^10:ℝ) := by nlinarith
  have hnorm := literal_error_bound M M false 2 z z
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).2
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hlower := c3_original_pair_lower t ht
  change (1/10^8-1/10^13:ℝ) < matrixPair (coefficientBlock (sourceKernel nativeC false) 2) z z at hlower
  refine ⟨hunit, ?_, ?_⟩ <;> norm_num at * <;> linarith

/-- The same source-derived margin at the actual PR41/PR70 critical direction,
with the product identity and both complete factors retained. -/
theorem c3_literal_critical_product_margin_eventually :
    ∀ᶠ M : ℕ in atTop,
      let z := monicSourceDirection nativeC nativeH 0 1
      literalHead M 0 ≠ 0 ∧
      20 * literalErrorBudget M M false 2 z z < (literalTerm M M true true false 2 z z).re ∧
      complexPair (literalProductHeadBlock M false 2) (fun i => (z i:ℂ)) (fun i => (z i:ℂ)) +
        complexPair (literalProductCorrectionBlock M false 2) (fun i => (z i:ℂ)) (fun i => (z i:ℂ)) =
          (nativeC 0 * nativeSourceSchurRemainder 0 1 : ℝ) := by
  filter_upwards [c3_literal_monic_margin_eventually] with M hM
  let t : ℝ := -(2:ℝ)*nativeC 2/nativeC 1
  have ht : |t| ≤ 1 := native_monic_two_coordinate_bound
  have hv : monicSourceDirection nativeC nativeH 0 1 = twoMonic t :=
    native_monic_two_direction native_even_one_isUnit_from_source
  have hm := hM t ht
  have hp := literal_product_critical M hm.1 false 1 native_even_one_isUnit_from_source
  rw [← hv] at hm
  exact ⟨hm.1, hm.2.2, hp⟩

#print axioms c3_original_pair_lower
#print axioms c3_literal_monic_margin_eventually
#print axioms c3_literal_critical_product_margin_eventually
end
end CarrySourceBezout
