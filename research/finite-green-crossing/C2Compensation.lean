import IncrementLimit
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy

namespace CarryFiniteGreen
open CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarrySelfAdjointOperator
open Filter Topology Set
noncomputable section
set_option autoImplicit false

theorem c2_weight_pos : (0 : ℝ)<1/Real.sqrt 2 := by positivity

theorem c2_weight_lt_one : (1 : ℝ)/Real.sqrt 2<1 := by
  have h : 1<Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  exact (div_lt_one (by positivity : (0 : ℝ)<Real.sqrt 2)).mpr h

/-- The sign input is h0 only, already independently certified. This is not
an assumption about a new Schur pivot or an all-order Hankel. -/
theorem c2_mixed_limit_pos (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0) :
    0<canonicalCompletedNativeLogDerivativeMoment 0*greenBudget (1/Real.sqrt 2) := by
  have hj := c2_green_budget_gt_half
  exact mul_pos hh0 (by linarith)

theorem c2_bulk_limit_neg (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0) :
    canonicalCompletedNativeLogDerivativeMoment 0*(1-2*greenBudget (1/Real.sqrt 2))<0 := by
  have hj := c2_green_budget_gt_half
  exact mul_neg_of_pos_of_neg hh0 (by linarith)

theorem c2_eventually_mixed_positive (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0) :
    ∀ᶠ k : ℕ in atTop,
      0<(physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
        (reconstructedResidual 0 (1/Real.sqrt 2) k initialInput)).re :=
  (mixed_energy_limit _ c2_weight_pos c2_weight_lt_one).eventually
    (Ioi_mem_nhds (c2_mixed_limit_pos hh0))

theorem c2_eventually_bulk_negative (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0) :
    ∀ᶠ k : ℕ in atTop,
      (physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
        (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)).re<0 :=
  (bulk_energy_limit _ c2_weight_pos c2_weight_lt_one).eventually
    (Iio_mem_nhds (c2_bulk_limit_neg hh0))

theorem c2_eventually_compensates (hh0 : 0<canonicalCompletedNativeLogDerivativeMoment 0) :
    ∀ᶠ k : ℕ in atTop,
      (physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
        (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)).re<0 ∧
      0<(physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
        (reconstructedResidual 0 (1/Real.sqrt 2) k initialInput)).re ∧
      -(physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
        (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)).re<
        2*(physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
          (reconstructedResidual 0 (1/Real.sqrt 2) k initialInput)).re := by
  have hs := source_energy_limit.eventually (Ioi_mem_nhds hh0)
  filter_upwards [c2_eventually_bulk_negative hh0,c2_eventually_mixed_positive hh0,hs,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 2] with k hb hm hs hk
  refine ⟨hb,hm,?_⟩
  have hbb := initial_bulk_real _ c2_weight_pos c2_weight_lt_one k
    (hk ⟨0,by omega⟩).2.1 (hk ⟨0,by omega⟩).2.2 (hk ⟨1,by omega⟩).2.1 (hk ⟨1,by omega⟩).2.2
  have hbe := initial_mixed_real _ c2_weight_pos c2_weight_lt_one k
    (hk ⟨0,by omega⟩).2.1 (hk ⟨0,by omega⟩).2.2 (hk ⟨1,by omega⟩).2.1 (hk ⟨1,by omega⟩).2.2
  rw [initial_source_energy k (hk ⟨0,by omega⟩).2.1 (hk ⟨0,by omega⟩).2.2] at hs
  linarith

/-- Unconditional first-jet physical sign, using ONLY the pre-existing h0
certificate. No higher-order positivity is inferred. -/
theorem c2_canonical_eventually_compensates :
    ∀ᶠ k : ℕ in atTop,
      (physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
        (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)).re<0 ∧
      0<(physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
        (reconstructedResidual 0 (1/Real.sqrt 2) k initialInput)).re ∧
      -(physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
        (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)).re<
        2*(physicalForm (reconstructedBulk 0 (1/Real.sqrt 2) k initialInput)
          (reconstructedResidual 0 (1/Real.sqrt 2) k initialInput)).re :=
  c2_eventually_compensates canonicalCompletedNativeLogDerivativeMoment_zero_pos

end
end CarryFiniteGreen
