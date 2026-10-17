import CanonicalBlock

namespace CarryCorrectedGreenPorts
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CarryMaterialMixedSchurComparison
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- Concrete calibration and first ordered crosses of ONE physical family.
The center vanishes only in the residual channel, before central reassembly. -/
theorem physical_residual_first_calibration :
    ∃ v : Fin 7 → CanonicalCompletedNativeChiralCauchyCarrier,
      v 0 = 0 ∧
      inner ℂ (v 1) (v 1) = (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) ∧
      inner ℂ (v 1) (v 2) = 0 ∧
      inner ℂ (v 2) (v 4) =
        ((canonicalCompletedNativeLogDerivativeMoment 3-
          canonicalCompletedNativeLogDerivativeMoment 1*canonicalCompletedNativeLogDerivativeMoment 2/
            canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ) := by
  obtain ⟨v,_,hv⟩ := correctedGreen_seven_physical_realization 1 (by norm_num)
  have hp (a b : Fin 7) : inner ℂ (v a) (v b) =
      (carryMaterialResidualJet a.val b.val : ℂ) := by
    rw [hv a b, material_valve_confluent_jet 1 (by norm_num), ← residualJet_eq_real]
  refine ⟨v,?_,?_,?_,?_⟩
  · apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [hp]
    norm_num only [Fin.val_zero]
    have hz := material_residual_jet_even_even 0 0
    norm_num only [Nat.reduceMul, Nat.reduceAdd] at hz
    rw [hz]
    have hn := canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
    push_cast
    field_simp
    ring
  · rw [hp]
    exact_mod_cast (material_residual_jet_odd_odd 0 0)
  · rw [hp]
    have h := material_residual_jet_odd_even 0 1
    norm_num only [Nat.reduceMul, Nat.reduceAdd] at h
    simp only [Fin.val_one, Fin.val_two, h, Complex.ofReal_zero]
  · rw [hp]
    exact_mod_cast (material_residual_jet_even_even 1 2)

end
end CarryCorrectedGreenPorts
