import FullTransverseCancellation

/-!
# Ligação transversal com o readout TFVD/Wronskiano original

O readout normalizado da síntese TFVD é identificado com a resposta
logarítmica completada apenas no germe onde a característica é não nula.
Não se presume positividade do kernel nem equivalência de estados.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem fullTransverse_eq_normalizedGreen (t : ℝ)
    (hF : completedNativeOperatorCharacteristic (t:ℂ) ≠ 0) :
    fullTransverseResponse t = 2 * Complex.I * completedNativeOperatorCharacteristic (t:ℂ) *
      completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion (t:ℂ) := by
  rw [fullTransverseResponse_eq]
  have hr := iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal 1 t
  simp only [iteratedDeriv_one] at hr
  rw [hr]
  unfold completedGreenNormalizedResponse completedNativeOperatorBoundaryCompanion
  field_simp

theorem fullTransverse_eq_tfvdWronskian_near (M : ℕ) :
    ∀ᶠ t : ℝ in 𝓝 0,
      fullTransverseResponse t = 2 * Complex.I * completedNativeOperatorCharacteristic (t:ℂ) *
        canonicalC3BracketTfvdNormalizedResponse M (t:ℂ) := by
  have hcast : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto (x:= (0:ℝ)))
  have hEq := hcast.eventually (canonicalC3BracketTfvdNormalizedResponse_eventuallyEq_completed M)
  have hne : ∀ᶠ z : ℂ in 𝓝 0, completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hEq, hcast.eventually hne] with t ht hn
  rw [ht]
  exact fullTransverse_eq_normalizedGreen t hn

#print axioms fullTransverse_eq_normalizedGreen
#print axioms fullTransverse_eq_tfvdWronskian_near
end
end CarryTiltSlice
