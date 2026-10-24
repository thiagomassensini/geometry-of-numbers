import OriginalSourceDomain

/-! Domain-correct traces of the EXISTING completed physical channels.
No channel is synthesized from a moment or from its desired readout. -/
namespace CarryCompletedTrace
open CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false

def valueCore (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : EndpointDomain :=
  ⟨physicalSourceValue k c r,original_value_in_domain k c r⟩
def companionCore (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : EndpointDomain :=
  ⟨physicalSourceCompanion k c r,original_companion_in_domain k c r⟩
def nativeCore (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : EndpointDomain :=
  ⟨physicalNativeCompanion k c r,original_native_companion_in_domain k c r⟩
def completionCore (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : EndpointDomain :=
  ⟨physicalCompletionCompanion k c r,original_completion_companion_in_domain k c r⟩
def incidentCore (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : EndpointDomain :=
  ⟨physicalOriginalIncident k c r,original_incident_in_domain k c r⟩
def returnedCore (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : EndpointDomain :=
  ⟨physicalOriginalReturned k c r,original_returned_in_domain k c r⟩

def sourceWeight (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) (j : Fin N) : ℂ :=
  c j*(r : ℂ)^(j.val+1) /
    completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)

theorem radial_core_trace (k N a : ℕ) (b : Fin N → ℂ) (x : EndpointDomain)
    (hx : ((x : PhysicalCauchySpace) : CanonicalCompletedNativeChiralCauchyCarrier) =
      ∑ j, b j • completedNativeRadialChiralCauchyState k j) :
    endpointTrace a x = (Real.sqrt ((k : ℝ)+1) : ℂ) *
      ∑ j, (j.val.descFactorial a : ℂ)*b j := by
  have he : x = finiteMaterialState N
      (fun j => b j*(Real.sqrt ((k : ℝ)+1) : ℂ)) := by
    apply Subtype.ext
    apply Subtype.ext
    exact hx.trans (radial_finite_material k N b).symm
  rw [he,endpoint_trace_finite_material,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem value_core_trace (k a : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    endpointTrace a (valueCore k c r) = (Real.sqrt ((k : ℝ)+1) : ℂ) *
      ∑ j, (j.val.descFactorial a : ℂ) * sourceWeight k c r j *
        completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) := by
  rw [radial_core_trace k N a _ _ rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceWeight,div_eq_mul_inv]
  ring

theorem companion_core_trace (k a : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    endpointTrace a (companionCore k c r) = (Real.sqrt ((k : ℝ)+1) : ℂ) *
      ∑ j, (j.val.descFactorial a : ℂ) * sourceWeight k c r j *
        (-deriv completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)) := by
  rw [radial_core_trace k N a _ _ rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceWeight,div_eq_mul_inv]
  ring

theorem native_core_trace (k a : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    endpointTrace a (nativeCore k c r) = (Real.sqrt ((k : ℝ)+1) : ℂ) *
      ∑ j, (j.val.descFactorial a : ℂ) * sourceWeight k c r j *
        (nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k j) *
          nativeHeightScalarBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k j)) := by
  rw [radial_core_trace k N a _ _ rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceWeight,div_eq_mul_inv]
  ring

theorem completion_core_trace (k a : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    endpointTrace a (completionCore k c r) = (Real.sqrt ((k : ℝ)+1) : ℂ) *
      ∑ j, (j.val.descFactorial a : ℂ) * sourceWeight k c r j *
        (nativeXiCompletionBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k j) *
          nativeHeightScalar (canonicalCompletedC3RadialTiltPoint k j)) := by
  rw [radial_core_trace k N a _ _ rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceWeight,div_eq_mul_inv]
  ring

theorem incident_core_trace (k a : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    endpointTrace a (incidentCore k c r) = (Real.sqrt ((k : ℝ)+1) : ℂ) *
      ∑ j, (j.val.descFactorial a : ℂ)* (c j*(r : ℂ)^(j.val+1)) := by
  exact radial_core_trace k N a _ _ rfl

theorem returned_core_trace (k a : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    endpointTrace a (returnedCore k c r) = (Real.sqrt ((k : ℝ)+1) : ℂ) *
      ∑ j, (j.val.descFactorial a : ℂ)* (c j*(r : ℂ)^(j.val+1))*
        completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j) := by
  have hx : (((returnedCore k c r : EndpointDomain) : PhysicalCauchySpace) :
      CanonicalCompletedNativeChiralCauchyCarrier) =
      ∑ j, ((c j*(r : ℂ)^(j.val+1))*
        completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)) •
          completedNativeRadialChiralCauchyState k j := by
    change (∑ j, (c j*(r : ℂ)^(j.val+1)) •
      completedNativeRadialChiralMultiplierState k j) = _
    simp only [completedNativeRadialChiralMultiplierState,smul_smul]
  have h := radial_core_trace k N a
    (fun j => (c j*(r : ℂ)^(j.val+1))*
      completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)) _ hx
  simpa only [mul_assoc] using h

theorem companion_core_split (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hs : ∀ j : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k j) ∈ CPFormal.Analytic.Cp.genuineCriticalStrip) :
    companionCore k c r = nativeCore k c r + completionCore k c r := by
  apply Subtype.ext
  apply Subtype.ext
  exact ChiralReturn.sourceCompanion_eq_native_add_completion k c r hs

theorem companion_trace_split (k a : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hs : ∀ j : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k j) ∈ CPFormal.Analytic.Cp.genuineCriticalStrip) :
    endpointTrace a (companionCore k c r) =
      endpointTrace a (nativeCore k c r) + endpointTrace a (completionCore k c r) := by
  rw [companion_core_split k c r hs,map_add]

end
end CarryCompletedTrace
