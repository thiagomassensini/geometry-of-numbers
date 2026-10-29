import NativeEncoder
import CarrySelfAdjointOperator.NativeCauchyLaguerreSources

namespace CarryPhysicalTrace
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- The actual radial factor is inserted exactly once. -/
theorem radial_finite_material (k N : ℕ) (a : Fin N → ℂ) :
    ((finiteMaterialState N (fun j => a j * (Real.sqrt ((k : ℝ)+1) : ℂ)) :
      PhysicalCauchySpace) : CanonicalCompletedNativeChiralCauchyCarrier) =
        ∑ j, a j • completedNativeRadialChiralCauchyState k j := by
  rw [finite_material_state_coe,physicalFiniteSynthesis_coe]
  simp only [ChiralReturn.radialIncidentSynthesis,completedNativeRadialChiralCauchyState]
  simp only [smul_smul]
  norm_num

theorem radial_combination_in_domain (k N : ℕ) (a : Fin N → ℂ) (x : PhysicalCauchySpace)
    (hx : (x : CanonicalCompletedNativeChiralCauchyCarrier) =
      ∑ j, a j • completedNativeRadialChiralCauchyState k j) : x ∈ EndpointDomain := by
  have he : (finiteMaterialState N (fun j => a j * (Real.sqrt ((k : ℝ)+1) : ℂ)) :
      PhysicalCauchySpace) = x := Subtype.ext ((radial_finite_material k N a).trans hx.symm)
  rw [← he]
  exact (finiteMaterialState N _).property

theorem original_incident_in_domain (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    physicalOriginalIncident k c r ∈ EndpointDomain := by
  exact radial_combination_in_domain k N (fun j => c j*(r : ℂ)^(j.val+1)) _ rfl

/-- The original completed chiral quotient remains in the coefficients. -/
theorem original_returned_in_domain (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    physicalOriginalReturned k c r ∈ EndpointDomain := by
  apply radial_combination_in_domain k N
    (fun j => (c j*(r : ℂ)^(j.val+1)) *
      completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j))
  simp only [physicalOriginalReturned,completedNativeRadialChiralMultiplierState,smul_smul]

theorem original_value_in_domain (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    physicalSourceValue k c r ∈ EndpointDomain := by
  apply radial_combination_in_domain k N _ _ rfl

theorem original_companion_in_domain (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    physicalSourceCompanion k c r ∈ EndpointDomain := by
  apply radial_combination_in_domain k N _ _ rfl

theorem original_native_companion_in_domain (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    physicalNativeCompanion k c r ∈ EndpointDomain := by
  apply radial_combination_in_domain k N _ _ rfl

theorem original_completion_companion_in_domain (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    physicalCompletionCompanion k c r ∈ EndpointDomain := by
  apply radial_combination_in_domain k N _ _ rfl

end
end CarryPhysicalTrace
