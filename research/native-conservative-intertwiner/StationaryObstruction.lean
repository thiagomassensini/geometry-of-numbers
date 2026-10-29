import LowOrder

/-! This obstruction concerns a FIXED operator on the already rescaled
Cauchy carrier. A k-dependent transport or an enriched upstream colligation
is not excluded. Only the independently established first moment sign is used. -/
namespace CarryConservativeIntertwiner
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre ChiralReturn
open CarryCriticalRelative CarryForcingResidual NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The first true moment face keeps its original factor FOUR. -/
theorem first_even_boundary_energy : nativeSourceFiniteBoundaryEnergy 2 firstEvenBoundary=
    4*canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [first_even_is_pr41]
  have he := nativeResidualBoundary_energy 0 0
  simpa [carryPairingPivot,carryPairingRemainder,hankelPairing] using he

/-- A stationary transport on this radial chart would have to act as -I
on the first physical column. -/
theorem stationary_action_on_first_feature
    (C : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace)
    (hb : ∀ᶠ k : ℕ in atTop, physicalReturned 1 k firstEvenBoundary=C (physicalIncident 1 k firstEvenBoundary)) :
    C (physicalCauchyFeature 0)=-physicalCauchyFeature 0 := by
  have hi := physical_scaled_incident_tendsto 1 0 firstEvenBoundary (by norm_num) even_support
  have hr := physical_scaled_returned_tendsto 1 0 firstEvenBoundary (by norm_num) even_support
  rw [even_leading_exact] at hi hr
  have hc := C.continuous.continuousAt.tendsto.comp hi
  have he : (fun k => C (observationScale k 0 • physicalIncident 1 k firstEvenBoundary))=ᶠ[atTop]
      (fun k => observationScale k 0 • physicalReturned 1 k firstEvenBoundary) := by
    filter_upwards [hb] with k hk
    rw [map_smul,← hk]
  have hw : C evenLeading=-evenLeading := tendsto_nhds_unique (hc.congr' he) hr
  unfold evenLeading at hw
  rw [map_smul,← smul_neg] at hw
  have hh := congrArg (fun v : PhysicalCauchySpace => (amp 0)⁻¹ • v) hw
  simpa only [smul_smul,inv_mul_cancel₀ amp_zero_ne,one_smul] using hh

/-- No fixed bounded linear map, contractive or otherwise, realizes even
the first completed jet eventually in this rescaled Cauchy chart. -/
theorem no_stationary_completed_return
    (C : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace) :
    ¬ (∀ᶠ k : ℕ in atTop, physicalReturned 1 k firstEvenBoundary=C (physicalIncident 1 k firstEvenBoundary)) := by
  intro hb
  have hc := stationary_action_on_first_feature C hb
  have hinc (k : ℕ) : C (physicalIncident 1 k firstEvenBoundary)=-physicalIncident 1 k firstEvenBoundary := by
    rw [first_incident_ray,map_smul,hc,smul_neg]
  have hz : (fun k => 2*(‖physicalIncident 1 k firstEvenBoundary‖^2-
      ‖physicalReturned 1 k firstEvenBoundary‖^2))=ᶠ[atTop] (fun _ => (0:ℝ)) := by
    filter_upwards [hb] with k hk
    rw [hk,hinc,norm_neg,sub_self,mul_zero]
  have ht := physical_signed_energy_tendsto 1 firstEvenBoundary
  rw [first_even_boundary_energy] at ht
  have hzero : Tendsto (fun k => 2*(‖physicalIncident 1 k firstEvenBoundary‖^2-
      ‖physicalReturned 1 k firstEvenBoundary‖^2)) atTop (nhds (0:ℝ)) :=
    tendsto_const_nhds.congr' hz.symm
  have he := tendsto_nhds_unique ht hzero
  have hp := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  linarith

end
end CarryConservativeIntertwiner
