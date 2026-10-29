import GreenSynthesis
import CameraBudget
import ScaleCompatibility
import CameraObservation
import GeometryOfNumbers.Analysis.CarryMaterialReadoutQuotient
import Lean
open Lean Elab Command
elab "#audit_global_synthesis " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for name in (← collectAxioms decl) do
      unless allowed.contains name do
        throwError "Unexpected axiom in {decl}: {name}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless allowed.contains name do
            throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? then
          todo := value.getUsedConstants.toList ++ todo
  logInfo m!"Global synthesis roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

#print axioms CarryGlobalGreenSynthesis.originalParseval
#print axioms CarryGlobalGreenSynthesis.sourceSynthesis
#print axioms CarryGlobalGreenSynthesis.frameNull
#print axioms CarryGlobalGreenSynthesis.branchState
#print axioms CarryGlobalGreenSynthesis.physicalEscape
#print axioms CarryGlobalGreenSynthesis.synthesis_parseval
#print axioms CarryGlobalGreenSynthesis.synthesis_frame_null
#print axioms CarryGlobalGreenSynthesis.frame_null_parseval
#print axioms CarryGlobalGreenSynthesis.coefficient_kernel_exact
#print axioms CarryGlobalGreenSynthesis.same_physical_state_iff
#print axioms CarryGlobalGreenSynthesis.frame_polarized_split
#print axioms CarryGlobalGreenSynthesis.complete_polarized_split
#print axioms CarryGlobalGreenSynthesis.complete_energy_split
#print axioms CarryGlobalGreenSynthesis.physical_quotient_energy
#print axioms CarryGlobalGreenSynthesis.branch_choice_preserves_total
#print axioms CarryGlobalGreenSynthesis.quotient_energy_minimum
#print axioms CarryGlobalGreenSynthesis.reconstructed_domain_iff
#print axioms CarryGlobalGreenSynthesis.reconstructed_clock_intertwines
#print axioms CarryGlobalGreenSynthesis.synthesis_real_complex_compatible
#print axioms CarryGlobalGreenSynthesis.raw_canonical_same_coefficient_kernel
#print axioms CarryGlobalGreenSynthesis.synthesis_homogeneous_energy
#print axioms CarryGlobalGreenSynthesis.c2_seed_compression_zero
#print axioms CarryGlobalGreenSynthesis.physical_seed_not_redundant
#print axioms CarryGlobalCameraBudget.finiteTotal
#print axioms CarryGlobalCameraBudget.large_camera_total
#print axioms CarryGlobalCameraBudget.centered_observations_finite
#print axioms CarryGlobalCameraBudget.camera_energy_summable_iff
#print axioms CarryGlobalCameraBudget.seed_camera_observation
#print axioms CarryGlobalCameraBudget.seed_camera_energy_prefix
#print axioms CarryGlobalCameraBudget.seed_camera_energy_not_summable
#print axioms CarryGlobalCameraBudget.total_and_centered_injective
#print axioms CarryGlobalCameraBudget.camera_polarized_total_split
#print axioms CarryGlobalCameraBudget.nativeTotalPrefix
#print axioms CarryGlobalCameraBudget.native_total_square_lower
#print axioms CarryGlobalCameraBudget.native_total_unbounded
#print axioms CarryGlobalScaleCompatibility.native_log_amplitude_invariant
#print axioms CarryGlobalScaleCompatibility.no_universal_unnormalized_linear_gram
#print axioms CarryGlobalScaleCompatibility.jacobi_blindness_not_source_equality
#print axioms CarryCameraObservationAudit.camera_two_four_distance
#print axioms GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_boundary_defect
#print axioms CarryMaterialCameraSeparation.all_cameras_finite_injective

#audit_global_synthesis
  CarryGlobalGreenSynthesis.originalParseval
  CarryGlobalGreenSynthesis.sourceSynthesis
  CarryGlobalGreenSynthesis.frameNull
  CarryGlobalGreenSynthesis.branchState
  CarryGlobalGreenSynthesis.physicalEscape
  CarryGlobalGreenSynthesis.synthesis_parseval
  CarryGlobalGreenSynthesis.synthesis_frame_null
  CarryGlobalGreenSynthesis.frame_null_parseval
  CarryGlobalGreenSynthesis.coefficient_kernel_exact
  CarryGlobalGreenSynthesis.same_physical_state_iff
  CarryGlobalGreenSynthesis.frame_polarized_split
  CarryGlobalGreenSynthesis.complete_polarized_split
  CarryGlobalGreenSynthesis.complete_energy_split
  CarryGlobalGreenSynthesis.physical_quotient_energy
  CarryGlobalGreenSynthesis.branch_choice_preserves_total
  CarryGlobalGreenSynthesis.quotient_energy_minimum
  CarryGlobalGreenSynthesis.reconstructed_domain_iff
  CarryGlobalGreenSynthesis.reconstructed_clock_intertwines
  CarryGlobalGreenSynthesis.synthesis_real_complex_compatible
  CarryGlobalGreenSynthesis.raw_canonical_same_coefficient_kernel
  CarryGlobalGreenSynthesis.synthesis_homogeneous_energy
  CarryGlobalGreenSynthesis.c2_seed_compression_zero
  CarryGlobalGreenSynthesis.physical_seed_not_redundant
  CarryGlobalCameraBudget.finiteTotal
  CarryGlobalCameraBudget.large_camera_total
  CarryGlobalCameraBudget.centered_observations_finite
  CarryGlobalCameraBudget.camera_energy_summable_iff
  CarryGlobalCameraBudget.seed_camera_observation
  CarryGlobalCameraBudget.seed_camera_energy_prefix
  CarryGlobalCameraBudget.seed_camera_energy_not_summable
  CarryGlobalCameraBudget.total_and_centered_injective
  CarryGlobalCameraBudget.camera_polarized_total_split
  CarryGlobalCameraBudget.nativeTotalPrefix
  CarryGlobalCameraBudget.native_total_square_lower
  CarryGlobalCameraBudget.native_total_unbounded
  CarryGlobalScaleCompatibility.native_log_amplitude_invariant
  CarryGlobalScaleCompatibility.no_universal_unnormalized_linear_gram
  CarryGlobalScaleCompatibility.jacobi_blindness_not_source_equality
  CarryCameraObservationAudit.camera_two_four_distance
  GeometryOfNumbers.Analysis.carryMaterialReadoutProjection_boundary_defect
  CarryMaterialCameraSeparation.all_cameras_finite_injective
