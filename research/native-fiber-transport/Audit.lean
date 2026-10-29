import NativeCauchyOverlap
import Lean

open Lean Elab Command
elab "#audit_native_fiber_transport " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeSourceMixedDiscriminants_pos,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.not_canonicalCompletedC3CausalChiralDefectGramNonnegativeAt_of_im_pos,
    `CarrySelfAdjointOperator.not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_im_pos]
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
      if forbidden.contains name then
        throwError "Unexpected finite sign dependency: {name}"
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
  logInfo m!"Native fiber transport audit roots: {ids.size}; type/body closure: {seen.size}; foundations and named sign guards passed"

#print axioms CarryFiberTransport.Source
#print axioms CarryFiberTransport.fullReadout
#print axioms CarryFiberTransport.plusReadout
#print axioms CarryFiberTransport.minusReadout
#print axioms CarryFiberTransport.ambientReadout
#print axioms CarryFiberTransport.cameraReadout
#print axioms CarryFiberTransport.enlargedReadout
#print axioms CarryFiberTransport.tracePart
#print axioms CarryFiberTransport.fiberPart
#print axioms CarryFiberTransport.source_reconstruction
#print axioms CarryFiberTransport.tracePart_orthogonal_fiberPart
#print axioms CarryFiberTransport.source_pairing_split
#print axioms CarryFiberTransport.fiber_direct
#print axioms CarryFiberTransport.tracePart_coherent
#print axioms CarryFiberTransport.fiberPart_coherent
#print axioms CarryFiberTransport.trace_fiber_zero
#print axioms CarryFiberTransport.arch_fiber_zero
#print axioms CarryFiberTransport.ambient_trace_zero
#print axioms CarryFiberTransport.ambient_fiber
#print axioms CarryFiberTransport.camera_trace_zero
#print axioms CarryFiberTransport.camera_fiber
#print axioms CarryFiberTransport.full_fiber_zero
#print axioms CarryFiberTransport.full_trace
#print axioms CarryFiberTransport.plus_fiber_zero
#print axioms CarryFiberTransport.minus_fiber_zero
#print axioms CarryFiberTransport.plus_trace
#print axioms CarryFiberTransport.minus_trace
#print axioms CarryFiberTransport.enlarged_trace
#print axioms CarryFiberTransport.enlarged_fiber
#print axioms CarryFiberTransport.camera_chiral_trace
#print axioms CarryFiberTransport.camera_chiral_fiber
#print axioms CarryFiberTransport.enlarged_trace_fiber_cross
#print axioms CarryFiberTransport.enlarged_fiber_trace_cross
#print axioms CarryFiberTransport.enlarged_pairing_split
#print axioms CarryFiberTransport.defectPair
#print axioms CarryFiberTransport.defectEnergy
#print axioms CarryFiberTransport.defectPair_split
#print axioms CarryFiberTransport.fiber_defect_exact
#print axioms CarryFiberTransport.trace_defect_exact
#print axioms CarryFiberTransport.enlarged_norm_split
#print axioms CarryFiberTransport.defectEnergy_split
#print axioms CarryFiberTransport.defectEnergy_budget
#print axioms CarryFiberTransport.defect_of_full_zero
#print axioms CarryFiberTransport.nativeSources
#print axioms CarryFiberTransport.nativeSynthesis
#print axioms CarryFiberTransport.nativeSources_causal
#print axioms CarryFiberTransport.nativeSynthesis_causal
#print axioms CarryFiberTransport.nativeSources_ambient_independent
#print axioms CarryFiberTransport.ambient_nativeSynthesis_ne_zero
#print axioms CarryFiberTransport.full_trace_native_kernel_witness
#print axioms CarryFiberTransport.causal_full_trace_negative_witness
#print axioms CarryFiberTransport.nativeSynthesis_ambient_port
#print axioms CarryFiberTransport.nativeSynthesis_ambient_norm_camera
#print axioms CarryFiberTransport.nativeSource
#print axioms CarryFiberTransport.signaturePair
#print axioms CarryFiberTransport.signature_trace
#print axioms CarryFiberTransport.full_functional_signature
#print axioms CarryFiberTransport.native_full_readout
#print axioms CarryFiberTransport.native_wronskian_trace_signature
#print axioms CarryFiberTransport.native_kernel_trace_signature
#print axioms CarryFiberTransport.native_four_channel_fiber_identity
#print axioms CarryFiberTransport.separationCorrection
#print axioms CarryFiberTransport.defectPair_signature
#print axioms CarryFiberTransport.native_four_channel_separation_correction
#print axioms CarryFiberTransport.separationCorrection_diagonal
#print axioms CarryFiberTransport.separationCorrection_radial
#print axioms CarryFiberTransport.separationCorrection_radial_ne_zero
#print axioms CarryFiberTransport.admissible_separation_correction_nonzero
#print axioms CarryFiberTransport.radialPoint
#print axioms CarryFiberTransport.radialField
#print axioms CarryFiberTransport.radialOverlap
#print axioms CarryFiberTransport.radialOverlap_inner
#print axioms CarryFiberTransport.radial_cauchy_separation_correction
#print axioms CarryFiberTransport.radialOverlap_diagonal
#print axioms CarryFiberTransport.radial_observed_norm_sq
#print axioms CarryFiberTransport.radial_four_channel_overlap_identity
#print axioms CarryFiberTransport.finite_radial_overlap_transport

#audit_native_fiber_transport
  CarryFiberTransport.Source
  CarryFiberTransport.fullReadout
  CarryFiberTransport.plusReadout
  CarryFiberTransport.minusReadout
  CarryFiberTransport.ambientReadout
  CarryFiberTransport.cameraReadout
  CarryFiberTransport.enlargedReadout
  CarryFiberTransport.tracePart
  CarryFiberTransport.fiberPart
  CarryFiberTransport.source_reconstruction
  CarryFiberTransport.tracePart_orthogonal_fiberPart
  CarryFiberTransport.source_pairing_split
  CarryFiberTransport.fiber_direct
  CarryFiberTransport.tracePart_coherent
  CarryFiberTransport.fiberPart_coherent
  CarryFiberTransport.trace_fiber_zero
  CarryFiberTransport.arch_fiber_zero
  CarryFiberTransport.ambient_trace_zero
  CarryFiberTransport.ambient_fiber
  CarryFiberTransport.camera_trace_zero
  CarryFiberTransport.camera_fiber
  CarryFiberTransport.full_fiber_zero
  CarryFiberTransport.full_trace
  CarryFiberTransport.plus_fiber_zero
  CarryFiberTransport.minus_fiber_zero
  CarryFiberTransport.plus_trace
  CarryFiberTransport.minus_trace
  CarryFiberTransport.enlarged_trace
  CarryFiberTransport.enlarged_fiber
  CarryFiberTransport.camera_chiral_trace
  CarryFiberTransport.camera_chiral_fiber
  CarryFiberTransport.enlarged_trace_fiber_cross
  CarryFiberTransport.enlarged_fiber_trace_cross
  CarryFiberTransport.enlarged_pairing_split
  CarryFiberTransport.defectPair
  CarryFiberTransport.defectEnergy
  CarryFiberTransport.defectPair_split
  CarryFiberTransport.fiber_defect_exact
  CarryFiberTransport.trace_defect_exact
  CarryFiberTransport.enlarged_norm_split
  CarryFiberTransport.defectEnergy_split
  CarryFiberTransport.defectEnergy_budget
  CarryFiberTransport.defect_of_full_zero
  CarryFiberTransport.nativeSources
  CarryFiberTransport.nativeSynthesis
  CarryFiberTransport.nativeSources_causal
  CarryFiberTransport.nativeSynthesis_causal
  CarryFiberTransport.nativeSources_ambient_independent
  CarryFiberTransport.ambient_nativeSynthesis_ne_zero
  CarryFiberTransport.full_trace_native_kernel_witness
  CarryFiberTransport.causal_full_trace_negative_witness
  CarryFiberTransport.nativeSynthesis_ambient_port
  CarryFiberTransport.nativeSynthesis_ambient_norm_camera
  CarryFiberTransport.nativeSource
  CarryFiberTransport.signaturePair
  CarryFiberTransport.signature_trace
  CarryFiberTransport.full_functional_signature
  CarryFiberTransport.native_full_readout
  CarryFiberTransport.native_wronskian_trace_signature
  CarryFiberTransport.native_kernel_trace_signature
  CarryFiberTransport.native_four_channel_fiber_identity
  CarryFiberTransport.separationCorrection
  CarryFiberTransport.defectPair_signature
  CarryFiberTransport.native_four_channel_separation_correction
  CarryFiberTransport.separationCorrection_diagonal
  CarryFiberTransport.separationCorrection_radial
  CarryFiberTransport.separationCorrection_radial_ne_zero
  CarryFiberTransport.admissible_separation_correction_nonzero
  CarryFiberTransport.radialPoint
  CarryFiberTransport.radialField
  CarryFiberTransport.radialOverlap
  CarryFiberTransport.radialOverlap_inner
  CarryFiberTransport.radial_cauchy_separation_correction
  CarryFiberTransport.radialOverlap_diagonal
  CarryFiberTransport.radial_observed_norm_sq
  CarryFiberTransport.radial_four_channel_overlap_identity
  CarryFiberTransport.finite_radial_overlap_transport
