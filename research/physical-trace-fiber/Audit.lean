import ReadoutTransport
import Lean

open Lean Elab Command
elab "#audit_physical_trace " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeSourceMixedDiscriminants_pos,
    `CarrySelfAdjointOperator.nativeSourceFourBoundaryEnergy_pos,
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef]
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
  logInfo m!"Physical trace audit roots: {ids.size}; type/body closure: {seen.size}; foundations and named sign guards passed"

#print axioms CarryTraceFiber.Physical
#print axioms CarryTraceFiber.Trace
#print axioms CarryTraceFiber.projection
#print axioms CarryTraceFiber.headTrace
#print axioms CarryTraceFiber.tailTrace
#print axioms CarryTraceFiber.contrast
#print axioms CarryTraceFiber.projection_eq_add
#print axioms CarryTraceFiber.head_reconstruction
#print axioms CarryTraceFiber.tail_reconstruction
#print axioms CarryTraceFiber.bulkPairing
#print axioms CarryTraceFiber.physical_inner_head_tail
#print axioms CarryTraceFiber.physical_inner_fiber
#print axioms CarryTraceFiber.physical_norm_fiber
#print axioms CarryTraceFiber.physical_eq_iff
#print axioms CarryTraceFiber.projection_zero_iff
#print axioms CarryTraceFiber.projection_defect_exact
#print axioms CarryTraceFiber.projection_defect_nonnegative
#print axioms CarryTraceFiber.balancedLift
#print axioms CarryTraceFiber.projection_balancedLift
#print axioms CarryTraceFiber.contrast_balancedLift
#print axioms CarryTraceFiber.bulkPairing_balancedLift
#print axioms CarryTraceFiber.balancedLift_inner
#print axioms CarryTraceFiber.invisible
#print axioms CarryTraceFiber.projection_invisible
#print axioms CarryTraceFiber.invisible_orthogonal
#print axioms CarryTraceFiber.physical_reconstruct
#print axioms CarryTraceFiber.physical_inner_visible_invisible
#print axioms CarryTraceFiber.invisible_norm_exact
#print axioms CarryTraceFiber.balancedLift_minimum
#print axioms CarryTraceFiber.physical_norm_visible_invisible
#print axioms CarryTraceFiber.trace_energy_preserved_iff
#print axioms CarryTraceFiber.finite_synthesis_pairing
#print axioms CarryTraceFiber.finite_synthesis_energy_defect
#print axioms CarryTraceFiber.nativeState
#print axioms CarryTraceFiber.native_tail_zero
#print axioms CarryTraceFiber.native_contrast_eq_trace
#print axioms CarryTraceFiber.native_pairing_exact
#print axioms CarryTraceFiber.native_invisible_energy_exact
#print axioms CarryTraceFiber.native_center_trace_ne_zero
#print axioms CarryTraceFiber.native_center_invisible_energy_positive
#print axioms CarryTraceFiber.native_center_invisible_ne_zero
#print axioms CarryTraceFiber.native_center_not_minimum_energy_lift
#print axioms CarryTraceFiber.native_invisible_tendsto
#print axioms CarryTraceFiber.not_physical_norm_factors_through_trace
#print axioms CarryTraceFiber.native_invisible_pairing_tendsto
#print axioms CarryTraceFiber.native_center_trace_energy_strict
#print axioms CarryTraceFiber.native_center_invisible_energy_eventually
#print axioms CarryTraceFiber.completed_readout_trace
#print axioms CarryTraceFiber.completed_readout_invisible_left
#print axioms CarryTraceFiber.completed_readout_invisible_right
#print axioms CarryTraceFiber.completed_readout_balanced
#print axioms CarryTraceFiber.native_center_invisible_boundary_radical
#print axioms CarryTraceFiber.normalized_functional_state_from_physical
#print axioms CarryTraceFiber.physical_functional_native_kernel
#print axioms CarryTraceFiber.native_kernel_from_physical_functional
#print axioms CarryTraceFiber.native_kernel_center_diagonal

#audit_physical_trace
  CarryTraceFiber.Physical
  CarryTraceFiber.Trace
  CarryTraceFiber.projection
  CarryTraceFiber.headTrace
  CarryTraceFiber.tailTrace
  CarryTraceFiber.contrast
  CarryTraceFiber.projection_eq_add
  CarryTraceFiber.head_reconstruction
  CarryTraceFiber.tail_reconstruction
  CarryTraceFiber.bulkPairing
  CarryTraceFiber.physical_inner_head_tail
  CarryTraceFiber.physical_inner_fiber
  CarryTraceFiber.physical_norm_fiber
  CarryTraceFiber.physical_eq_iff
  CarryTraceFiber.projection_zero_iff
  CarryTraceFiber.projection_defect_exact
  CarryTraceFiber.projection_defect_nonnegative
  CarryTraceFiber.balancedLift
  CarryTraceFiber.projection_balancedLift
  CarryTraceFiber.contrast_balancedLift
  CarryTraceFiber.bulkPairing_balancedLift
  CarryTraceFiber.balancedLift_inner
  CarryTraceFiber.invisible
  CarryTraceFiber.projection_invisible
  CarryTraceFiber.invisible_orthogonal
  CarryTraceFiber.physical_reconstruct
  CarryTraceFiber.physical_inner_visible_invisible
  CarryTraceFiber.invisible_norm_exact
  CarryTraceFiber.balancedLift_minimum
  CarryTraceFiber.physical_norm_visible_invisible
  CarryTraceFiber.trace_energy_preserved_iff
  CarryTraceFiber.finite_synthesis_pairing
  CarryTraceFiber.finite_synthesis_energy_defect
  CarryTraceFiber.nativeState
  CarryTraceFiber.native_tail_zero
  CarryTraceFiber.native_contrast_eq_trace
  CarryTraceFiber.native_pairing_exact
  CarryTraceFiber.native_invisible_energy_exact
  CarryTraceFiber.native_center_trace_ne_zero
  CarryTraceFiber.native_center_invisible_energy_positive
  CarryTraceFiber.native_center_invisible_ne_zero
  CarryTraceFiber.native_center_not_minimum_energy_lift
  CarryTraceFiber.native_invisible_tendsto
  CarryTraceFiber.not_physical_norm_factors_through_trace
  CarryTraceFiber.native_invisible_pairing_tendsto
  CarryTraceFiber.native_center_trace_energy_strict
  CarryTraceFiber.native_center_invisible_energy_eventually
  CarryTraceFiber.completed_readout_trace
  CarryTraceFiber.completed_readout_invisible_left
  CarryTraceFiber.completed_readout_invisible_right
  CarryTraceFiber.completed_readout_balanced
  CarryTraceFiber.native_center_invisible_boundary_radical
  CarryTraceFiber.normalized_functional_state_from_physical
  CarryTraceFiber.physical_functional_native_kernel
  CarryTraceFiber.native_kernel_from_physical_functional
  CarryTraceFiber.native_kernel_center_diagonal
