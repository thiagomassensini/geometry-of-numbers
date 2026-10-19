import MaterialCameraSeparation
import CameraObservation
import Lean

open Lean Elab Command
elab "#audit_quotient_roots " ids:ident+ : command => do
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
  logInfo m!"Quotient roots: {ids.size}; type/body closure: {seen.size}; foundational guard passed"

#print axioms CarryMaterialCameraSeparation.materialReadout
#print axioms CarryMaterialCameraSeparation.divisibilityReadout
#print axioms CarryMaterialCameraSeparation.totalReadout
#print axioms CarryMaterialCameraSeparation.odd_camera_total
#print axioms CarryMaterialCameraSeparation.even_camera_divisibility
#print axioms CarryMaterialCameraSeparation.divisibility_above_support
#print axioms CarryMaterialCameraSeparation.divisor_readouts_zero
#print axioms CarryMaterialCameraSeparation.divisibility_separates
#print axioms CarryMaterialCameraSeparation.finite_camera_separation
#print axioms CarryMaterialCameraSeparation.finiteMaterialObservation
#print axioms CarryMaterialCameraSeparation.bounded_readout_eq
#print axioms CarryMaterialCameraSeparation.all_cameras_finite_separate
#print axioms CarryMaterialCameraSeparation.finiteMaterialObservation_sub
#print axioms CarryMaterialCameraSeparation.all_cameras_finite_injective
#print axioms CarryCameraObservationAudit.cameraTwo
#print axioms CarryCameraObservationAudit.cameraFour
#print axioms CarryCameraObservationAudit.camera_two_four_gram
#print axioms CarryCameraObservationAudit.camera_two_four_distance
#print axioms CarryCameraObservationAudit.completed_camera_two_four_equal
#print axioms CarryCameraObservationAudit.no_camera_energy_descent

#audit_quotient_roots
  CarryMaterialCameraSeparation.materialReadout
  CarryMaterialCameraSeparation.divisibilityReadout
  CarryMaterialCameraSeparation.totalReadout
  CarryMaterialCameraSeparation.odd_camera_total
  CarryMaterialCameraSeparation.even_camera_divisibility
  CarryMaterialCameraSeparation.divisibility_above_support
  CarryMaterialCameraSeparation.divisor_readouts_zero
  CarryMaterialCameraSeparation.divisibility_separates
  CarryMaterialCameraSeparation.finite_camera_separation
  CarryMaterialCameraSeparation.finiteMaterialObservation
  CarryMaterialCameraSeparation.bounded_readout_eq
  CarryMaterialCameraSeparation.all_cameras_finite_separate
  CarryMaterialCameraSeparation.finiteMaterialObservation_sub
  CarryMaterialCameraSeparation.all_cameras_finite_injective
  CarryCameraObservationAudit.cameraTwo
  CarryCameraObservationAudit.cameraFour
  CarryCameraObservationAudit.camera_two_four_gram
  CarryCameraObservationAudit.camera_two_four_distance
  CarryCameraObservationAudit.completed_camera_two_four_equal
  CarryCameraObservationAudit.no_camera_energy_descent
