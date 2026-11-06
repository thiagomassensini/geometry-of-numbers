import SigmaSourceBezout
import Lean

open Lean Elab Command

elab "#audit_sigma_source_bezout " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for axiomName in (← collectAxioms decl) do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom in {decl}: {axiomName}"
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
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else
        throwError "Missing declaration: {name}"
  for required in #[
      `CarryMovingSigma.sigmaMatrix,
      `CarrySigmaSource.completedSigmaLogJet,
      `CarrySigmaSource.completedSigmaDensity,
      `CarrySigmaObstruction.displacedProductC] do
    unless seen.contains required do
      throwError "Missing original-source provenance dependency: {required}"
  logInfo m!"Sigma source/Bézout audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; original displaced product and sigma jets retained"

#audit_sigma_source_bezout
  CarrySigmaObstruction.completedSigmaDisplacedSourceTaylorSeries_sums_to_density
  CarrySigmaObstruction.displacedProductC_eq_completedSigmaDisplacedSource_eventually
  CarrySigmaObstruction.completedSigmaDisplacedSource_coefficient_recurrence
  CarrySigmaObstruction.completedSigmaDisplacedSource_recurrence
  CarrySigmaObstruction.completedSigmaDisplacedSourceSeries_mul_moments_eq_neg_derivative
  CarrySigmaObstruction.completedSigmaDisplacedSource_log_derivative_eq_moments
  CarrySigmaObstruction.completedSigmaDisplacedMoment_hankel_eq_two_sigmaMatrix
  CarrySigmaObstruction.completedSigmaDisplacedSource_bezout_congruence_sigmaMatrix
  CarrySigmaObstruction.completedSigmaDisplacedSource_bezout_posSemidef_iff_sigmaMatrix
  CarrySourceBezout.sourceKernel_head_tail

#print axioms CarrySigmaObstruction.completedSigmaDisplacedSourceTaylorSeries_sums_to_density
#print axioms CarrySigmaObstruction.displacedProductC_eq_completedSigmaDisplacedSource_eventually
#print axioms CarrySigmaObstruction.completedSigmaDisplacedSource_coefficient_recurrence
#print axioms CarrySigmaObstruction.completedSigmaDisplacedSource_recurrence
#print axioms CarrySigmaObstruction.completedSigmaDisplacedSourceSeries_mul_moments_eq_neg_derivative
#print axioms CarrySigmaObstruction.completedSigmaDisplacedSource_log_derivative_eq_moments
#print axioms CarrySigmaObstruction.completedSigmaDisplacedMoment_hankel_eq_two_sigmaMatrix
#print axioms CarrySigmaObstruction.completedSigmaDisplacedSource_bezout_congruence_sigmaMatrix
#print axioms CarrySigmaObstruction.completedSigmaDisplacedSource_bezout_posSemidef_iff_sigmaMatrix
#print axioms CarrySourceBezout.sourceKernel_head_tail
