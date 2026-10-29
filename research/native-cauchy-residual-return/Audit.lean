import CrossControls
import ProjectionLoss
import JetResidual
import Lean

open Lean Elab Command
elab "#audit_cauchy_residual " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let alwaysForbidden := #[
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.trial_seven_posDef,
    `CarrySeventhEven.trial_seven_pivots_pos,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let forbidden := alwaysForbidden ++ #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthEven.even_six_pivots_pos,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier]
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
        throwError "Unexpected later positivity dependency: {name}"
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
  logInfo m!"Cauchy residual audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryCauchyResidual.feature
#print axioms CarryCauchyResidual.cauchy
#print axioms CarryCauchyResidual.feature_inner
#print axioms CarryCauchyResidual.feature_projection
#print axioms CarryCauchyResidual.perpendicularFeature
#print axioms CarryCauchyResidual.perpendicularFeature_eq_complement
#print axioms CarryCauchyResidual.perpendicularFeature_inner
#print axioms CarryCauchyResidual.isometricFeature
#print axioms CarryCauchyResidual.isometricFeature_inner
#print axioms CarryCauchyResidual.tailSynthesis
#print axioms CarryCauchyResidual.isometricSynthesis
#print axioms CarryCauchyResidual.synthesis_isometry
#print axioms CarryCauchyResidual.synthesis_norm
#print axioms CarryCauchyResidual.tailSynthesis_eq_original
#print axioms CarryCauchyResidual.tailSynthesis_injective
#print axioms CarryCauchyResidual.finitePhysicalIsometry
#print axioms CarryCauchyResidual.finitePhysicalIsometry_exact
#print axioms CarryCauchyResidual.sourceReturn
#print axioms CarryCauchyResidual.feedbackDenominator
#print axioms CarryCauchyResidual.incidentCoefficient
#print axioms CarryCauchyResidual.returnedCoefficient
#print axioms CarryCauchyResidual.nativeIn_basis
#print axioms CarryCauchyResidual.nativeOut_basis
#print axioms CarryCauchyResidual.remainingIncident_basis
#print axioms CarryCauchyResidual.remainingIncident_basis_isometric
#print axioms CarryCauchyResidual.residual_basis_kernel
#print axioms CarryCauchyResidual.tailInput
#print axioms CarryCauchyResidual.tailCoefficients
#print axioms CarryCauchyResidual.eraseHead_eq_tail
#print axioms CarryCauchyResidual.linearMap_tail
#print axioms CarryCauchyResidual.incidentCoordinates
#print axioms CarryCauchyResidual.returnedCoordinates
#print axioms CarryCauchyResidual.incidentCoordinates_injective
#print axioms CarryCauchyResidual.remainingIncident_tail
#print axioms CarryCauchyResidual.nativeOut_tail
#print axioms CarryCauchyResidual.residual_same_cauchy
#print axioms CarryCauchyResidual.residual_full_source
#print axioms CarryCauchyResidual.reducedReturn
#print axioms CarryCauchyResidual.reducedReturn_formula
#print axioms CarryCauchyResidual.reduced_coordinates_exact
#print axioms CarryCauchyResidual.residual_return_comparison
#print axioms CarryCauchyResidual.controlMultiplier
#print axioms CarryCauchyResidual.controlCoefficients
#print axioms CarryCauchyResidual.controlPair
#print axioms CarryCauchyResidual.control_diagonal_contracts
#print axioms CarryCauchyResidual.control_first_diagonal
#print axioms CarryCauchyResidual.control_second_diagonal
#print axioms CarryCauchyResidual.control_cross
#print axioms CarryCauchyResidual.control_full_negative
#print axioms CarryCauchyResidual.radialScale
#print axioms CarryCauchyResidual.radialScale_ne_zero
#print axioms CarryCauchyResidual.curvature_eq_four_moment
#print axioms CarryCauchyResidual.sourceReturn_tendsto
#print axioms CarryCauchyResidual.source_tangent
#print axioms CarryCauchyResidual.returnedCoefficient_tangent
#print axioms CarryCauchyResidual.feedbackDenominator_tangent
#print axioms CarryCauchyResidual.incidentCoefficient_tangent
#print axioms CarryCauchyResidual.central_deficit_tangent
#print axioms CarryCauchyResidual.incidentCoefficient_eventually_ne_zero
#print axioms CarryCauchyResidual.reduced_coordinates_eventually_valid
#print axioms CarryCauchyResidual.reducedReturn_tendsto_one
#print axioms CarryCauchyResidual.returnedHead
#print axioms CarryCauchyResidual.projectedBothPair
#print axioms CarryCauchyResidual.projection_loss_polarized
#print axioms CarryCauchyResidual.projection_loss_energy
#print axioms CarryCauchyResidual.returnedHead_basis
#print axioms CarryCauchyResidual.nativeAnchor_norm_sq
#print axioms CarryCauchyResidual.returnedHead_energy
#print axioms CarryCauchyResidual.projection_loss_schur_tendsto
#print axioms CarryCauchyResidual.projection_loss_strict_eventually
#print axioms CarryCauchyResidual.second_source_projection_loss
#print axioms CarryCauchyResidual.jetTailCoefficients
#print axioms CarryCauchyResidual.reducedJetIncident
#print axioms CarryCauchyResidual.reducedJetReturned
#print axioms CarryCauchyResidual.reducedJetPair
#print axioms CarryCauchyResidual.reducedJetPair_exact
#print axioms CarryCauchyResidual.reducedJetPair_canonical_schur_limit

#audit_cauchy_residual cauchy
  CarryCauchyResidual.feature
  CarryCauchyResidual.cauchy
  CarryCauchyResidual.feature_inner
  CarryCauchyResidual.feature_projection
  CarryCauchyResidual.perpendicularFeature
  CarryCauchyResidual.perpendicularFeature_eq_complement
  CarryCauchyResidual.perpendicularFeature_inner
  CarryCauchyResidual.isometricFeature
  CarryCauchyResidual.isometricFeature_inner
  CarryCauchyResidual.tailSynthesis
  CarryCauchyResidual.isometricSynthesis
  CarryCauchyResidual.synthesis_isometry
  CarryCauchyResidual.synthesis_norm
  CarryCauchyResidual.tailSynthesis_eq_original
  CarryCauchyResidual.tailSynthesis_injective
  CarryCauchyResidual.finitePhysicalIsometry
  CarryCauchyResidual.finitePhysicalIsometry_exact
  CarryCauchyResidual.sourceReturn
  CarryCauchyResidual.feedbackDenominator
  CarryCauchyResidual.incidentCoefficient
  CarryCauchyResidual.returnedCoefficient
  CarryCauchyResidual.nativeIn_basis
  CarryCauchyResidual.nativeOut_basis
  CarryCauchyResidual.remainingIncident_basis
  CarryCauchyResidual.remainingIncident_basis_isometric
  CarryCauchyResidual.residual_basis_kernel
  CarryCauchyResidual.tailInput
  CarryCauchyResidual.tailCoefficients
  CarryCauchyResidual.eraseHead_eq_tail
  CarryCauchyResidual.linearMap_tail
  CarryCauchyResidual.incidentCoordinates
  CarryCauchyResidual.returnedCoordinates
  CarryCauchyResidual.incidentCoordinates_injective
  CarryCauchyResidual.remainingIncident_tail
  CarryCauchyResidual.nativeOut_tail
  CarryCauchyResidual.residual_same_cauchy
  CarryCauchyResidual.residual_full_source
  CarryCauchyResidual.reducedReturn
  CarryCauchyResidual.reducedReturn_formula
  CarryCauchyResidual.reduced_coordinates_exact
  CarryCauchyResidual.residual_return_comparison
  CarryCauchyResidual.controlMultiplier
  CarryCauchyResidual.controlCoefficients
  CarryCauchyResidual.controlPair
  CarryCauchyResidual.control_diagonal_contracts
  CarryCauchyResidual.control_first_diagonal
  CarryCauchyResidual.control_second_diagonal
  CarryCauchyResidual.control_cross
  CarryCauchyResidual.control_full_negative

#audit_cauchy_residual source
  CarryCauchyResidual.radialScale
  CarryCauchyResidual.radialScale_ne_zero
  CarryCauchyResidual.curvature_eq_four_moment
  CarryCauchyResidual.sourceReturn_tendsto
  CarryCauchyResidual.source_tangent
  CarryCauchyResidual.returnedCoefficient_tangent
  CarryCauchyResidual.feedbackDenominator_tangent
  CarryCauchyResidual.incidentCoefficient_tangent
  CarryCauchyResidual.central_deficit_tangent
  CarryCauchyResidual.incidentCoefficient_eventually_ne_zero
  CarryCauchyResidual.reduced_coordinates_eventually_valid
  CarryCauchyResidual.reducedReturn_tendsto_one
  CarryCauchyResidual.returnedHead
  CarryCauchyResidual.projectedBothPair
  CarryCauchyResidual.projection_loss_polarized
  CarryCauchyResidual.projection_loss_energy
  CarryCauchyResidual.returnedHead_basis
  CarryCauchyResidual.nativeAnchor_norm_sq
  CarryCauchyResidual.returnedHead_energy
  CarryCauchyResidual.projection_loss_schur_tendsto
  CarryCauchyResidual.projection_loss_strict_eventually
  CarryCauchyResidual.second_source_projection_loss
  CarryCauchyResidual.jetTailCoefficients
  CarryCauchyResidual.reducedJetIncident
  CarryCauchyResidual.reducedJetReturned
  CarryCauchyResidual.reducedJetPair
  CarryCauchyResidual.reducedJetPair_exact
  CarryCauchyResidual.reducedJetPair_canonical_schur_limit
