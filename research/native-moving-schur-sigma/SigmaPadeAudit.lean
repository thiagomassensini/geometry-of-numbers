import SigmaTwoPoleModel
import Lean

open Lean Elab Command

elab "#audit_sigma_pade " ids:ident+ : command => do
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
      `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic] do
    unless seen.contains required do
      throwError "Missing original-source provenance dependency: {required}"
  logInfo m!"Sigma pencil/Padé audit: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; original characteristic and sigma jets retained"

#print axioms CarrySigmaPade.sigmaPencilGram
#print axioms CarrySigmaPade.sigmaPencilShifted
#print axioms CarrySigmaPade.sigmaPencilOperator
#print axioms CarrySigmaPade.sigmaPencil_metricSelfAdjoint
#print axioms CarrySigmaPade.hermitian_generalizedEigenvector_isotropic
#print axioms CarrySigmaPade.sigmaPadeD
#print axioms CarrySigmaPade.sigmaPadeB
#print axioms CarrySigmaPade.sigmaPadeC
#print axioms CarrySigmaPade.sigmaPadeAlpha
#print axioms CarrySigmaPade.sigmaPadeBeta
#print axioms CarrySigmaPade.sigmaPencilGram_det
#print axioms CarrySigmaPade.sigmaPencilCharacteristic
#print axioms CarrySigmaPade.sigmaPencilCharacteristic_eq_quadratic
#print axioms CarrySigmaPade.sigmaPade_cancellation_succ_succ
#print axioms CarrySigmaPade.sigmaPade_cancellation_succ_succ_succ
#print axioms CarrySigmaPade.sigmaPadeDenominator
#print axioms CarrySigmaPade.sigmaOriginalMomentSeries
#print axioms CarrySigmaPade.sigmaPadeDenominatorSeries
#print axioms CarrySigmaPade.sigmaPadeNumeratorSeries
#print axioms CarrySigmaPade.sigmaPadeProductCoeff_succ_succ
#print axioms CarrySigmaPade.sigmaPadeProductCoeff_succ_succ_succ
#print axioms CarrySigmaPade.IsPadeApproximant
#print axioms CarrySigmaPade.sigmaPadeDenominatorSeries_coeff_zero
#print axioms CarrySigmaPade.sigmaPadeDenominatorSeries_coeff_one
#print axioms CarrySigmaPade.sigmaPadeDenominatorSeries_coeff_two
#print axioms CarrySigmaPade.sigmaPadeDenominatorSeries_coeff_eq_zero_of_two_lt
#print axioms CarrySigmaPade.sigmaOriginalMomentSeries_is_pade
#print axioms CarrySigmaPade.sigmaPencilGramComplex
#print axioms CarrySigmaPade.sigmaPencilShiftedComplex
#print axioms CarrySigmaPade.sigmaPencilCharacteristicComplex
#print axioms CarrySigmaPade.sigmaPencilCharacteristicComplex_eq_quadratic
#print axioms CarrySigmaPade.sigmaPadeDenominatorComplex
#print axioms CarrySigmaPade.sigmaPencilCharacteristicComplex_eq_reciprocal_pade
#print axioms CarrySigmaPade.sigmaPencil_root_iff_reciprocal_pade_root
#print axioms CarrySigmaPade.sigmaPencil_root_classification
#print axioms CarrySigmaPade.twoPoleMoment
#print axioms CarrySigmaPade.twoPoleGram
#print axioms CarrySigmaPade.twoPoleShifted
#print axioms CarrySigmaPade.normSq_pow_aux
#print axioms CarrySigmaPade.twoPoleGram_det
#print axioms CarrySigmaPade.twoPoleGram_det_neg
#print axioms CarrySigmaPade.twoPoleGram_not_posSemidef
#print axioms CarrySigmaPade.twoPoleGram_negative_direction
#print axioms CarrySigmaPade.twoPoleMoment_recurrence
#print axioms CarrySigmaPade.twoPolePencil_characteristic
#print axioms CarrySigmaPade.inverseSquareNode
#print axioms CarrySigmaPade.inverseSquareNode_re
#print axioms CarrySigmaPade.inverseSquareNode_im
#print axioms CarrySigmaPade.inverseSquareNode_normSq
#print axioms CarrySigmaPade.inverseSquare_twoPoleGram_det
#print axioms CarrySigmaPade.inverseSquare_twoPole_negative_direction
#print axioms CarrySigmaPade.inverseSquare_twoPole_roots
#print axioms CarrySigmaPade.inverseSquare_roots_recover_height

#audit_sigma_pade
  CarrySigmaPade.sigmaPencilGram
  CarrySigmaPade.sigmaPencilShifted
  CarrySigmaPade.sigmaPencilOperator
  CarrySigmaPade.sigmaPencil_metricSelfAdjoint
  CarrySigmaPade.hermitian_generalizedEigenvector_isotropic
  CarrySigmaPade.sigmaPadeD
  CarrySigmaPade.sigmaPadeB
  CarrySigmaPade.sigmaPadeC
  CarrySigmaPade.sigmaPadeAlpha
  CarrySigmaPade.sigmaPadeBeta
  CarrySigmaPade.sigmaPencilGram_det
  CarrySigmaPade.sigmaPencilCharacteristic
  CarrySigmaPade.sigmaPencilCharacteristic_eq_quadratic
  CarrySigmaPade.sigmaPade_cancellation_succ_succ
  CarrySigmaPade.sigmaPade_cancellation_succ_succ_succ
  CarrySigmaPade.sigmaPadeDenominator
  CarrySigmaPade.sigmaOriginalMomentSeries
  CarrySigmaPade.sigmaPadeDenominatorSeries
  CarrySigmaPade.sigmaPadeNumeratorSeries
  CarrySigmaPade.sigmaPadeProductCoeff_succ_succ
  CarrySigmaPade.sigmaPadeProductCoeff_succ_succ_succ
  CarrySigmaPade.IsPadeApproximant
  CarrySigmaPade.sigmaPadeDenominatorSeries_coeff_zero
  CarrySigmaPade.sigmaPadeDenominatorSeries_coeff_one
  CarrySigmaPade.sigmaPadeDenominatorSeries_coeff_two
  CarrySigmaPade.sigmaPadeDenominatorSeries_coeff_eq_zero_of_two_lt
  CarrySigmaPade.sigmaOriginalMomentSeries_is_pade
  CarrySigmaPade.sigmaPencilGramComplex
  CarrySigmaPade.sigmaPencilShiftedComplex
  CarrySigmaPade.sigmaPencilCharacteristicComplex
  CarrySigmaPade.sigmaPencilCharacteristicComplex_eq_quadratic
  CarrySigmaPade.sigmaPadeDenominatorComplex
  CarrySigmaPade.sigmaPencilCharacteristicComplex_eq_reciprocal_pade
  CarrySigmaPade.sigmaPencil_root_iff_reciprocal_pade_root
  CarrySigmaPade.sigmaPencil_root_classification
  CarrySigmaPade.twoPoleMoment
  CarrySigmaPade.twoPoleGram
  CarrySigmaPade.twoPoleShifted
  CarrySigmaPade.normSq_pow_aux
  CarrySigmaPade.twoPoleGram_det
  CarrySigmaPade.twoPoleGram_det_neg
  CarrySigmaPade.twoPoleGram_not_posSemidef
  CarrySigmaPade.twoPoleGram_negative_direction
  CarrySigmaPade.twoPoleMoment_recurrence
  CarrySigmaPade.twoPolePencil_characteristic
  CarrySigmaPade.inverseSquareNode
  CarrySigmaPade.inverseSquareNode_re
  CarrySigmaPade.inverseSquareNode_im
  CarrySigmaPade.inverseSquareNode_normSq
  CarrySigmaPade.inverseSquare_twoPoleGram_det
  CarrySigmaPade.inverseSquare_twoPole_negative_direction
  CarrySigmaPade.inverseSquare_twoPole_roots
  CarrySigmaPade.inverseSquare_roots_recover_height
