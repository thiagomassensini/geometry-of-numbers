import AtomicCorrectionControl
import RadialExtrapolation
import FiniteVelocityBudget
import Lean
open Lean Elab Command
elab "#audit_flow " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarryMaterialVariation.six_critical_correction_positive,
    `CarryMaterialVariation.six_energy_eventually_above,
    `CarryMaterialVariation.six_original_eventually_above,
    `CarryBoundaryReconstruction.six_physical_eventually_decreasing,
    `CarryBoundaryReconstruction.six_boundary_tail,
    `CarryBoundaryReconstruction.six_accumulated_tail_scale,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.storage_one_original_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.storage_one_fourSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_four_eventually_norm_le_one,
    `CarrySelfAdjointOperator.storage_one_original_sevenSample_eventually_pos,
    `CarrySelfAdjointOperator.radialReturnTransfer_seven_eventually_norm_le_one,
    `CarrySelfAdjointOperator.nativeSourceEvenBoundary_positive_iff_stieltjes,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarryIntegralCertificate.material_fourth_pivot_bounds_integral,
    `CarryIntegralCertificate.material_fourth_pivot_pos_integral,
    `CarryIntegralCertificate.material_fourth_block_posDef_integral,
    `CarryIntegralCertificate.material_fourth_critical_positive_integral,
    `CarryIntegralCertificate.material_fourth_theta_integral_gate,
    `CarryIntegralCertificate.material_fourth_cholesky_integral]
  let mut todo : List Name := []
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    for a in (← collectAxioms decl) do
      unless allowed.contains a do throwError "Unexpected axiom in {decl}: {a}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      if forbidden.contains name ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden finite positivity/equivalence dependency: {name}"
      if name == `CarryIntegralCertificate.material_theta_integral_input then
        throwError "Unexpected finite interval certificate: {name}"
      seen := seen.insert name
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ => unless allowed.contains name do throwError "Unverified dependency: {name}"
        | _ => pure ()
        todo := info.type.getUsedConstants.toList ++ todo
        if let some value := info.value? (allowOpaque := true) then
          todo := value.getUsedConstants.toList ++ todo
      else throwError "Missing declaration: {name}"
  for required in #[`CarryMaterialVariation.physical_material_derivative,
      `CarryEffectiveRadial.native_response_exact_remainder,
      `CarryEffectiveRadial.source_remainder_deriv_bound,
      `CarryEffectiveRadial.six_expansion_on_disc,
      `CarryMaterialVariation.radial_jet_hasDerivAt] do
    unless seen.contains required do throwError "Missing actual source bridge: {required}"
  logInfo m!"Transitive source audit: {ids.size} roots; {seen.size} type/body dependencies; standard axioms only; finite positivity forbidden"

#audit_flow
  CarryAtomicControl.twoAtomMoment
  CarryAtomicControl.criticalParameter
  CarryAtomicControl.criticalResidual
  CarryAtomicControl.criticalCorrection
  CarryAtomicControl.two_atom_gram
  CarryAtomicControl.two_atom_positive
  CarryAtomicControl.two_atom_majorant
  CarryAtomicControl.exact_parameter
  CarryAtomicControl.exact_positive_residual
  CarryAtomicControl.exact_negative_correction
  CarryJetVariationBudget.velocityPrefix
  CarryJetVariationBudget.velocityAddressBudget
  CarryJetVariationBudget.velocityFamilyBudget
  CarryJetVariationBudget.velocity_address_budget_nonneg
  CarryJetVariationBudget.native_velocity_address_error
  CarryJetVariationBudget.physical_derivative_explicit_budget
  CarryJetVariationBudget.native_jets_derivative_explicit_budget
  CarryJetVariationBudget.native_jet_velocity_size
  CarryJetVariationBudget.native_jets_ordered_velocity_budget
  CarryRadialExtrapolation.quadratic_cancellation
  CarryRadialExtrapolation.extrapolation_error
  CarryRadialExtrapolation.radial_step_half
  CarryRadialExtrapolation.six_source_extrapolation
  CarryRadialExtrapolation.six_source_extrapolation_effective
  CarryRadialExtrapolation.original_radial_step_half
  CarryJetVariationBudget.omitted_response_derivative_bound
  CarryJetVariationBudget.native_response_derivative_prefix_error
  CarryJetVariationBudget.responseTail
  CarryJetVariationBudget.radial_response_derivative_prefix_error
  CarryJetVariationBudget.size
  CarryJetVariationBudget.variation_error_bound
  CarryJetVariationBudget.physical_derivative_approximation
