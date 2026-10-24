import AlignmentTest
import GreenBudget
import Lean

open Lean Elab Command
elab "#audit_completed_pairing " tier:num ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let moments := `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment
  let forbidden := #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg]
  let signs := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_ne_zero,
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial]
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
      if forbidden.contains name || name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden downstream sign consumer: {name}"
      if tier.getNat == 0 && name == moments then
        throwError "Moment-defined construction: {name}"
      if tier.getNat <= 1 && signs.contains name then
        throwError "Finite sign or theta-moment dependency outside canary: {name}"
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
      else
        throwError "Missing dependency: {name}"
  logInfo m!"Native mean/contrast audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryMeanContrast.meanPort
#print axioms CarryMeanContrast.contrastPort
#print axioms CarryMeanContrast.mean_contrast_reconstruct
#print axioms CarryMeanContrast.signed_form_mean_contrast
#print axioms CarryMeanContrast.signed_energy_mean_contrast
#print axioms CarryMeanContrast.equal_legs_contrast
#print axioms CarryMeanContrast.equal_legs_mean
#print axioms CarryMeanContrast.completed_equal_legs_mean_contrast
#print axioms CarryMeanContrast.mean_power
#print axioms CarryMeanContrast.contrast_power
#print axioms CarryMeanContrast.symmetric_alignment_necessary
#print axioms CarryMeanContrast.corrected_kernel_mean_contrast
#print axioms CarryMeanContrast.nativeResponse
#print axioms CarryMeanContrast.normalized_chiral_mean
#print axioms CarryMeanContrast.projective_mean_response
#print axioms CarryMeanContrast.projective_contrast_response
#print axioms CarryMeanContrast.alignmentDefect
#print axioms CarryMeanContrast.alignment_defect_common_refinement
#print axioms CarryMeanContrast.weighted_alignment_defect
#print axioms CarryMeanContrast.no_symmetric_alignment_of_nonzero_defect
#print axioms CarryMeanContrast.no_symmetric_alignment_weighted
#print axioms CarryMeanContrast.radial_cross_real_ne_zero
#print axioms CarryMeanContrast.no_symmetric_two_original_ports
#print axioms CarryMeanContrast.greenDensity
#print axioms CarryMeanContrast.greenBudget
#print axioms CarryMeanContrast.green_density_remainder
#print axioms CarryMeanContrast.green_density_lower
#print axioms CarryMeanContrast.green_density_continuousOn
#print axioms CarryMeanContrast.green_budget_lower
#print axioms CarryMeanContrast.c2_green_budget_gt_half

#audit_completed_pairing 0
  CarryMeanContrast.meanPort
  CarryMeanContrast.contrastPort
  CarryMeanContrast.mean_contrast_reconstruct
  CarryMeanContrast.signed_form_mean_contrast
  CarryMeanContrast.signed_energy_mean_contrast
  CarryMeanContrast.equal_legs_contrast
  CarryMeanContrast.equal_legs_mean
  CarryMeanContrast.completed_equal_legs_mean_contrast
  CarryMeanContrast.mean_power
  CarryMeanContrast.contrast_power
  CarryMeanContrast.symmetric_alignment_necessary
  CarryMeanContrast.corrected_kernel_mean_contrast
  CarryMeanContrast.nativeResponse
  CarryMeanContrast.normalized_chiral_mean
  CarryMeanContrast.projective_mean_response
  CarryMeanContrast.projective_contrast_response
  CarryMeanContrast.alignmentDefect
  CarryMeanContrast.alignment_defect_common_refinement
  CarryMeanContrast.weighted_alignment_defect
  CarryMeanContrast.no_symmetric_alignment_of_nonzero_defect
  CarryMeanContrast.no_symmetric_alignment_weighted
  CarryMeanContrast.radial_cross_real_ne_zero
  CarryMeanContrast.no_symmetric_two_original_ports
  CarryMeanContrast.greenDensity
  CarryMeanContrast.greenBudget
  CarryMeanContrast.green_density_remainder
  CarryMeanContrast.green_density_lower
  CarryMeanContrast.green_density_continuousOn
  CarryMeanContrast.green_budget_lower
  CarryMeanContrast.c2_green_budget_gt_half

#audit_completed_pairing 0
  CarryMeanContrast.meanPort
  CarryMeanContrast.contrastPort
  CarryMeanContrast.mean_contrast_reconstruct
  CarryMeanContrast.signed_form_mean_contrast
  CarryMeanContrast.signed_energy_mean_contrast
  CarryMeanContrast.equal_legs_contrast
  CarryMeanContrast.equal_legs_mean
  CarryMeanContrast.completed_equal_legs_mean_contrast
  CarryMeanContrast.mean_power
  CarryMeanContrast.contrast_power
  CarryMeanContrast.symmetric_alignment_necessary
  CarryMeanContrast.corrected_kernel_mean_contrast
  CarryMeanContrast.nativeResponse
  CarryMeanContrast.normalized_chiral_mean
  CarryMeanContrast.projective_mean_response
  CarryMeanContrast.projective_contrast_response
  CarryMeanContrast.alignmentDefect
  CarryMeanContrast.alignment_defect_common_refinement
  CarryMeanContrast.weighted_alignment_defect
  CarryMeanContrast.no_symmetric_alignment_of_nonzero_defect
  CarryMeanContrast.no_symmetric_alignment_weighted
  CarryMeanContrast.radial_cross_real_ne_zero
  CarryMeanContrast.no_symmetric_two_original_ports
  CarryMeanContrast.greenDensity
  CarryMeanContrast.greenBudget
  CarryMeanContrast.green_density_remainder
  CarryMeanContrast.green_density_lower
  CarryMeanContrast.green_density_continuousOn
  CarryMeanContrast.green_budget_lower
  CarryMeanContrast.c2_green_budget_gt_half
