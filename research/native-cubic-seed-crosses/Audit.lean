import SeedFamily
import Lean

open Lean Elab Command
elab "#audit_cubic_seed " group:ident ids:ident+ : command => do
  let spatial := group.getId == `spatial
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
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
      if forbidden.contains name ||
          (spatial && name == `CarrySelfAdjointOperator.completedNativeOperatorCharacteristic) ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Canonical or downstream sign dependency in spatial proof: {name}"
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
  logInfo m!"Cubic seed {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; no canonical moments; characteristic forbidden={spatial}"

#print axioms CarryCubicSeed.seedCubicTangent
#print axioms CarryCubicSeed.positive_seed_cubic_commutator
#print axioms CarryCubicSeed.positive_seed_eq_neg_seedInput
#print axioms CarryCubicSeed.seed_cubic_tangent_native
#print axioms CarryCubicSeed.seed_cubic_tangent_resolvent
#print axioms CarryCubicSeed.quadratic_seed_polarized
#print axioms CarryCubicSeed.seed_quadratic_polarized
#print axioms CarryCubicSeed.quartic_seed_polarized
#print axioms CarryCubicSeed.seed_quartic_polarized
#print axioms CarryCubicSeed.seed_seed_polarized
#print axioms CarryCubicSeed.native_quadratic_seed_complex
#print axioms CarryCubicSeed.native_seed_quadratic_complex
#print axioms CarryCubicSeed.native_quartic_seed_complex
#print axioms CarryCubicSeed.native_seed_quartic_complex
#print axioms CarryCubicSeed.native_seed_seed_complex
#print axioms CarryCubicSeed.native_quadratic_seed
#print axioms CarryCubicSeed.native_seed_quadratic
#print axioms CarryCubicSeed.native_quartic_seed
#print axioms CarryCubicSeed.native_seed_quartic
#print axioms CarryCubicSeed.native_seed_seed
#print axioms CarryCubicSeed.quadratic_gradient_norm_le_base
#print axioms CarryCubicSeed.quartic_gradient_norm_le_base
#print axioms CarryCubicSeed.native_base_gradient_lower
#print axioms CarryCubicSeed.quadratic_margin_inner_lower
#print axioms CarryCubicSeed.native_quadratic_seed_lower
#print axioms CarryCubicSeed.native_seed_quadratic_upper
#print axioms CarryCubicSeed.native_quartic_seed_upper
#print axioms CarryCubicSeed.native_seed_quartic_lower
#print axioms CarryCubicSeed.native_seed_seed_upper
#print axioms CarryCubicSeed.native_seed_cross_signs
#print axioms CarryCubicSeed.native_quadratic_seed_sum_upper
#print axioms CarryCubicSeed.native_quartic_seed_sum_lower
#print axioms CarryCubicSeed.twoJetCubic
#print axioms CarryCubicSeed.nativeCubicFamily
#print axioms CarryCubicSeed.seedPenalty
#print axioms CarryCubicSeed.two_jet_cubic_lower
#print axioms CarryCubicSeed.seed_penalty_lower
#print axioms CarryCubicSeed.native_family_exact
#print axioms CarryCubicSeed.native_family_at_zero
#print axioms CarryCubicSeed.native_family_positive_iff
#print axioms CarryCubicSeed.native_family_strict_decrease
#print axioms CarryCubicSeed.native_family_negative_witness
#print axioms CarryCubicSeed.exists_positive_seed_negative_family

#audit_cubic_seed spatial
  CarryCubicSeed.seedCubicTangent
  CarryCubicSeed.positive_seed_cubic_commutator
  CarryCubicSeed.positive_seed_eq_neg_seedInput
  CarryCubicSeed.seed_cubic_tangent_native
  CarryCubicSeed.seed_cubic_tangent_resolvent
  CarryCubicSeed.quadratic_seed_polarized
  CarryCubicSeed.seed_quadratic_polarized
  CarryCubicSeed.quartic_seed_polarized
  CarryCubicSeed.seed_quartic_polarized
  CarryCubicSeed.seed_seed_polarized
  CarryCubicSeed.native_quadratic_seed_complex
  CarryCubicSeed.native_seed_quadratic_complex
  CarryCubicSeed.native_quartic_seed_complex
  CarryCubicSeed.native_seed_quartic_complex
  CarryCubicSeed.native_seed_seed_complex
  CarryCubicSeed.native_quadratic_seed
  CarryCubicSeed.native_seed_quadratic
  CarryCubicSeed.native_quartic_seed
  CarryCubicSeed.native_seed_quartic
  CarryCubicSeed.native_seed_seed
  CarryCubicSeed.quadratic_gradient_norm_le_base
  CarryCubicSeed.quartic_gradient_norm_le_base
  CarryCubicSeed.native_base_gradient_lower
  CarryCubicSeed.quadratic_margin_inner_lower
  CarryCubicSeed.native_quadratic_seed_lower
  CarryCubicSeed.native_seed_quadratic_upper
  CarryCubicSeed.native_quartic_seed_upper
  CarryCubicSeed.native_seed_quartic_lower
  CarryCubicSeed.native_seed_seed_upper
  CarryCubicSeed.native_seed_cross_signs
  CarryCubicSeed.native_quadratic_seed_sum_upper
  CarryCubicSeed.native_quartic_seed_sum_lower
  CarryCubicSeed.twoJetCubic
  CarryCubicSeed.nativeCubicFamily
  CarryCubicSeed.seedPenalty
  CarryCubicSeed.two_jet_cubic_lower
  CarryCubicSeed.seed_penalty_lower
  CarryCubicSeed.native_family_exact
  CarryCubicSeed.native_family_at_zero
  CarryCubicSeed.native_family_positive_iff
  CarryCubicSeed.native_family_strict_decrease
  CarryCubicSeed.native_family_negative_witness
  CarryCubicSeed.exists_positive_seed_negative_family
