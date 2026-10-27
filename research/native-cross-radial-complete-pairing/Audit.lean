import RadialRegression
import Lean

open Lean Elab Command
elab "#audit_cross_radial " group:ident ids:ident+ : command => do
  let construction := group.getId == `construction
  let signCanary := group.getId == `sign_canary
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
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
          (!signCanary && name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos) ||
          (construction && name == `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment) ||
          name.toString.startsWith "CarrySixthEven." ||
          name.toString.startsWith "CarrySixthOdd." ||
          name.toString.startsWith "CarrySeventhEven." ||
          name.toString.startsWith "CarryThetaPolarized." then
        throwError "Forbidden canonical/sign dependency: {name}"
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
  logInfo m!"Complete cross-radial pairing {group.getId}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only; canonical moments forbidden={construction}; preexisting h0-sign allowed={signCanary}"

#print axioms CarryCrossRadial.crossScale
#print axioms CarryCrossRadial.cross_scale_symm
#print axioms CarryCrossRadial.cross_scale_diagonal
#print axioms CarryCrossRadial.cross_scale_pos
#print axioms CarryCrossRadial.crossSignedPair
#print axioms CarryCrossRadial.cross_pair_diagonal
#print axioms CarryCrossRadial.cross_contrast_mean_scale
#print axioms CarryCrossRadial.complete_cross_pair
#print axioms CarryCrossRadial.crossMixedPair
#print axioms CarryCrossRadial.cross_mixed_exact
#print axioms CarryCrossRadial.cross_mixed_conjugate
#print axioms CarryCrossRadial.cross_mixed_real_zero
#print axioms CarryCrossRadial.cross_source_reconstruction
#print axioms CarryCrossRadial.cross_source_nine_pairings
#print axioms CarryCrossRadial.crossGreenPair
#print axioms CarryCrossRadial.cross_green_eq_original
#print axioms CarryCrossRadial.cross_green_four_blocks
#print axioms CarryCrossRadial.firstCrossPair
#print axioms CarryCrossRadial.first_cross_exact
#print axioms CarryCrossRadial.doubled_index_tendsto
#print axioms CarryCrossRadial.doubled_step
#print axioms CarryCrossRadial.doubled_cross_scale
#print axioms CarryCrossRadial.doubledFirstPair
#print axioms CarryCrossRadial.doubled_first_exact
#print axioms CarryCrossRadial.doubledLeading
#print axioms CarryCrossRadial.doubledNext
#print axioms CarryCrossRadial.doubledRemainder
#print axioms CarryCrossRadial.doubled_remainder_continuous
#print axioms CarryCrossRadial.doubled_scaled_expansion
#print axioms CarryCrossRadial.doubled_unscaled_expansion
#print axioms CarryCrossRadial.doubled_scaled_tendsto
#print axioms CarryCrossRadial.doubled_next_tendsto
#print axioms CarryCrossRadial.doubled_green_scaled_tendsto
#print axioms CarryCrossRadial.first_cross_diagonal
#print axioms CarryCrossRadial.first_cross_diagonal_scaled_tendsto
#print axioms CarryCrossRadial.doubled_leading_eq_zero_iff
#print axioms CarryCrossRadial.doubled_finite_limit_forces_h0_zero
#print axioms CarryCrossRadial.doubled_no_finite_limit_of_h0_ne_zero
#print axioms CarryCrossRadial.doubled_no_finite_limit
#print axioms CarryCrossRadial.doubled_imaginary_scaled_tendsto

#audit_cross_radial construction
  CarryCrossRadial.crossScale
  CarryCrossRadial.cross_scale_symm
  CarryCrossRadial.cross_scale_diagonal
  CarryCrossRadial.cross_scale_pos
  CarryCrossRadial.crossSignedPair
  CarryCrossRadial.cross_pair_diagonal
  CarryCrossRadial.cross_contrast_mean_scale
  CarryCrossRadial.complete_cross_pair
  CarryCrossRadial.crossMixedPair
  CarryCrossRadial.cross_mixed_exact
  CarryCrossRadial.cross_mixed_conjugate
  CarryCrossRadial.cross_mixed_real_zero
  CarryCrossRadial.cross_source_reconstruction
  CarryCrossRadial.cross_source_nine_pairings
  CarryCrossRadial.crossGreenPair
  CarryCrossRadial.cross_green_eq_original
  CarryCrossRadial.cross_green_four_blocks
  CarryCrossRadial.firstCrossPair
  CarryCrossRadial.first_cross_exact
  CarryCrossRadial.doubled_index_tendsto
  CarryCrossRadial.doubled_step
  CarryCrossRadial.doubled_cross_scale
  CarryCrossRadial.doubledFirstPair
  CarryCrossRadial.doubled_first_exact
  CarryCrossRadial.first_cross_diagonal


#audit_cross_radial provenance
  CarryCrossRadial.doubledLeading
  CarryCrossRadial.doubledNext
  CarryCrossRadial.doubledRemainder
  CarryCrossRadial.doubled_remainder_continuous
  CarryCrossRadial.doubled_scaled_expansion
  CarryCrossRadial.doubled_unscaled_expansion
  CarryCrossRadial.doubled_scaled_tendsto
  CarryCrossRadial.doubled_next_tendsto
  CarryCrossRadial.doubled_green_scaled_tendsto
  CarryCrossRadial.first_cross_diagonal_scaled_tendsto
  CarryCrossRadial.doubled_leading_eq_zero_iff
  CarryCrossRadial.doubled_finite_limit_forces_h0_zero
  CarryCrossRadial.doubled_no_finite_limit_of_h0_ne_zero
  CarryCrossRadial.doubled_imaginary_scaled_tendsto


#audit_cross_radial sign_canary
  CarryCrossRadial.doubled_no_finite_limit
