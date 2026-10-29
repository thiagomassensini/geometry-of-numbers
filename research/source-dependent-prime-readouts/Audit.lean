import PrimeCanaries
import SignedReadoutSplit
import PrimeReturnObstruction
import MellinKernelDefect
import MellinPrimeReadout
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
    `CarrySelfAdjointOperator.nativeThetaMomentPolynomial,
    `CarrySelfAdjointOperator.nativeSourceFiveEvenDiscriminant_pos,
    `CarrySelfAdjointOperator.nativeSourceFiveEvenBoundaryEnergy_pos,
    `CarryCriticalMixed.source_nonlinear_margin_pos,
    `CarryCriticalMixed.source_correction_numerator_pos]
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
  logInfo m!"Source-dependent prime audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarrySourcePrime.primeReadout
#print axioms CarrySourcePrime.primeProjection
#print axioms CarrySourcePrime.prime_projection_apply
#print axioms CarrySourcePrime.prime_projection_zero
#print axioms CarrySourcePrime.prime_projection_add
#print axioms CarrySourcePrime.prime_projection_smul
#print axioms CarrySourcePrime.prime_readout_projection
#print axioms CarrySourcePrime.prime_projection_idempotent
#print axioms CarrySourcePrime.prime_dual_pairing
#print axioms CarrySourcePrime.prime_projection_pairing
#print axioms CarrySourcePrime.prime_projection_self_adjoint
#print axioms CarrySourcePrime.prime_projection_projected_pairing
#print axioms CarrySourcePrime.prime_projection_residual_pairing
#print axioms CarrySourcePrime.prime_residual_projection_pairing
#print axioms CarrySourcePrime.prime_projection_polarized_pythagoras
#print axioms CarrySourcePrime.prime_projection_norm_sq
#print axioms CarrySourcePrime.prime_projection_norm_sq_le
#print axioms CarrySourcePrime.prime_projection_norm_le
#print axioms CarrySourcePrime.prime_projection_nested
#print axioms CarrySourcePrime.prime_projection_nested_reverse
#print axioms CarrySourcePrime.primeAnalysis
#print axioms CarrySourcePrime.prime_contraction_readout_original
#print axioms CarrySourcePrime.prime_analysis_zero
#print axioms CarrySourcePrime.prime_analysis_apply
#print axioms CarrySourcePrime.prime_analysis_readout
#print axioms CarrySourcePrime.prime_analysis_coordinate_mask
#print axioms CarrySourcePrime.prime_analysis_pairing
#print axioms CarrySourcePrime.prime_analysis_norm_sq_le
#print axioms CarrySourcePrime.prime_analysis_nested
#print axioms CarrySourcePrime.prime_analysis_synthesis
#print axioms CarrySourcePrime.prime_analysis_all_crosses
#print axioms CarrySourcePrime.prime_analysis_three_term_polarization
#print axioms CarrySourcePrime.prime_projection_recovers_fixed_realization
#print axioms CarrySourcePrime.towerBasis
#print axioms CarrySourcePrime.primeTwo
#print axioms CarrySourcePrime.tower_basis_profile
#print axioms CarrySourcePrime.tower_basis_ne_zero
#print axioms CarrySourcePrime.prime_contraction_zero_level
#print axioms CarrySourcePrime.prime_analysis_zero_level
#print axioms CarrySourcePrime.prime_contraction_not_injective
#print axioms CarrySourcePrime.zero_level_complement_energy
#print axioms CarrySourcePrime.two_level_active_gram
#print axioms CarrySourcePrime.quadratureProjection
#print axioms CarrySourcePrime.quadrature_projection_rotation
#print axioms CarrySourcePrime.quadrature_projection_pairing
#print axioms CarrySourcePrime.quadrature_projection_rotation_pairing
#print axioms CarrySourcePrime.quadrature_projection_complex_pairing
#print axioms CarrySourcePrime.complete_signed_readout_split
#print axioms CarrySourcePrime.native_return_ratio_limit
#print axioms CarrySourcePrime.native_incident_energy_pos
#print axioms CarrySourcePrime.native_return_exceeds_fixed_fraction
#print axioms CarrySourcePrime.no_eventual_isometric_prime_return
#print axioms CarrySourcePrime.no_eventual_isometric_finite_prime_return
#print axioms CarrySourcePrime.primeColumnKernel
#print axioms CarrySourcePrime.cauchyPrimeDefect
#print axioms CarrySourcePrime.prime_column_kernel_formula
#print axioms CarrySourcePrime.cauchy_prime_pairing_split
#print axioms CarrySourcePrime.complete_chiral_kernel_prime_split
#print axioms CarrySourcePrime.prime_column_zero_row
#print axioms CarrySourcePrime.cauchy_prime_defect_center
#print axioms CarrySourcePrime.cauchy_prime_defect_negative
#print axioms CarrySourcePrime.no_cauchy_prime_positive_loss
#print axioms CarrySourcePrime.no_original_cauchy_positive_loss
#print axioms CarrySourcePrime.complete_chiral_first_source_defect
#print axioms CarrySourcePrime.originalContinuousSynthesis
#print axioms CarrySourcePrime.mellinTailPolynomial
#print axioms CarrySourcePrime.finiteTowerSynthesis
#print axioms CarrySourcePrime.finite_polynomial_with_trace
#print axioms CarrySourcePrime.original_continuous_with_trace
#print axioms CarrySourcePrime.original_continuous_zero
#print axioms CarrySourcePrime.mellin_tail_from_original_source
#print axioms CarrySourcePrime.original_continuous_toLp
#print axioms CarrySourcePrime.mellin_tail_integral
#print axioms CarrySourcePrime.mellin_integral_native_profile
#print axioms CarrySourcePrime.mellin_integral_prime_readout
#print axioms CarrySourcePrime.originalComplexContinuousSynthesis
#print axioms CarrySourcePrime.original_complex_two_quadratures
#print axioms CarrySourcePrime.original_complex_with_trace
#print axioms CarrySourcePrime.original_complex_toLp

#audit_completed_pairing 0
  CarrySourcePrime.primeReadout
  CarrySourcePrime.primeProjection
  CarrySourcePrime.prime_projection_apply
  CarrySourcePrime.prime_projection_zero
  CarrySourcePrime.prime_projection_add
  CarrySourcePrime.prime_projection_smul
  CarrySourcePrime.prime_readout_projection
  CarrySourcePrime.prime_projection_idempotent
  CarrySourcePrime.prime_dual_pairing
  CarrySourcePrime.prime_projection_pairing
  CarrySourcePrime.prime_projection_self_adjoint
  CarrySourcePrime.prime_projection_projected_pairing
  CarrySourcePrime.prime_projection_residual_pairing
  CarrySourcePrime.prime_residual_projection_pairing
  CarrySourcePrime.prime_projection_polarized_pythagoras
  CarrySourcePrime.prime_projection_norm_sq
  CarrySourcePrime.prime_projection_norm_sq_le
  CarrySourcePrime.prime_projection_norm_le
  CarrySourcePrime.prime_projection_nested
  CarrySourcePrime.prime_projection_nested_reverse
  CarrySourcePrime.primeAnalysis
  CarrySourcePrime.prime_contraction_readout_original
  CarrySourcePrime.prime_analysis_zero
  CarrySourcePrime.prime_analysis_apply
  CarrySourcePrime.prime_analysis_readout
  CarrySourcePrime.prime_analysis_coordinate_mask
  CarrySourcePrime.prime_analysis_pairing
  CarrySourcePrime.prime_analysis_norm_sq_le
  CarrySourcePrime.prime_analysis_nested
  CarrySourcePrime.prime_analysis_synthesis
  CarrySourcePrime.prime_analysis_all_crosses
  CarrySourcePrime.prime_analysis_three_term_polarization
  CarrySourcePrime.prime_projection_recovers_fixed_realization
  CarrySourcePrime.towerBasis
  CarrySourcePrime.primeTwo
  CarrySourcePrime.tower_basis_profile
  CarrySourcePrime.tower_basis_ne_zero
  CarrySourcePrime.prime_contraction_zero_level
  CarrySourcePrime.prime_analysis_zero_level
  CarrySourcePrime.prime_contraction_not_injective
  CarrySourcePrime.zero_level_complement_energy
  CarrySourcePrime.two_level_active_gram
  CarrySourcePrime.quadratureProjection
  CarrySourcePrime.quadrature_projection_rotation
  CarrySourcePrime.quadrature_projection_pairing
  CarrySourcePrime.quadrature_projection_rotation_pairing
  CarrySourcePrime.quadrature_projection_complex_pairing
  CarrySourcePrime.complete_signed_readout_split
  CarrySourcePrime.native_return_ratio_limit
  CarrySourcePrime.native_incident_energy_pos
  CarrySourcePrime.native_return_exceeds_fixed_fraction
  CarrySourcePrime.no_eventual_isometric_prime_return
  CarrySourcePrime.no_eventual_isometric_finite_prime_return
  CarrySourcePrime.primeColumnKernel
  CarrySourcePrime.cauchyPrimeDefect
  CarrySourcePrime.prime_column_kernel_formula
  CarrySourcePrime.cauchy_prime_pairing_split
  CarrySourcePrime.complete_chiral_kernel_prime_split
  CarrySourcePrime.prime_column_zero_row
  CarrySourcePrime.cauchy_prime_defect_center
  CarrySourcePrime.cauchy_prime_defect_negative
  CarrySourcePrime.no_cauchy_prime_positive_loss
  CarrySourcePrime.no_original_cauchy_positive_loss
  CarrySourcePrime.complete_chiral_first_source_defect
  CarrySourcePrime.originalContinuousSynthesis
  CarrySourcePrime.mellinTailPolynomial
  CarrySourcePrime.finiteTowerSynthesis
  CarrySourcePrime.finite_polynomial_with_trace
  CarrySourcePrime.original_continuous_with_trace
  CarrySourcePrime.original_continuous_zero
  CarrySourcePrime.mellin_tail_from_original_source
  CarrySourcePrime.original_continuous_toLp
  CarrySourcePrime.mellin_tail_integral
  CarrySourcePrime.mellin_integral_native_profile
  CarrySourcePrime.mellin_integral_prime_readout
  CarrySourcePrime.originalComplexContinuousSynthesis
  CarrySourcePrime.original_complex_two_quadratures
  CarrySourcePrime.original_complex_with_trace
  CarrySourcePrime.original_complex_toLp
#print axioms CarrySelfAdjointOperator.RealFirstNative.primeContractionLinear
