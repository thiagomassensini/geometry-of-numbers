import PhysicalRay
import GeneralCorrectionForm
import AffineFrameObstruction
import CarrySelfAdjointOperator.CompletedNativeChiralReturnTenthSourceIntegral
import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence
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
  logInfo m!"Binomial Green audit tier {tier.getNat}: {ids.size} public roots; {seen.size} type/body dependencies; standard axioms only"

#print axioms CarryBinomialGreen.difference
#print axioms CarryBinomialGreen.difference_succ
#print axioms CarryBinomialGreen.difference_mul_coordinate
#print axioms CarryBinomialGreen.shiftedPower
#print axioms CarryBinomialGreen.triangular
#print axioms CarryBinomialGreen.secondOffset
#print axioms CarryBinomialGreen.shifted_power_sum
#print axioms CarryBinomialGreen.shifted_power_zero
#print axioms CarryBinomialGreen.shifted_power_self
#print axioms CarryBinomialGreen.shifted_power_recurrence
#print axioms CarryBinomialGreen.shifted_power_first
#print axioms CarryBinomialGreen.shifted_power_second
#print axioms CarryBinomialGreen.homogeneous
#print axioms CarryBinomialGreen.mixedCoefficient
#print axioms CarryBinomialGreen.mixed_coefficient_zero
#print axioms CarryBinomialGreen.mixed_coefficient_leading
#print axioms CarryBinomialGreen.mixed_coefficient_next
#print axioms CarryBinomialGreen.firstRadialCoefficient
#print axioms CarryBinomialGreen.first_radial_coefficient_all_order
#print axioms CarryBinomialGreen.parityRadialCoefficient
#print axioms CarryBinomialGreen.same_parity_first_correction
#print axioms CarryBinomialGreen.even_coefficient_regression
#print axioms CarryBinomialGreen.coefficient_two_by_two_negative
#print axioms CarryBinomialGreen.realWeight
#print axioms CarryBinomialGreen.mixedStencil
#print axioms CarryBinomialGreen.homogeneous_division
#print axioms CarryBinomialGreen.homogeneous_even_quotient
#print axioms CarryBinomialGreen.mixed_stencil_homogeneous
#print axioms CarryBinomialGreen.original_quotient_first_correction
#print axioms CarryBinomialGreen.original_quotient_same_parity
#print axioms CarryBinomialGreen.parityInput
#print axioms CarryBinomialGreen.parity_source_original
#print axioms CarryBinomialGreen.parity_input_even
#print axioms CarryBinomialGreen.parity_green_vector_split
#print axioms CarryBinomialGreen.parity_green_four_sectors
#print axioms CarryBinomialGreen.parity_source_all_crosses
#print axioms CarryBinomialGreen.nodeRay
#print axioms CarryBinomialGreen.rawRay
#print axioms CarryBinomialGreen.readout_dilation_analytic
#print axioms CarryBinomialGreen.node_ray_analytic
#print axioms CarryBinomialGreen.raw_ray_analytic
#print axioms CarryBinomialGreen.node_ray_coefficient
#print axioms CarryBinomialGreen.raw_ray_derivative
#print axioms CarryBinomialGreen.raw_ray_coefficient
#print axioms CarryBinomialGreen.native_first_correction_all_order
#print axioms CarryBinomialGreen.native_same_parity_first_correction
#print axioms CarryBinomialGreen.raw_ray_exact_remainder
#print axioms CarryBinomialGreen.evenScale
#print axioms CarryBinomialGreen.even_scale_original
#print axioms CarryBinomialGreen.forward_weight_real
#print axioms CarryBinomialGreen.even_jet_input_real
#print axioms CarryBinomialGreen.raw_ray_real
#print axioms CarryBinomialGreen.even_physical_ray
#print axioms CarryBinomialGreen.momentBilinear
#print axioms CarryBinomialGreen.correctionBilinear
#print axioms CarryBinomialGreen.correction_bilinear_three_pairings
#print axioms CarryBinomialGreen.correction_bilinear_pr88
#print axioms CarryBinomialGreen.correction_bilinear_canonical_pr88
#print axioms CarryBinomialGreen.source_schur_eq_of_prefix
#print axioms CarryBinomialGreen.alterFifthMoment
#print axioms CarryBinomialGreen.alter_fifth_prefix
#print axioms CarryBinomialGreen.alter_fifth_matrix
#print axioms CarryBinomialGreen.alter_fifth_coupling
#print axioms CarryBinomialGreen.alter_fifth_schur
#print axioms CarryBinomialGreen.alter_fifth_critical_polynomial
#print axioms CarryBinomialGreen.momentCorrection
#print axioms CarryBinomialGreen.moment_correction_canonical
#print axioms CarryBinomialGreen.alter_fifth_correction
#print axioms CarryBinomialGreen.alter_fifth_critical_correction
#print axioms CarryBinomialGreen.arbitrary_correction_with_fixed_schur
#print axioms CarryBinomialGreen.twoAtomControl
#print axioms CarryBinomialGreen.two_atom_prefix_det
#print axioms CarryBinomialGreen.two_atom_prefix_isUnit
#print axioms CarryBinomialGreen.two_atom_inverse_coefficients
#print axioms CarryBinomialGreen.two_atom_critical_polynomial
#print axioms CarryBinomialGreen.two_atom_schur_zero
#print axioms CarryBinomialGreen.two_atom_correction_positive
#print axioms CarryBinomialGreen.correction_positive_does_not_force_schur_positive
#print axioms CarryBinomialGreen.fixed_readouts_linear_family_zero
#print axioms CarryBinomialGreen.fixed_readouts_linear_family_active_zero
#print axioms CarryBinomialGreen.fixed_readouts_linear_family_bessel_zero
#print axioms CarryBinomialGreen.no_fixed_readout_linear_family_of_active_ne_zero
#print axioms NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit

#audit_completed_pairing 0
  CarryBinomialGreen.difference
  CarryBinomialGreen.difference_succ
  CarryBinomialGreen.difference_mul_coordinate
  CarryBinomialGreen.shiftedPower
  CarryBinomialGreen.triangular
  CarryBinomialGreen.secondOffset
  CarryBinomialGreen.shifted_power_sum
  CarryBinomialGreen.shifted_power_zero
  CarryBinomialGreen.shifted_power_self
  CarryBinomialGreen.shifted_power_recurrence
  CarryBinomialGreen.shifted_power_first
  CarryBinomialGreen.shifted_power_second
  CarryBinomialGreen.homogeneous
  CarryBinomialGreen.mixedCoefficient
  CarryBinomialGreen.mixed_coefficient_zero
  CarryBinomialGreen.mixed_coefficient_leading
  CarryBinomialGreen.mixed_coefficient_next
  CarryBinomialGreen.firstRadialCoefficient
  CarryBinomialGreen.first_radial_coefficient_all_order
  CarryBinomialGreen.parityRadialCoefficient
  CarryBinomialGreen.same_parity_first_correction
  CarryBinomialGreen.even_coefficient_regression
  CarryBinomialGreen.coefficient_two_by_two_negative
  CarryBinomialGreen.realWeight
  CarryBinomialGreen.mixedStencil
  CarryBinomialGreen.homogeneous_division
  CarryBinomialGreen.homogeneous_even_quotient
  CarryBinomialGreen.mixed_stencil_homogeneous
  CarryBinomialGreen.original_quotient_first_correction
  CarryBinomialGreen.original_quotient_same_parity
  CarryBinomialGreen.parityInput
  CarryBinomialGreen.parity_source_original
  CarryBinomialGreen.parity_input_even
  CarryBinomialGreen.parity_green_vector_split
  CarryBinomialGreen.parity_green_four_sectors
  CarryBinomialGreen.parity_source_all_crosses
  CarryBinomialGreen.fixed_readouts_linear_family_zero
  CarryBinomialGreen.fixed_readouts_linear_family_active_zero
  CarryBinomialGreen.fixed_readouts_linear_family_bessel_zero
  CarryBinomialGreen.no_fixed_readout_linear_family_of_active_ne_zero

#audit_completed_pairing 1
  CarryBinomialGreen.nodeRay
  CarryBinomialGreen.rawRay
  CarryBinomialGreen.readout_dilation_analytic
  CarryBinomialGreen.node_ray_analytic
  CarryBinomialGreen.raw_ray_analytic
  CarryBinomialGreen.node_ray_coefficient
  CarryBinomialGreen.raw_ray_derivative
  CarryBinomialGreen.raw_ray_coefficient
  CarryBinomialGreen.native_first_correction_all_order
  CarryBinomialGreen.native_same_parity_first_correction
  CarryBinomialGreen.raw_ray_exact_remainder
  CarryBinomialGreen.evenScale
  CarryBinomialGreen.even_scale_original
  CarryBinomialGreen.forward_weight_real
  CarryBinomialGreen.even_jet_input_real
  CarryBinomialGreen.raw_ray_real
  CarryBinomialGreen.even_physical_ray
  CarryBinomialGreen.momentBilinear
  CarryBinomialGreen.correctionBilinear
  CarryBinomialGreen.correction_bilinear_three_pairings
  CarryBinomialGreen.correction_bilinear_pr88
  CarryBinomialGreen.correction_bilinear_canonical_pr88
  CarryBinomialGreen.source_schur_eq_of_prefix
  CarryBinomialGreen.alterFifthMoment
  CarryBinomialGreen.alter_fifth_prefix
  CarryBinomialGreen.alter_fifth_matrix
  CarryBinomialGreen.alter_fifth_coupling
  CarryBinomialGreen.alter_fifth_schur
  CarryBinomialGreen.alter_fifth_critical_polynomial
  CarryBinomialGreen.momentCorrection
  CarryBinomialGreen.moment_correction_canonical
  CarryBinomialGreen.alter_fifth_correction
  CarryBinomialGreen.alter_fifth_critical_correction
  CarryBinomialGreen.arbitrary_correction_with_fixed_schur
  CarryBinomialGreen.twoAtomControl
  CarryBinomialGreen.two_atom_prefix_det
  CarryBinomialGreen.two_atom_prefix_isUnit
  CarryBinomialGreen.two_atom_inverse_coefficients
  CarryBinomialGreen.two_atom_critical_polynomial
  CarryBinomialGreen.two_atom_schur_zero
  CarryBinomialGreen.two_atom_correction_positive
  CarryBinomialGreen.correction_positive_does_not_force_schur_positive

#audit_completed_pairing 1
  CarryBinomialGreen.difference
  CarryBinomialGreen.difference_succ
  CarryBinomialGreen.difference_mul_coordinate
  CarryBinomialGreen.shiftedPower
  CarryBinomialGreen.triangular
  CarryBinomialGreen.secondOffset
  CarryBinomialGreen.shifted_power_sum
  CarryBinomialGreen.shifted_power_zero
  CarryBinomialGreen.shifted_power_self
  CarryBinomialGreen.shifted_power_recurrence
  CarryBinomialGreen.shifted_power_first
  CarryBinomialGreen.shifted_power_second
  CarryBinomialGreen.homogeneous
  CarryBinomialGreen.mixedCoefficient
  CarryBinomialGreen.mixed_coefficient_zero
  CarryBinomialGreen.mixed_coefficient_leading
  CarryBinomialGreen.mixed_coefficient_next
  CarryBinomialGreen.firstRadialCoefficient
  CarryBinomialGreen.first_radial_coefficient_all_order
  CarryBinomialGreen.parityRadialCoefficient
  CarryBinomialGreen.same_parity_first_correction
  CarryBinomialGreen.even_coefficient_regression
  CarryBinomialGreen.coefficient_two_by_two_negative
  CarryBinomialGreen.realWeight
  CarryBinomialGreen.mixedStencil
  CarryBinomialGreen.homogeneous_division
  CarryBinomialGreen.homogeneous_even_quotient
  CarryBinomialGreen.mixed_stencil_homogeneous
  CarryBinomialGreen.original_quotient_first_correction
  CarryBinomialGreen.original_quotient_same_parity
  CarryBinomialGreen.parityInput
  CarryBinomialGreen.parity_source_original
  CarryBinomialGreen.parity_input_even
  CarryBinomialGreen.parity_green_vector_split
  CarryBinomialGreen.parity_green_four_sectors
  CarryBinomialGreen.parity_source_all_crosses
  CarryBinomialGreen.nodeRay
  CarryBinomialGreen.rawRay
  CarryBinomialGreen.readout_dilation_analytic
  CarryBinomialGreen.node_ray_analytic
  CarryBinomialGreen.raw_ray_analytic
  CarryBinomialGreen.node_ray_coefficient
  CarryBinomialGreen.raw_ray_derivative
  CarryBinomialGreen.raw_ray_coefficient
  CarryBinomialGreen.native_first_correction_all_order
  CarryBinomialGreen.native_same_parity_first_correction
  CarryBinomialGreen.raw_ray_exact_remainder
  CarryBinomialGreen.evenScale
  CarryBinomialGreen.even_scale_original
  CarryBinomialGreen.forward_weight_real
  CarryBinomialGreen.even_jet_input_real
  CarryBinomialGreen.raw_ray_real
  CarryBinomialGreen.even_physical_ray
  CarryBinomialGreen.momentBilinear
  CarryBinomialGreen.correctionBilinear
  CarryBinomialGreen.correction_bilinear_three_pairings
  CarryBinomialGreen.correction_bilinear_pr88
  CarryBinomialGreen.correction_bilinear_canonical_pr88
  CarryBinomialGreen.source_schur_eq_of_prefix
  CarryBinomialGreen.alterFifthMoment
  CarryBinomialGreen.alter_fifth_prefix
  CarryBinomialGreen.alter_fifth_matrix
  CarryBinomialGreen.alter_fifth_coupling
  CarryBinomialGreen.alter_fifth_schur
  CarryBinomialGreen.alter_fifth_critical_polynomial
  CarryBinomialGreen.momentCorrection
  CarryBinomialGreen.moment_correction_canonical
  CarryBinomialGreen.alter_fifth_correction
  CarryBinomialGreen.alter_fifth_critical_correction
  CarryBinomialGreen.arbitrary_correction_with_fixed_schur
  CarryBinomialGreen.twoAtomControl
  CarryBinomialGreen.two_atom_prefix_det
  CarryBinomialGreen.two_atom_prefix_isUnit
  CarryBinomialGreen.two_atom_inverse_coefficients
  CarryBinomialGreen.two_atom_critical_polynomial
  CarryBinomialGreen.two_atom_schur_zero
  CarryBinomialGreen.two_atom_correction_positive
  CarryBinomialGreen.correction_positive_does_not_force_schur_positive
  CarryBinomialGreen.fixed_readouts_linear_family_zero
  CarryBinomialGreen.fixed_readouts_linear_family_active_zero
  CarryBinomialGreen.fixed_readouts_linear_family_bessel_zero
  CarryBinomialGreen.no_fixed_readout_linear_family_of_active_ne_zero

#audit_completed_pairing 2
  CarrySelfAdjointOperator.nativeSourceFiveEvenDiscriminant_pos
  CarrySelfAdjointOperator.nativeSourceFiveEvenBoundaryEnergy_pos
  CarrySelfAdjointOperator.primeDepthGeometricMoment_eq_canonical
  CarrySelfAdjointOperator.nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment

#print axioms CarrySelfAdjointOperator.nativeSourceFiveEvenDiscriminant_pos
#print axioms CarrySelfAdjointOperator.nativeSourceFiveEvenBoundaryEnergy_pos
#print axioms CarrySelfAdjointOperator.primeDepthGeometricMoment_eq_canonical
#print axioms CarrySelfAdjointOperator.nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment
