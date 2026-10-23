import Regression
import Lean

open Lean Elab Command
elab "#audit_c3_four_boxes " mode:ident ids:ident+ : command => do
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
  let forbidden := forbidden ++ #[
    `CarryMaterialResponseComparison.material_scale_pos,
    `CarryMixedGreen.controlResponse,
    `CarryMixedGreen.controlLoewner]
  let forbidden := if mode.getId == `orientation then forbidden else forbidden ++ #[
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth]
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
  logInfo m!"C3 original source four-box audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; allowed foundations passed"

#print axioms CarryC3Tail.fd
#print axioms CarryC3Tail.fd_zero
#print axioms CarryC3Tail.fd_succ
#print axioms CarryC3Tail.fd_shift_one
#print axioms CarryC3Tail.fd_shift_two
#print axioms CarryC3Tail.fd_shift_three
#print axioms CarryC3Tail.fd_two
#print axioms CarryC3Tail.c3Boundary
#print axioms CarryC3Tail.c3_acceleration_cell
#print axioms CarryC3Tail.c3_acceleration_finite
#print axioms CarryC3Tail.c3Sample
#print axioms CarryC3Tail.c3_sample_eq_generic_power
#print axioms CarryC3Tail.native_c3_cell_fd
#print axioms CarryC3Tail.native_c3_tail_window
#print axioms CarryC3Tail.hasDerivAt_fd
#print axioms CarryC3Tail.fd_norm_le
#print axioms CarryC3Tail.falling
#print axioms CarryC3Tail.falling_succ
#print axioms CarryC3Tail.falling_norm_le
#print axioms CarryC3Tail.cpow_derivative_chain
#print axioms CarryC3Tail.fd_cpow_norm_le
#print axioms CarryC3Tail.fd_nat_real
#print axioms CarryC3Tail.c3_exponent_bounds
#print axioms CarryC3Tail.native_fd_bound
#print axioms CarryC3Tail.c3_sample_entire
#print axioms CarryC3Tail.native_fd_entire
#print axioms CarryC3Tail.reciprocal_fourteenth_step
#print axioms CarryC3Tail.c3_power14_summable
#print axioms CarryC3Tail.c3_power14_tail
#print axioms CarryC3Tail.c3_fourteenth_summable
#print axioms CarryC3Tail.c3_fourteenth_series_bound
#print axioms CarryC3Tail.native_fd_at_infinity
#print axioms CarryC3Tail.c3_boundary_at_infinity
#print axioms CarryC3Tail.height_mem_bracket_half_plane
#print axioms CarryC3Tail.native_c3_tail_acceleration
#print axioms CarryC3Tail.acceleratedC3Tail
#print axioms CarryC3Tail.acceleratedC3Head
#print axioms CarryC3Tail.fullC3Signal
#print axioms CarryC3Tail.native_c3_head_tail
#print axioms CarryC3Tail.accelerated_c3_tail_bound
#print axioms CarryC3Tail.c3_boundary_entire
#print axioms CarryC3Tail.original_c3_tail_analytic
#print axioms CarryC3Tail.accelerated_c3_tail_analytic
#print axioms CarryC3Tail.accelerated_c3_head_analytic
#print axioms CarryC3Tail.c3TailJetBudget
#print axioms CarryC3Tail.accelerated_c3_tail_jet_bound
#print axioms CarryC3Tail.native_c3_signal_jet_error
#print axioms CarryC3Tail.native_c3_seven_jet_error_at64
#print axioms CarryC3Boxes.Box.Contains
#print axioms CarryC3Boxes.Box.Subset
#print axioms CarryC3Boxes.Box.point
#print axioms CarryC3Boxes.Box.add
#print axioms CarryC3Boxes.Box.neg
#print axioms CarryC3Boxes.Box.sub
#print axioms CarryC3Boxes.Box.mul
#print axioms CarryC3Boxes.Box.inv
#print axioms CarryC3Boxes.Box.expand
#print axioms CarryC3Boxes.Box.point_contains
#print axioms CarryC3Boxes.Box.subset_contains
#print axioms CarryC3Boxes.Box.add_contains
#print axioms CarryC3Boxes.Box.neg_contains
#print axioms CarryC3Boxes.Box.sub_contains
#print axioms CarryC3Boxes.endpoint_mul_bounds
#print axioms CarryC3Boxes.Box.mul_contains
#print axioms CarryC3Boxes.Box.inv_contains
#print axioms CarryC3Boxes.gridScale
#print axioms CarryC3Boxes.roundLower
#print axioms CarryC3Boxes.roundUpper
#print axioms CarryC3Boxes.Box.round
#print axioms CarryC3Boxes.round_lower_le
#print axioms CarryC3Boxes.le_round_upper
#print axioms CarryC3Boxes.Box.round_contains
#print axioms CarryC3Boxes.badd
#print axioms CarryC3Boxes.bmul
#print axioms CarryC3Boxes.bneg
#print axioms CarryC3Boxes.bsub
#print axioms CarryC3Boxes.binv
#print axioms CarryC3Boxes.bpow
#print axioms CarryC3Boxes.bsum
#print axioms CarryC3Boxes.badd_contains
#print axioms CarryC3Boxes.bmul_contains
#print axioms CarryC3Boxes.bsub_contains
#print axioms CarryC3Boxes.binv_contains
#print axioms CarryC3Boxes.bpow_contains
#print axioms CarryC3Boxes.bsum_contains
#print axioms CarryC3Boxes.Box.expand_contains
#print axioms CarryC3Boxes.unitLogSum
#print axioms CarryC3Boxes.unitLogBox
#print axioms CarryC3Boxes.unit_log_box
#print axioms CarryC3Boxes.rationalLogBox
#print axioms CarryC3Boxes.rational_log_box
#print axioms CarryC3Boxes.piLower
#print axioms CarryC3Boxes.piUpper
#print axioms CarryC3Boxes.piLogBox
#print axioms CarryC3Boxes.pi_log_box
#print axioms CarryC3Boxes.expBox
#print axioms CarryC3Boxes.exp_polynomial_error
#print axioms CarryC3Boxes.exp_box
#print axioms CarryC3Tail.height_parameter_crosswalk
#print axioms CarryC3Tail.height_strip
#print axioms CarryC3Tail.c3_chart_inverse_bound
#print axioms CarryC3Tail.c3_xi_without_gamma_bound
#print axioms CarryC3Tail.c3ElementaryMultiplier
#print axioms CarryC3Tail.c3_elementary_bound
#print axioms CarryC3Tail.c3_value_multiplier_bound
#print axioms CarryC3Tail.native_boundary_at64_bound
#print axioms CarryC3Tail.c3_prefix_bound
#print axioms CarryC3Tail.c3_accelerated_head_at64_bound
#print axioms CarryC3Tail.boundaryWeight
#print axioms CarryC3Tail.boundary_stencil
#print axioms CarryC3Tail.sampleRealJet
#print axioms CarryC3Tail.sample_exp_formula
#print axioms CarryC3Tail.sample_jet_formula
#print axioms CarryC3Tail.jet_constant
#print axioms CarryC3Tail.jet_sub
#print axioms CarryC3Tail.headRealJet
#print axioms CarryC3Tail.accelerated_head_jet_formula
#print axioms CarryC3Boxes.sampleLogReference
#print axioms CarryC3Boxes.sampleAmplitudeReference
#print axioms CarryC3Boxes.sample_log_normalization
#print axioms CarryC3Boxes.sample_log_evaluator_check
#print axioms CarryC3Boxes.sample_amplitude_range_check
#print axioms CarryC3Boxes.sample_amplitude_evaluator_check
#print axioms CarryC3Boxes.sample_log_reference_contains
#print axioms CarryC3Boxes.sample_amplitude_reference_contains
#print axioms CarryC3Boxes.piLogReference
#print axioms CarryC3Boxes.piAmplitudeReference
#print axioms CarryC3Boxes.chartAmplitudeReference
#print axioms CarryC3Boxes.logThreeBox
#print axioms CarryC3Boxes.pi_log_evaluator_check
#print axioms CarryC3Boxes.pi_amplitude_range
#print axioms CarryC3Boxes.chart_amplitude_range
#print axioms CarryC3Boxes.pi_amplitude_check
#print axioms CarryC3Boxes.chart_amplitude_check
#print axioms CarryC3Boxes.pi_log_reference_contains
#print axioms CarryC3Boxes.log_three_reference_contains
#print axioms CarryC3Boxes.pi_amplitude_reference_contains
#print axioms CarryC3Boxes.chart_amplitude_reference_contains
#print axioms CarryC3Tail.characteristic_c3_formula
#print axioms CarryC3Tail.value_multiplier_analytic_at
#print axioms CarryC3Tail.elementary_multiplier_analytic_at
#print axioms CarryC3Tail.finiteLeft
#print axioms CarryC3Tail.finite_left_analytic
#print axioms CarryC3Tail.cauchy_quarter
#print axioms CarryC3Tail.finite_left_jet_bound
#print axioms CarryC3Tail.completedTailError
#print axioms CarryC3Tail.completedHead64
#print axioms CarryC3Tail.completed_head_tail
#print axioms CarryC3Tail.completed_tail_jet_error
#print axioms CarryC3Tail.finiteCompletedJet
#print axioms CarryC3Tail.gamma_jet_replacement_error
#print axioms CarryC3Tail.completed_jet_evaluator_error
#print axioms CarryC3Tail.convolution
#print axioms CarryC3Tail.phased_product
#print axioms CarryC3Tail.reciprocalJet
#print axioms CarryC3Tail.phased_reciprocal
#print axioms CarryC3Tail.polynomialRealJet
#print axioms CarryC3Tail.exponentialRealJet
#print axioms CarryC3Tail.chartRealJet
#print axioms CarryC3Tail.nativePolynomial
#print axioms CarryC3Tail.nativeExponential
#print axioms CarryC3Tail.nativeChart
#print axioms CarryC3Tail.polynomial_jet_formula
#print axioms CarryC3Tail.exponential_jet_formula
#print axioms CarryC3Tail.chart_jet_formula
#print axioms CarryC3Tail.leftRealJet
#print axioms CarryC3Tail.finite_left_jet_formula
#print axioms CarryC3Tail.finiteCompletedRealJet
#print axioms CarryC3Tail.finite_completed_jet_formula
#print axioms CarryC3Boxes.bsumFin
#print axioms CarryC3Boxes.bsumFin_contains
#print axioms CarryC3Boxes.sampleJetBox
#print axioms CarryC3Boxes.sample_jet_box
#print axioms CarryC3Boxes.headJetBox
#print axioms CarryC3Boxes.head_jet_box
#print axioms CarryC3Boxes.polynomialJetBox
#print axioms CarryC3Boxes.exponentialJetBox
#print axioms CarryC3Boxes.chartJetBox
#print axioms CarryC3Boxes.convolutionBox
#print axioms CarryC3Boxes.convolution_box
#print axioms CarryC3Boxes.reciprocalJetBox
#print axioms CarryC3Boxes.reciprocal_jet_box
#print axioms CarryC3Boxes.leftJetBox
#print axioms CarryC3Boxes.completedJetBox
#print axioms CarryC3Boxes.polynomial_jet_box
#print axioms CarryC3Boxes.exponential_jet_box
#print axioms CarryC3Boxes.chart_jet_box
#print axioms CarryC3Boxes.chart_center_interval_negative
#print axioms CarryC3Boxes.left_jet_box
#print axioms CarryC3Boxes.completed_jet_box
#print axioms CarryC3Boxes.headReferenceBox
#print axioms CarryC3Boxes.head_evaluator_check
#print axioms CarryC3Boxes.head_reference_contains
#print axioms CarryC3Boxes.cachedHeadJetBox
#print axioms CarryC3Boxes.cached_head_contains
#print axioms CarryC3Boxes.cachedLeftJetBox
#print axioms CarryC3Boxes.cachedCompletedJetBox
#print axioms CarryC3Boxes.cached_left_contains
#print axioms CarryC3Boxes.cached_completed_contains
#print axioms CarryC3Boxes.referenceReal
#print axioms CarryC3Boxes.reference_real_eq
#print axioms CarryC3Boxes.signedCompletedBox
#print axioms CarryC3Boxes.signedCompletedReal
#print axioms CarryC3Boxes.signed_completed_contains
#print axioms CarryC3Boxes.signed_completed_formula
#print axioms CarryC3Boxes.four_finite_evaluator_checks
#print axioms CarryC3Boxes.finite_completed_reference_error
#print axioms CarryC3Boxes.canonical_four_source_boxes
#print axioms CarryC3Boxes.canonical_two_even_determinant_pos_from_c3

#audit_c3_four_boxes c3_algebra
  CarryC3Tail.fd
  CarryC3Tail.fd_zero
  CarryC3Tail.fd_succ
  CarryC3Tail.fd_shift_one
  CarryC3Tail.fd_shift_two
  CarryC3Tail.fd_shift_three
  CarryC3Tail.fd_two
  CarryC3Tail.c3Boundary
  CarryC3Tail.c3_acceleration_cell
  CarryC3Tail.c3_acceleration_finite
  CarryC3Tail.c3Sample
  CarryC3Tail.c3_sample_eq_generic_power
  CarryC3Tail.native_c3_cell_fd
  CarryC3Tail.native_c3_tail_window

#audit_c3_four_boxes difference_analysis
  CarryC3Tail.hasDerivAt_fd
  CarryC3Tail.fd_norm_le
  CarryC3Tail.falling
  CarryC3Tail.falling_succ
  CarryC3Tail.falling_norm_le
  CarryC3Tail.cpow_derivative_chain
  CarryC3Tail.fd_cpow_norm_le
  CarryC3Tail.fd_nat_real
  CarryC3Tail.c3_exponent_bounds
  CarryC3Tail.native_fd_bound
  CarryC3Tail.c3_sample_entire
  CarryC3Tail.native_fd_entire

#audit_c3_four_boxes power_tail
  CarryC3Tail.reciprocal_fourteenth_step
  CarryC3Tail.c3_power14_summable
  CarryC3Tail.c3_power14_tail
  CarryC3Tail.c3_fourteenth_summable
  CarryC3Tail.c3_fourteenth_series_bound
  CarryC3Tail.native_fd_at_infinity
  CarryC3Tail.c3_boundary_at_infinity

#audit_c3_four_boxes infinite_c3_tail
  CarryC3Tail.height_mem_bracket_half_plane
  CarryC3Tail.native_c3_tail_acceleration
  CarryC3Tail.acceleratedC3Tail
  CarryC3Tail.acceleratedC3Head
  CarryC3Tail.fullC3Signal
  CarryC3Tail.native_c3_head_tail
  CarryC3Tail.accelerated_c3_tail_bound
  CarryC3Tail.c3_boundary_entire
  CarryC3Tail.original_c3_tail_analytic
  CarryC3Tail.accelerated_c3_tail_analytic
  CarryC3Tail.accelerated_c3_head_analytic
  CarryC3Tail.c3TailJetBudget
  CarryC3Tail.accelerated_c3_tail_jet_bound
  CarryC3Tail.native_c3_signal_jet_error
  CarryC3Tail.native_c3_seven_jet_error_at64

#audit_c3_four_boxes rational_box_engine
  CarryC3Boxes.Box.Contains
  CarryC3Boxes.Box.Subset
  CarryC3Boxes.Box.point
  CarryC3Boxes.Box.add
  CarryC3Boxes.Box.neg
  CarryC3Boxes.Box.sub
  CarryC3Boxes.Box.mul
  CarryC3Boxes.Box.inv
  CarryC3Boxes.Box.expand
  CarryC3Boxes.Box.point_contains
  CarryC3Boxes.Box.subset_contains
  CarryC3Boxes.Box.add_contains
  CarryC3Boxes.Box.neg_contains
  CarryC3Boxes.Box.sub_contains
  CarryC3Boxes.endpoint_mul_bounds
  CarryC3Boxes.Box.mul_contains
  CarryC3Boxes.Box.inv_contains
  CarryC3Boxes.gridScale
  CarryC3Boxes.roundLower
  CarryC3Boxes.roundUpper
  CarryC3Boxes.Box.round
  CarryC3Boxes.round_lower_le
  CarryC3Boxes.le_round_upper
  CarryC3Boxes.Box.round_contains
  CarryC3Boxes.badd
  CarryC3Boxes.bmul
  CarryC3Boxes.bneg
  CarryC3Boxes.bsub
  CarryC3Boxes.binv
  CarryC3Boxes.bpow
  CarryC3Boxes.bsum
  CarryC3Boxes.badd_contains
  CarryC3Boxes.bmul_contains
  CarryC3Boxes.bsub_contains
  CarryC3Boxes.binv_contains
  CarryC3Boxes.bpow_contains
  CarryC3Boxes.bsum_contains
  CarryC3Boxes.Box.expand_contains

#audit_c3_four_boxes elementary_enclosures
  CarryC3Boxes.unitLogSum
  CarryC3Boxes.unitLogBox
  CarryC3Boxes.unit_log_box
  CarryC3Boxes.rationalLogBox
  CarryC3Boxes.rational_log_box
  CarryC3Boxes.piLower
  CarryC3Boxes.piUpper
  CarryC3Boxes.piLogBox
  CarryC3Boxes.pi_log_box
  CarryC3Boxes.expBox
  CarryC3Boxes.exp_polynomial_error
  CarryC3Boxes.exp_box

#audit_c3_four_boxes original_completion_bounds
  CarryC3Tail.height_parameter_crosswalk
  CarryC3Tail.height_strip
  CarryC3Tail.c3_chart_inverse_bound
  CarryC3Tail.c3_xi_without_gamma_bound
  CarryC3Tail.c3ElementaryMultiplier
  CarryC3Tail.c3_elementary_bound
  CarryC3Tail.c3_value_multiplier_bound
  CarryC3Tail.native_boundary_at64_bound
  CarryC3Tail.c3_prefix_bound
  CarryC3Tail.c3_accelerated_head_at64_bound

#audit_c3_four_boxes native_finite_coefficients
  CarryC3Tail.boundaryWeight
  CarryC3Tail.boundary_stencil
  CarryC3Tail.sampleRealJet
  CarryC3Tail.sample_exp_formula
  CarryC3Tail.sample_jet_formula
  CarryC3Tail.jet_constant
  CarryC3Tail.jet_sub
  CarryC3Tail.headRealJet
  CarryC3Tail.accelerated_head_jet_formula

#audit_c3_four_boxes primitive_sample_boxes
  CarryC3Boxes.sampleLogReference
  CarryC3Boxes.sampleAmplitudeReference
  CarryC3Boxes.sample_log_normalization
  CarryC3Boxes.sample_log_evaluator_check
  CarryC3Boxes.sample_amplitude_range_check
  CarryC3Boxes.sample_amplitude_evaluator_check
  CarryC3Boxes.sample_log_reference_contains
  CarryC3Boxes.sample_amplitude_reference_contains

#audit_c3_four_boxes primitive_completion_boxes
  CarryC3Boxes.piLogReference
  CarryC3Boxes.piAmplitudeReference
  CarryC3Boxes.chartAmplitudeReference
  CarryC3Boxes.logThreeBox
  CarryC3Boxes.pi_log_evaluator_check
  CarryC3Boxes.pi_amplitude_range
  CarryC3Boxes.chart_amplitude_range
  CarryC3Boxes.pi_amplitude_check
  CarryC3Boxes.chart_amplitude_check
  CarryC3Boxes.pi_log_reference_contains
  CarryC3Boxes.log_three_reference_contains
  CarryC3Boxes.pi_amplitude_reference_contains
  CarryC3Boxes.chart_amplitude_reference_contains

#audit_c3_four_boxes finite_evaluation_error
  CarryC3Tail.characteristic_c3_formula
  CarryC3Tail.value_multiplier_analytic_at
  CarryC3Tail.elementary_multiplier_analytic_at
  CarryC3Tail.finiteLeft
  CarryC3Tail.finite_left_analytic
  CarryC3Tail.cauchy_quarter
  CarryC3Tail.finite_left_jet_bound
  CarryC3Tail.completedTailError
  CarryC3Tail.completedHead64
  CarryC3Tail.completed_head_tail
  CarryC3Tail.completed_tail_jet_error
  CarryC3Tail.finiteCompletedJet
  CarryC3Tail.gamma_jet_replacement_error
  CarryC3Tail.completed_jet_evaluator_error

#audit_c3_four_boxes elementary_jet_formulas
  CarryC3Tail.convolution
  CarryC3Tail.phased_product
  CarryC3Tail.reciprocalJet
  CarryC3Tail.phased_reciprocal
  CarryC3Tail.polynomialRealJet
  CarryC3Tail.exponentialRealJet
  CarryC3Tail.chartRealJet
  CarryC3Tail.nativePolynomial
  CarryC3Tail.nativeExponential
  CarryC3Tail.nativeChart
  CarryC3Tail.polynomial_jet_formula
  CarryC3Tail.exponential_jet_formula
  CarryC3Tail.chart_jet_formula
  CarryC3Tail.leftRealJet
  CarryC3Tail.finite_left_jet_formula
  CarryC3Tail.finiteCompletedRealJet
  CarryC3Tail.finite_completed_jet_formula

#audit_c3_four_boxes coefficient_enclosures
  CarryC3Boxes.bsumFin
  CarryC3Boxes.bsumFin_contains
  CarryC3Boxes.sampleJetBox
  CarryC3Boxes.sample_jet_box
  CarryC3Boxes.headJetBox
  CarryC3Boxes.head_jet_box
  CarryC3Boxes.polynomialJetBox
  CarryC3Boxes.exponentialJetBox
  CarryC3Boxes.chartJetBox
  CarryC3Boxes.convolutionBox
  CarryC3Boxes.convolution_box
  CarryC3Boxes.reciprocalJetBox
  CarryC3Boxes.reciprocal_jet_box
  CarryC3Boxes.leftJetBox
  CarryC3Boxes.completedJetBox
  CarryC3Boxes.polynomial_jet_box
  CarryC3Boxes.exponential_jet_box
  CarryC3Boxes.chart_jet_box
  CarryC3Boxes.chart_center_interval_negative
  CarryC3Boxes.left_jet_box
  CarryC3Boxes.completed_jet_box

#audit_c3_four_boxes head_evaluator_data
  CarryC3Boxes.headReferenceBox
  CarryC3Boxes.head_evaluator_check

#audit_c3_four_boxes head_coefficient_boxes
  CarryC3Boxes.head_reference_contains
  CarryC3Boxes.cachedHeadJetBox
  CarryC3Boxes.cached_head_contains
  CarryC3Boxes.cachedLeftJetBox
  CarryC3Boxes.cachedCompletedJetBox
  CarryC3Boxes.cached_left_contains
  CarryC3Boxes.cached_completed_contains

#audit_c3_four_boxes native_four_boxes
  CarryC3Boxes.referenceReal
  CarryC3Boxes.reference_real_eq
  CarryC3Boxes.signedCompletedBox
  CarryC3Boxes.signedCompletedReal
  CarryC3Boxes.signed_completed_contains
  CarryC3Boxes.signed_completed_formula
  CarryC3Boxes.four_finite_evaluator_checks
  CarryC3Boxes.finite_completed_reference_error
  CarryC3Boxes.canonical_four_source_boxes
  CarryC3Boxes.canonical_two_even_determinant_pos_from_c3
