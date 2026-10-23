import Regression
import Lean

open Lean Elab Command
elab "#audit_source_transport " mode:ident ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let forbidden := #[
    `CarrySixthEven.even_source_six_posDef,
    `CarrySixthOdd.odd_source_six_posDef,
    `CarrySeventhEven.seventh_even_pivot_pos,
    `CarrySeventhEven.even_source_seven_posDef,
    `CarrySelfAdjointOperator.nativeSourceSixBoundaryEnergy_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_one_pos,
    `CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth,
    `CarrySelfAdjointOperator.canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier,
    `CarrySelfAdjointOperator.ChiralReturn.radialReturnEnergyDefect_nonneg,
    `CarryC3Boxes.canonical_two_even_determinant_pos_from_c3,
    `CarryTwoEvenJets.canonical_two_even_det_pos_of_four_jet_boxes]
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
        throwError "Circular/later sign dependency: {name}"
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
        throwError "Missing dependency in imported environment: {name}"
  logInfo m!"Source residual audit {mode.getId}: roots {ids.size}; type/body closure {seen.size}; standard axioms only; forbidden sign dependencies absent"

#print axioms CarrySourceBezout.BiSeries
#print axioms CarrySourceBezout.left
#print axioms CarrySourceBezout.right
#print axioms CarrySourceBezout.divided
#print axioms CarrySourceBezout.uv
#print axioms CarrySourceBezout.divided_identity
#print axioms CarrySourceBezout.uv_ne_zero
#print axioms CarrySourceBezout.bezout
#print axioms CarrySourceBezout.bezout_numerator
#print axioms CarrySourceBezout.bezout_product
#print axioms CarrySourceBezout.momentSeries
#print axioms CarrySourceBezout.sourceSeries
#print axioms CarrySourceBezout.hankelSeries
#print axioms CarrySourceBezout.sourceKernel
#print axioms CarrySourceBezout.SourceRecurrence
#print axioms CarrySourceBezout.source_kernel_numerator_even
#print axioms CarrySourceBezout.source_kernel_numerator_odd
#print axioms CarrySourceBezout.source_kernel_even
#print axioms CarrySourceBezout.source_kernel_odd
#print axioms CarrySourceBezout.coefficientBlock
#print axioms CarrySourceBezout.convolutionMatrix
#print axioms CarrySourceBezout.hankelMatrix
#print axioms CarrySourceBezout.coeff_product_finite
#print axioms CarrySourceBezout.coefficient_congruence
#print axioms CarrySourceBezout.source_bezout_to_hankel_congruence
#print axioms CarrySourceBezout.convolutionMatrix_det
#print axioms CarrySourceBezout.source_bezout_det
#print axioms CarrySourceBezout.divided_add
#print axioms CarrySourceBezout.bezout_add_left
#print axioms CarrySourceBezout.bezout_add_right
#print axioms CarrySourceBezout.mixedSourceKernel
#print axioms CarrySourceBezout.sourceSeries_add
#print axioms CarrySourceBezout.mixedSourceKernel_add_left
#print axioms CarrySourceBezout.mixedSourceKernel_add_right
#print axioms CarrySourceBezout.sourceKernel_head_tail
#print axioms CarrySourceBezout.source_bezout_posSemidef_iff
#print axioms CarrySourceBezout.source_bezout_posDef_iff
#print axioms CarrySourceBezout.mapBi
#print axioms CarrySourceBezout.sourceSeries_map
#print axioms CarrySourceBezout.divided_map
#print axioms CarrySourceBezout.right_map
#print axioms CarrySourceBezout.bezout_map
#print axioms CarrySourceBezout.derivative_map
#print axioms CarrySourceBezout.sourceKernel_map
#print axioms CarrySourceBezout.coefficientBlock_map
#print axioms CarrySourceBezout.nativeC
#print axioms CarrySourceBezout.nativeH
#print axioms CarrySourceBezout.native_source_recurrence
#print axioms CarrySourceBezout.native_source_bezout_congruence
#print axioms CarrySourceBezout.native_source_bezout_det
#print axioms CarrySourceBezout.native_source_bezout_posSemidef_iff
#print axioms CarrySourceBezout.native_source_bezout_posDef_iff
#print axioms CarrySourceBezout.source_even_two
#print axioms CarrySourceBezout.source_odd_two
#print axioms CarrySourceBezout.source_even_two_det
#print axioms CarrySourceBezout.negativeControl
#print axioms CarrySourceBezout.negative_control_center
#print axioms CarrySourceBezout.negative_control_source_det
#print axioms CarrySourceBezout.negative_control_not_posSemidef
#print axioms CarrySourceBezout.negative_control_entire_source
#print axioms CarrySourceBezout.negativeControlH
#print axioms CarrySourceBezout.negative_control_recurrence
#print axioms CarrySourceBezout.negative_control_hankel_not_posSemidef
#print axioms CarrySourceBezout.matrixPair
#print axioms CarrySourceBezout.hankelMatrix_source
#print axioms CarrySourceBezout.criticalVector
#print axioms CarrySourceBezout.sourceDirection
#print axioms CarrySourceBezout.monicSourceDirection
#print axioms CarrySourceBezout.convolutionMatrix_isUnit
#print axioms CarrySourceBezout.sourceDirection_transport
#print axioms CarrySourceBezout.convolution_transpose_last
#print axioms CarrySourceBezout.sourceDirection_last
#print axioms CarrySourceBezout.monicSourceDirection_last
#print axioms CarrySourceBezout.congruence_pair
#print axioms CarrySourceBezout.criticalVector_mulVec
#print axioms CarrySourceBezout.criticalVector_pair
#print axioms CarrySourceBezout.monicSourceDirection_pair
#print axioms CarrySourceBezout.sourceDirection_energy
#print axioms CarrySourceBezout.monicSourceDirection_energy
#print axioms CarrySourceBezout.native_sourceDirection_remainder
#print axioms CarrySourceBezout.native_monicSourceDirection_remainder
#print axioms CarrySourceBezout.sourceCoupling
#print axioms CarrySourceBezout.sourceSchur
#print axioms CarrySourceBezout.sourceCritical
#print axioms CarrySourceBezout.source_prefix_isUnit
#print axioms CarrySourceBezout.source_block_transpose
#print axioms CarrySourceBezout.monicSourceDirection_eq_sourceCritical
#print axioms CarrySourceBezout.sourceSchur_eq_scaled
#print axioms CarrySourceBezout.native_sourceSchur_remainder
#print axioms CarrySourceBezout.NativeTrace.tracePiece
#print axioms CarrySourceBezout.NativeTrace.headTrace
#print axioms CarrySourceBezout.NativeTrace.tailTrace
#print axioms CarrySourceBezout.NativeTrace.tracePiece_add
#print axioms CarrySourceBezout.NativeTrace.stateTrace_head_tail
#print axioms CarrySourceBezout.NativeTrace.completedTrace_head_tail
#print axioms CarrySourceBezout.NativeTrace.valueMultiplier
#print axioms CarrySourceBezout.NativeTrace.completedCell
#print axioms CarrySourceBezout.NativeTrace.head_value_formula
#print axioms CarrySourceBezout.NativeTrace.head_value_seed_cells
#print axioms CarrySourceBezout.NativeTrace.head_value_succ
#print axioms CarrySourceBezout.NativeTrace.value_multiplier_analytic_at
#print axioms CarrySourceBezout.NativeTrace.valueMultiplier_analytic
#print axioms CarrySourceBezout.NativeTrace.head_value_analytic
#print axioms CarrySourceBezout.NativeTrace.completedCell_analytic
#print axioms CarrySourceBezout.NativeTrace.full_value_eventually_head_tail
#print axioms CarrySourceBezout.NativeTrace.tail_value_analytic
#print axioms CarrySourceBezout.NativeTrace.sourceJet
#print axioms CarrySourceBezout.NativeTrace.sourceJet_add
#print axioms CarrySourceBezout.literalHead
#print axioms CarrySourceBezout.literalTail
#print axioms CarrySourceBezout.literal_head_tail
#print axioms CarrySourceBezout.complexPair
#print axioms CarrySourceBezout.complexPair_add
#print axioms CarrySourceBezout.coefficientBlock_add
#print axioms CarrySourceBezout.complexPair_real
#print axioms CarrySourceBezout.literalTerm
#print axioms CarrySourceBezout.literal_four_terms
#print axioms CarrySourceBezout.literalResidualTerm
#print axioms CarrySourceBezout.native_residual_literal_four_terms
#print axioms CarrySourceBezout.sourceResponse
#print axioms CarrySourceBezout.responseCoefficient
#print axioms CarrySourceBezout.mixed_kernel_coefficient
#print axioms CarrySourceBezout.coefficientBudget
#print axioms CarrySourceBezout.coefficientBudget_nonneg
#print axioms CarrySourceBezout.mixed_coefficient_bound
#print axioms CarrySourceBezout.directionalBudget
#print axioms CarrySourceBezout.directionalBudget_nonneg
#print axioms CarrySourceBezout.mixed_direction_bound
#print axioms CarrySourceBezout.literalErrorBudget
#print axioms CarrySourceBezout.literal_error_bound
#print axioms CarrySourceBezout.native_residual_pos_of_literal_margin
#print axioms CarrySourceBezout.literal_height_half_plane
#print axioms CarrySourceBezout.literal_cell_bound
#print axioms CarrySourceBezout.literal_c3_tail_bound
#print axioms CarrySourceBezout.literal_multiplier_analytic_at
#print axioms CarrySourceBezout.literal_original_tail_analytic
#print axioms CarrySourceBezout.literal_tail_value_formula
#print axioms CarrySourceBezout.literal_head_analytic_at
#print axioms CarrySourceBezout.literal_tail_analytic_at
#print axioms CarrySourceBezout.literal_cauchy_quarter
#print axioms CarrySourceBezout.literal_tail_jet_envelope
#print axioms CarrySourceBezout.responseCoefficient_even_zero
#print axioms CarrySourceBezout.responseCoefficient_even_succ
#print axioms CarrySourceBezout.responseCoefficient_odd
#print axioms CarrySourceBezout.responseCoefficient_tendsto
#print axioms CarrySourceBezout.coefficientBudget_tendsto
#print axioms CarrySourceBezout.directionalBudget_tendsto
#print axioms CarrySourceBezout.literal_tail_tendsto_zero
#print axioms CarrySourceBezout.literal_head_tendsto
#print axioms CarrySourceBezout.responseCoefficient_zero
#print axioms CarrySourceBezout.directionalBudget_zero_left
#print axioms CarrySourceBezout.directionalBudget_zero_right
#print axioms CarrySourceBezout.literal_error_budget_tendsto_zero
#print axioms CarrySourceBezout.tracePiece_companion
#print axioms CarrySourceBezout.literal_head_companion
#print axioms CarrySourceBezout.literal_tail_companion
#print axioms CarrySourceBezout.sourceJet_neg_deriv
#print axioms CarrySourceBezout.literal_head_companion_eventually
#print axioms CarrySourceBezout.literal_tail_companion_eventually
#print axioms CarrySourceBezout.literal_head_companion_jet
#print axioms CarrySourceBezout.literal_tail_companion_jet
#print axioms CarrySourceBezout.literal_head_response_odd
#print axioms CarrySourceBezout.literal_tail_response_odd
#print axioms CarrySourceBezout.literal_head_response_even_succ
#print axioms CarrySourceBezout.literal_tail_response_even_succ
#print axioms CarrySourceBezout.mixed_four_terms
#print axioms CarrySourceBezout.boundary_repartition
#print axioms CarrySourceBezout.coefficientPair
#print axioms CarrySourceBezout.coefficientPair_four_terms
#print axioms CarrySourceBezout.coefficientPair_boundary_repartition
#print axioms CarrySourceBezout.native_residual_repartition

#audit_source_transport SourceBezout
  CarrySourceBezout.BiSeries
  CarrySourceBezout.left
  CarrySourceBezout.right
  CarrySourceBezout.divided
  CarrySourceBezout.uv
  CarrySourceBezout.divided_identity
  CarrySourceBezout.uv_ne_zero
  CarrySourceBezout.bezout
  CarrySourceBezout.bezout_numerator
  CarrySourceBezout.bezout_product
  CarrySourceBezout.momentSeries
  CarrySourceBezout.sourceSeries
  CarrySourceBezout.hankelSeries
  CarrySourceBezout.sourceKernel
  CarrySourceBezout.SourceRecurrence
  CarrySourceBezout.source_kernel_numerator_even
  CarrySourceBezout.source_kernel_numerator_odd
  CarrySourceBezout.source_kernel_even
  CarrySourceBezout.source_kernel_odd
  CarrySourceBezout.coefficientBlock
  CarrySourceBezout.convolutionMatrix
  CarrySourceBezout.hankelMatrix
  CarrySourceBezout.coeff_product_finite
  CarrySourceBezout.coefficient_congruence
  CarrySourceBezout.source_bezout_to_hankel_congruence
  CarrySourceBezout.convolutionMatrix_det
  CarrySourceBezout.source_bezout_det
  CarrySourceBezout.divided_add
  CarrySourceBezout.bezout_add_left
  CarrySourceBezout.bezout_add_right
  CarrySourceBezout.mixedSourceKernel
  CarrySourceBezout.sourceSeries_add
  CarrySourceBezout.mixedSourceKernel_add_left
  CarrySourceBezout.mixedSourceKernel_add_right
  CarrySourceBezout.sourceKernel_head_tail
  CarrySourceBezout.source_bezout_posSemidef_iff
  CarrySourceBezout.source_bezout_posDef_iff

#audit_source_transport SourceMap
  CarrySourceBezout.mapBi
  CarrySourceBezout.sourceSeries_map
  CarrySourceBezout.divided_map
  CarrySourceBezout.right_map
  CarrySourceBezout.bezout_map
  CarrySourceBezout.derivative_map
  CarrySourceBezout.sourceKernel_map
  CarrySourceBezout.coefficientBlock_map

#audit_source_transport SourceNative
  CarrySourceBezout.nativeC
  CarrySourceBezout.nativeH
  CarrySourceBezout.native_source_recurrence
  CarrySourceBezout.native_source_bezout_congruence
  CarrySourceBezout.native_source_bezout_det
  CarrySourceBezout.native_source_bezout_posSemidef_iff
  CarrySourceBezout.native_source_bezout_posDef_iff

#audit_source_transport SourceBlocks
  CarrySourceBezout.source_even_two
  CarrySourceBezout.source_odd_two
  CarrySourceBezout.source_even_two_det
  CarrySourceBezout.negativeControl
  CarrySourceBezout.negative_control_center
  CarrySourceBezout.negative_control_source_det
  CarrySourceBezout.negative_control_not_posSemidef
  CarrySourceBezout.negative_control_entire_source
  CarrySourceBezout.negativeControlH
  CarrySourceBezout.negative_control_recurrence
  CarrySourceBezout.negative_control_hankel_not_posSemidef

#audit_source_transport SchurTransport
  CarrySourceBezout.matrixPair
  CarrySourceBezout.hankelMatrix_source
  CarrySourceBezout.criticalVector
  CarrySourceBezout.sourceDirection
  CarrySourceBezout.monicSourceDirection
  CarrySourceBezout.convolutionMatrix_isUnit
  CarrySourceBezout.sourceDirection_transport
  CarrySourceBezout.convolution_transpose_last
  CarrySourceBezout.sourceDirection_last
  CarrySourceBezout.monicSourceDirection_last
  CarrySourceBezout.congruence_pair
  CarrySourceBezout.criticalVector_mulVec
  CarrySourceBezout.criticalVector_pair
  CarrySourceBezout.monicSourceDirection_pair
  CarrySourceBezout.sourceDirection_energy
  CarrySourceBezout.monicSourceDirection_energy
  CarrySourceBezout.native_sourceDirection_remainder
  CarrySourceBezout.native_monicSourceDirection_remainder

#audit_source_transport SourceSchur
  CarrySourceBezout.sourceCoupling
  CarrySourceBezout.sourceSchur
  CarrySourceBezout.sourceCritical
  CarrySourceBezout.source_prefix_isUnit
  CarrySourceBezout.source_block_transpose
  CarrySourceBezout.monicSourceDirection_eq_sourceCritical
  CarrySourceBezout.sourceSchur_eq_scaled
  CarrySourceBezout.native_sourceSchur_remainder

#audit_source_transport LiteralNativeTrace
  CarrySourceBezout.NativeTrace.tracePiece
  CarrySourceBezout.NativeTrace.headTrace
  CarrySourceBezout.NativeTrace.tailTrace
  CarrySourceBezout.NativeTrace.tracePiece_add
  CarrySourceBezout.NativeTrace.stateTrace_head_tail
  CarrySourceBezout.NativeTrace.completedTrace_head_tail
  CarrySourceBezout.NativeTrace.valueMultiplier
  CarrySourceBezout.NativeTrace.completedCell
  CarrySourceBezout.NativeTrace.head_value_formula
  CarrySourceBezout.NativeTrace.head_value_seed_cells
  CarrySourceBezout.NativeTrace.head_value_succ
  CarrySourceBezout.NativeTrace.value_multiplier_analytic_at
  CarrySourceBezout.NativeTrace.valueMultiplier_analytic
  CarrySourceBezout.NativeTrace.head_value_analytic
  CarrySourceBezout.NativeTrace.completedCell_analytic
  CarrySourceBezout.NativeTrace.full_value_eventually_head_tail
  CarrySourceBezout.NativeTrace.tail_value_analytic
  CarrySourceBezout.NativeTrace.sourceJet
  CarrySourceBezout.NativeTrace.sourceJet_add

#audit_source_transport LiteralTfvd
  CarrySourceBezout.literalHead
  CarrySourceBezout.literalTail
  CarrySourceBezout.literal_head_tail
  CarrySourceBezout.complexPair
  CarrySourceBezout.complexPair_add
  CarrySourceBezout.coefficientBlock_add
  CarrySourceBezout.complexPair_real
  CarrySourceBezout.literalTerm
  CarrySourceBezout.literal_four_terms
  CarrySourceBezout.literalResidualTerm
  CarrySourceBezout.native_residual_literal_four_terms

#audit_source_transport KernelBudget
  CarrySourceBezout.sourceResponse
  CarrySourceBezout.responseCoefficient
  CarrySourceBezout.mixed_kernel_coefficient
  CarrySourceBezout.coefficientBudget
  CarrySourceBezout.coefficientBudget_nonneg
  CarrySourceBezout.mixed_coefficient_bound
  CarrySourceBezout.directionalBudget
  CarrySourceBezout.directionalBudget_nonneg
  CarrySourceBezout.mixed_direction_bound
  CarrySourceBezout.literalErrorBudget
  CarrySourceBezout.literal_error_bound
  CarrySourceBezout.native_residual_pos_of_literal_margin

#audit_source_transport LiteralTailBounds
  CarrySourceBezout.literal_height_half_plane
  CarrySourceBezout.literal_cell_bound
  CarrySourceBezout.literal_c3_tail_bound
  CarrySourceBezout.literal_multiplier_analytic_at
  CarrySourceBezout.literal_original_tail_analytic
  CarrySourceBezout.literal_tail_value_formula
  CarrySourceBezout.literal_head_analytic_at
  CarrySourceBezout.literal_tail_analytic_at
  CarrySourceBezout.literal_cauchy_quarter
  CarrySourceBezout.literal_tail_jet_envelope

#audit_source_transport LiteralBudgetLimit
  CarrySourceBezout.responseCoefficient_even_zero
  CarrySourceBezout.responseCoefficient_even_succ
  CarrySourceBezout.responseCoefficient_odd
  CarrySourceBezout.responseCoefficient_tendsto
  CarrySourceBezout.coefficientBudget_tendsto
  CarrySourceBezout.directionalBudget_tendsto
  CarrySourceBezout.literal_tail_tendsto_zero
  CarrySourceBezout.literal_head_tendsto
  CarrySourceBezout.responseCoefficient_zero
  CarrySourceBezout.directionalBudget_zero_left
  CarrySourceBezout.directionalBudget_zero_right
  CarrySourceBezout.literal_error_budget_tendsto_zero

#audit_source_transport LiteralCompanion
  CarrySourceBezout.tracePiece_companion
  CarrySourceBezout.literal_head_companion
  CarrySourceBezout.literal_tail_companion

#audit_source_transport CompanionJets
  CarrySourceBezout.sourceJet_neg_deriv
  CarrySourceBezout.literal_head_companion_eventually
  CarrySourceBezout.literal_tail_companion_eventually
  CarrySourceBezout.literal_head_companion_jet
  CarrySourceBezout.literal_tail_companion_jet
  CarrySourceBezout.literal_head_response_odd
  CarrySourceBezout.literal_tail_response_odd
  CarrySourceBezout.literal_head_response_even_succ
  CarrySourceBezout.literal_tail_response_even_succ

#audit_source_transport Repartition
  CarrySourceBezout.mixed_four_terms
  CarrySourceBezout.boundary_repartition
  CarrySourceBezout.coefficientPair
  CarrySourceBezout.coefficientPair_four_terms
  CarrySourceBezout.coefficientPair_boundary_repartition
  CarrySourceBezout.native_residual_repartition
