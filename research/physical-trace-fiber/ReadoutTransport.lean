import NativeCompletion
import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerNumerator

/-! Full-source boundary readout and the native two-input kernel.
This transports the existing symplectic functional, not a positive Gram.
The state before the trace projection is retained together with its fiber. -/
namespace CarryTraceFiber
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open CanonicalCompletedC3AllCutoffOnePointHilbert
open scoped InnerProductSpace ComplexConjugate
noncomputable section

/-- The actual boundary readout factors through the actual trace map. -/
theorem completed_readout_trace (x y : Physical) :
    pairCompletedWronskianReadout x y =
      inner ℂ (projection y) (completedScalarBoundarySymplecticRotation (projection x)) := by
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_apply,
    canonicalCompletedC3OnePointCompletedTraceProjection_apply,
    completedScalarBoundarySymplecticRotation_apply, WithLp.prod_inner_apply]
  simp only [pairCompletedWronskianReadout, mixedScalarBoundaryWedge, RCLike.inner_apply, neg_mul]
  dsimp only [WithLp.fst, WithLp.snd, WithLp.ofLp_toLp]
  ring

theorem completed_readout_invisible_left (x y : Physical) :
    pairCompletedWronskianReadout (invisible x) y=0 := by
  rw [completed_readout_trace, projection_invisible, map_zero, inner_zero_right]

theorem completed_readout_invisible_right (x y : Physical) :
    pairCompletedWronskianReadout x (invisible y)=0 := by
  rw [completed_readout_trace, projection_invisible, inner_zero_left]

/-- Keeping only the balanced lift preserves this readout, while the earlier
metric theorem accounts for every physical coordinate it omits. -/
theorem completed_readout_balanced (x y : Physical) :
    pairCompletedWronskianReadout (balancedLift (projection x)) (balancedLift (projection y))=
      pairCompletedWronskianReadout x y := by
  rw [completed_readout_trace, completed_readout_trace,
    projection_balancedLift,projection_balancedLift]

/-- An actual nonzero source component is in the radical of the pulled-back
boundary form, not in the radical of the physical Hilbert metric. -/
theorem native_center_invisible_boundary_radical :
    invisible (nativeState 0 zero_mem_completedNativeHeightDomain) ≠ 0 ∧
      ∀ y : Physical,
        pairCompletedWronskianReadout
          (invisible (nativeState 0 zero_mem_completedNativeHeightDomain)) y=0 ∧
        pairCompletedWronskianReadout y
          (invisible (nativeState 0 zero_mem_completedNativeHeightDomain))=0 := by
  refine ⟨native_center_invisible_ne_zero, ?_⟩
  intro y
  exact ⟨completed_readout_invisible_left _ _,completed_readout_invisible_right _ _⟩

/-- This is the existing completed functional state, explicitly showing the
physical trace projection and the ORIGINAL archimedean/chart block. -/
theorem normalized_functional_state_from_physical (z : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3NormalizedFullWronskianFunctionalState z hz =
      (canonicalC3ChartFactorHeight z)⁻¹ •
        WithLp.toLp 2 (nativeXiCompletionFactor z • projection (nativeState z hz),
          canonicalCompletedC3ArchimedeanChartOperatorState z) := rfl

/-- Division-free identity on two independent source arguments. All original
completion and chart channels enter through the full functional states.
Its right side is the NATIVE kernel, not a newly selected moment sequence. -/
theorem physical_functional_native_kernel (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3FullWronskianFunctional
        (canonicalCompletedC3NormalizedFullWronskianFunctionalState z hz)
        (canonicalCompletedC3NormalizedFullWronskianFunctionalState w hw) =
      (2*conj (completedNativeOperatorCharacteristic z)*completedNativeOperatorCharacteristic w)*
        ((w-conj z)*canonicalCompletedNativePolarizedDslopeKernel z w) := by
  rw [← completedGreenWronskian_eq_normalizedFullSymplecticFunctional hw hz]
  change completedGreenWronskian completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion w z = _
  rw [completedGreenWronskian_eq_normalizedResponse_cross_mul
    completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion w z hwF hzF]
  change _ * canonicalCompletedNativePolarizedResponseNumerator z w = _
  rw [canonicalCompletedNativePolarizedResponseNumerator_eq_mul_dslope hz hsep]

/-- The required source/Green comparison has its exact normalization. A
positive Gram has NOT been substituted for the symplectic functional. -/
theorem native_kernel_from_physical_functional (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedNativePolarizedDslopeKernel z w =
      canonicalCompletedC3FullWronskianFunctional
        (canonicalCompletedC3NormalizedFullWronskianFunctionalState z hz)
        (canonicalCompletedC3NormalizedFullWronskianFunctionalState w hw) /
          ((2*conj (completedNativeOperatorCharacteristic z)*completedNativeOperatorCharacteristic w)*
            (w-conj z)) := by
  rw [physical_functional_native_kernel z w hz hw hzF hwF hsep]
  have hzc : conj (completedNativeOperatorCharacteristic z) ≠ 0 := by simpa using hzF
  field_simp [hzF,hwF,hzc,sub_ne_zero.mpr hsep]


/-- The diagonal is the derivative continuation, not division by zero in the
preceding separated-input formula. -/
theorem native_kernel_center_diagonal :
    canonicalCompletedNativePolarizedDslopeKernel 0 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [canonicalCompletedNativePolarizedDslopeKernel, map_zero, dslope_same]
  have h := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0
  simpa [completedNativeGreenResponseTaylorCoefficient, iteratedDeriv_one] using h

end
end CarryTraceFiber
