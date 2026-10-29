import SourceSpan
import CarrySelfAdjointOperator.CompletedNativeSourceThreeSectorSewing

/-! The SAME completed native kernel and four-channel residual, with the
exact transport images from the physical split. This retains the distinction
between a fixed consumer parameter and two native spectral source slots. -/
namespace CarryFiberTransport
open CarrySelfAdjointOperator CarryTraceFiber CPFormal.Analytic.Cp
open scoped InnerProductSpace ComplexConjugate
noncomputable section

abbrev nativeSource (z : ℂ) (hz : operatorHeightParameter z ∈ genuineCriticalStrip) : Source :=
  canonicalCompletedC3EnrichedChiralSourceState z hz

/-- The signed chiral readout, in the two ORIGINAL Hilbert polarizations. -/
def signaturePair (z w : ℂ) (u v : Source) : ℂ :=
  inner ℂ (plusReadout z u) (plusReadout w v)-
    inner ℂ (minusReadout z u) (minusReadout w v)

theorem signature_trace (z w : ℂ) (u v : Source) :
    signaturePair z w (tracePart u) (tracePart v)=signaturePair z w u v := by
  simp only [signaturePair,plus_trace,minus_trace]

theorem full_functional_signature (z w : ℂ) (u v : Source) :
    canonicalCompletedC3FullWronskianFunctional (fullReadout z u) (fullReadout w v)=
      Complex.I*signaturePair z w u v := by
  exact inner_canonicalCompletedC3FullWronskianOperator_eq_polarizationDifference _ _

theorem native_full_readout (z : ℂ) (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    fullReadout z (nativeSource z hz)=canonicalCompletedC3NormalizedFullWronskianFunctionalState z hz := by
  exact canonicalCompletedC3EnrichedNormalizedFullWronskianReadout_sourceState z hz

/-- No division, no nonvanishing premise, and independent native arguments. -/
theorem native_wronskian_trace_signature (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    completedGreenWronskian completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w z =
      Complex.I*signaturePair z w
        (tracePart (nativeSource z hz)) (tracePart (nativeSource w hw)) := by
  rw [signature_trace]
  change completedGreenWronskian completedNativeOperatorCharacteristic
    (fun u => -deriv completedNativeOperatorCharacteristic u) w z=_
  rw [completedGreenWronskian_eq_normalizedFullSymplecticFunctional hw hz]
  rw [← native_full_readout z hz,← native_full_readout w hw,full_functional_signature]

/-- The exact target kernel is read from the traced part with the prescribed
completion, chart, characteristic weight and spectral separation. -/
theorem native_kernel_trace_signature (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) (hsep : w ≠ conj z) :
    Complex.I*signaturePair z w
        (tracePart (nativeSource z hz)) (tracePart (nativeSource w hw)) =
      (2*conj (completedNativeOperatorCharacteristic z)*completedNativeOperatorCharacteristic w)*
        ((w-conj z)*canonicalCompletedNativePolarizedDslopeKernel z w) := by
  rw [signature_trace,← full_functional_signature,native_full_readout,native_full_readout]
  exact physical_functional_native_kernel z w hz hw hzF hwF hsep

/-- The full OLD four-channel defect is a comparison of the transported
fiber Gram and the complete traced signature. The defect is retained. -/
theorem native_four_channel_fiber_identity (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (ht : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricWronskianFourChannelDefect z w hz hw hs.1 ht.1 =
      (w-conj z)*inner ℂ
        (ambientReadout (fiberPart (nativeSource z hs)))
        (ambientReadout (fiberPart (nativeSource w ht))) -
      Complex.I*signaturePair z w
        (tracePart (nativeSource z hs)) (tracePart (nativeSource w ht)) := by
  rw [ambient_fiber,ambient_fiber]
  have h := canonicalCompletedC3CoisometricWronskianFourChannelDefect_eq_sub z w hz hw hs ht
  rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel,
    inner_completedC3SymplecticCameraState_eq_ambientResponseKernel,
    native_wronskian_trace_signature z w hs ht] at h
  exact h

end
end CarryFiberTransport
