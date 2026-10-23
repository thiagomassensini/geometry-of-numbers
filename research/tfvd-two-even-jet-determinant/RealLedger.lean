import QuarticFlux

namespace CarryTwoEvenJets
open CarrySelfAdjointOperator PhysicalSewing CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Reality comes from the original termwise native reflection, not theta
moment signs or a normalization of the complete characteristic. -/
theorem native_center_real : (nativeEvenJets 0).im = 0 := by
  have he := completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel 0
  have hi := congrArg Complex.im he
  simp only [map_zero,neg_zero,Complex.conj_im] at hi
  have hz : nativeEvenJets 0 = completedNativeOperatorCharacteristic 0 :=
    completedNativeEvenCharacteristicCoefficient_zero
  rw [hz]
  linarith

theorem native_center_eq_ofReal : nativeEvenJets 0 = ((nativeEvenJets 0).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using native_center_real

theorem native_center_re_ne_zero : (nativeEvenJets 0).re ≠ 0 := by
  intro hz
  have hn : nativeEvenJets 0 ≠ 0 := by
    change completedNativeEvenCharacteristicCoefficient 0 ≠ 0
    rw [completedNativeEvenCharacteristicCoefficient_zero]
    exact completedNativeOperatorCharacteristic_zero_ne_zero
  apply hn
  rw [native_center_eq_ofReal,hz,Complex.ofReal_zero]

/-- Strict positivity here belongs ONLY to the fourth power of the original
nonzero source value, not to the determinant one wants to prove positive. -/
theorem native_center_fourth_pos : 0 < (nativeEvenJets 0).re^4 := by
  have hs : 0 < (nativeEvenJets 0).re^2 := sq_pos_of_ne_zero native_center_re_ne_zero
  nlinarith [sq_pos_of_pos hs]

/-- Calibration of the original real determinant against the complete source numerator. -/
theorem native_real_determinant :
    (nativeEvenJets 0).re^4 *
      (canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2-
        (canonicalCompletedNativeLogDerivativeMoment 1)^2) = (quartic nativeEvenJets).re := by
  have he := congrArg Complex.re native_two_even_determinant_clear
  rw [native_center_eq_ofReal] at he
  simpa only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re] using he

/-- Finite cutoff ledger AFTER all trace and quartic crossings are assembled. -/
theorem native_real_tfvd_ledger (M : ℕ) :
    (nativeEvenJets 0).re^4 *
      (canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2-
        (canonicalCompletedNativeLogDerivativeMoment 1)^2) =
      (quartic (headEvenJets 0)+
       (∑ m ∈ Finset.range M, quarticFlux (headEvenJets m) (cellEvenJets m))+
       determinantTail M).re := by
  rw [native_real_determinant,← native_two_even_tfvd_ledger M,← native_two_even_determinant_clear]

end
end CarryTwoEvenJets
