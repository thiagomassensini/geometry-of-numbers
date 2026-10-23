import SourceBezout
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

namespace CarrySourceBezout
open CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section

abbrev nativeC := completedNativeRealEvenCharacteristicCoefficient
abbrev nativeH := canonicalCompletedNativeLogDerivativeMoment

/-- Only the existing original, division-free moment recurrence is used. -/
theorem native_source_recurrence : SourceRecurrence nativeC nativeH := by
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n (sourceSeries nativeC * momentSeries nativeH) =
    PowerSeries.coeff n (-(PowerSeries.derivative ℝ (sourceSeries nativeC)))
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [sourceSeries, momentSeries, PowerSeries.coeff_mk, map_neg,
    PowerSeries.coeff_derivative]
  rw [Finset.sum_range_succ]
  have hn := canonicalCompletedNativeLogDerivativeMoment_real_recurrence n
  convert hn using 1
  · simp [nativeC, nativeH, mul_comm, add_comm]
  · simp only [nativeC]
    push_cast
    ring

/-- Both parities and every finite order, for the original canonical moments. -/
theorem native_source_bezout_congruence (b : Bool) (r : ℕ) :
    coefficientBlock (sourceKernel nativeC b) r = convolutionMatrix nativeC r *
      sourceMomentMatrix nativeH (if b then 1 else 0) r *
        (convolutionMatrix nativeC r).transpose :=
  source_bezout_to_hankel_congruence nativeC nativeH native_source_recurrence b r

theorem native_source_bezout_det (b : Bool) (r : ℕ) :
    (coefficientBlock (sourceKernel nativeC b) r).det = nativeC 0 ^ (2*r) *
      (sourceMomentMatrix nativeH (if b then 1 else 0) r).det :=
  source_bezout_det nativeC nativeH native_source_recurrence b r

theorem native_source_bezout_posSemidef_iff (b : Bool) (r : ℕ) :
    (coefficientBlock (sourceKernel nativeC b) r).PosSemidef ↔
      (sourceMomentMatrix nativeH (if b then 1 else 0) r).PosSemidef :=
  source_bezout_posSemidef_iff nativeC nativeH native_source_recurrence
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero b r

theorem native_source_bezout_posDef_iff (b : Bool) (r : ℕ) :
    (coefficientBlock (sourceKernel nativeC b) r).PosDef ↔
      (sourceMomentMatrix nativeH (if b then 1 else 0) r).PosDef :=
  source_bezout_posDef_iff nativeC nativeH native_source_recurrence
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero b r

end
end CarrySourceBezout
