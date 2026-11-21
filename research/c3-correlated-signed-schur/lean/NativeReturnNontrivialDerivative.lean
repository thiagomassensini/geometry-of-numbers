import NativeReturnPrimitiveVariation
import CarrySelfAdjointOperator.CompletedNativeChiralReturnLinearizationObstruction

/-!
The genuine completed-native return multiplier varies between consecutive
radial nodes. Its first normalized variation is forced by the native
completed zeroth moment and is NONZERO.

Therefore deflating the first old source DOES NOT annihilate every later
independent source: the return contains a surviving physical channel.
This is a source-level obstruction to "return only cancels the inherited".
No negative Hankel pivot is inferred.
-/

namespace CarryWheelNativeSignedGate

open CarryReturnDeflation CarrySelfAdjointOperator ChiralReturn CarryPositiveSquare
open Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section
set_option autoImplicit false

def nativeSampleQuotient (k n : ℕ) : ℂ :=
  completedNativeHermiteBiehlerChiralQuotient
    (canonicalCompletedC3RadialTiltPoint k n)

def nativeSampleTangent (k n : ℕ) : ℂ :=
  Complex.I * ((nativeSampleQuotient k n + 1) /
    canonicalCompletedC3RadialTiltPoint k n)

def nativeSampleGapRatio (k : ℕ) : ℂ :=
  Complex.I * ((nativeSampleQuotient k 1 - nativeSampleQuotient k 0) /
    canonicalCompletedC3RadialTiltPoint k 0)

/-- The original derivative/first completed moment controls the source
chiral quotient curvature, with no assumed zero spectrum. -/
theorem nativeRadialSourceCurvature_eq_four_zerothMoment :
    nativeRadialSourceCurvature =
      4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral]
  unfold nativeRadialSourceCurvature
  have hf0 := completedNativeOperatorCharacteristic_zero_ne_zero
  field_simp [hf0]
  ring

/-- Pure algebra on the REAL ORIGINAL first two radial Cauchy sample nodes:
Q(2z)-Q(z) = 2 (Q(2z)+1) - (Q(z)+1). -/
theorem nativeSampleGapRatio_eq_tangent_difference (k : ℕ) :
    nativeSampleGapRatio k = 2 * nativeSampleTangent k 1 -
      nativeSampleTangent k 0 := by
  have hz : canonicalCompletedC3RadialTiltPoint k 0 ≠ 0 := by
    intro h
    exact canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0 (by rw [h]; rfl)
  have hdouble :
      canonicalCompletedC3RadialTiltPoint k 1 =
        2 * canonicalCompletedC3RadialTiltPoint k 0 := by
    simp [canonicalCompletedC3RadialTiltPoint,
      canonicalCompletedC3RadialTiltStep]
  unfold nativeSampleGapRatio nativeSampleTangent nativeSampleQuotient
  rw [hdouble]
  field_simp [hz]
  ring

/-- The transverse return variation is asymptotically the curvature
4*h0, so it cannot vanish identically on the next original source. -/
theorem nativeSampleGapRatio_tendsto_zerothMoment :
    Tendsto nativeSampleGapRatio atTop
      (nhds (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  have h0 := nativeRadialSource_tangent 0
  have h1 := nativeRadialSource_tangent 1
  have ht := (h1.const_mul (2 : ℂ)).sub h0
  have heq : nativeSampleGapRatio =
      fun k => 2 * nativeSampleTangent k 1 - nativeSampleTangent k 0 := by
    funext k
    exact nativeSampleGapRatio_eq_tangent_difference k
  rw [heq, ← nativeRadialSourceCurvature_eq_four_zerothMoment]
  convert ht using 1 <;> first | rfl | ring

/-- Even after removing the inherited first head, the quotient-driven
return does NOT vanish on the independent second native coordinate at
all sufficiently large radial cutoffs. -/
theorem nativeSampleQuotient_second_ne_first_eventually :
    ∀ᶠ k : ℕ in atTop, nativeSampleQuotient k 1 ≠ nativeSampleQuotient k 0 := by
  have hcurv : 4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num)
      (by exact_mod_cast ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos)
  have ht := nativeSampleGapRatio_tendsto_zerothMoment.eventually_ne hcurv
  filter_upwards [ht] with k hk
  intro h
  apply hk
  simp [nativeSampleGapRatio, h]

/-- Genuine SECOND source has a nonzero return after subtracting the old
anchor return. This is not a claim of negative energy or of all-order sign. -/
theorem nativeOut_second_source_eventually_nonzero :
    ∀ᶠ k : ℕ in atTop,
      nativeOut k 2 (Pi.single (1 : Fin 2) 1) ≠ 0 := by
  filter_upwards [nativeSampleQuotient_second_ne_first_eventually] with k hk
  intro hout
  have hcam : radialIncidentSynthesis k 2
      (quotientVariationCoefficient k (Pi.single (1 : Fin 2) 1)) =
        radialIncidentSynthesis k 2 0 := by
    calc
      _ = nativeOut k 2 (Pi.single (1 : Fin 2) 1) :=
        (nativeOut_eq_quotientVariation k 2 _).symm
      _ = 0 := hout
      _ = radialIncidentSynthesis k 2 0 := (map_zero _).symm
  have hcoeff : quotientVariationCoefficient k
      (Pi.single (1 : Fin 2) 1) = 0 :=
    (radialIncidentSynthesis_injective k 2) hcam
  have hpoint := congrArg (fun c : Fin 2 → ℂ => c 1) hcoeff
  simp only [quotientVariationCoefficient, Pi.single_eq_same, one_mul, Pi.zero_apply] at hpoint
  apply hk
  change completedNativeHermiteBiehlerChiralQuotient
    (canonicalCompletedC3RadialTiltPoint k 1) =
    completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k 0)
  exact sub_eq_zero.mp hpoint

end
end CarryWheelNativeSignedGate
