import NativeQuadraticSlopeSignatureSeparation
import NativeExactTailAllJetSignedMassGate

/-!
# The original complete C2 source after exact positive slope normalization

The logarithmic slope/height readout is not assumed positive. No spectral
zeros are supplied: nativeH is the original -F'/(2F) completed jet.
We extract ANY a > 0 as a quadratic scale to isolate the residual
signature, then transport the same original PSD obligation to the exact
signed theta/TFVD four-crossings via the previously proved source bridge.
-/

namespace CarryWheelNativeSignedGate

open CarrySourceBezout CarrySelfAdjointOperator XiThetaCosine
open scoped Matrix

noncomputable section

def nativeSlopeResidual (a : ℝ) (n : ℕ) : ℝ :=
  nativeH n / a ^ (n+1)

theorem nativeSlopeResidual_reconstruct (a : ℝ) (ha : 0 < a) :
    momentQuadraticScale a (nativeSlopeResidual a) = nativeH := by
  funext n
  simp only [momentQuadraticScale, nativeSlopeResidual]
  exact mul_div_cancel₀ _ (pow_ne_zero _ ha.ne')

theorem nativeSlopeResidual_matrix_posSemidef_iff (a : ℝ) (ha : 0 < a)
    (s N : ℕ) :
    (sourceMomentMatrix (nativeSlopeResidual a) s N).PosSemidef ↔
      (sourceMomentMatrix nativeH s N).PosSemidef := by
  conv_rhs => rw [← nativeSlopeResidual_reconstruct a ha]
  exact (momentQuadraticScale_posSemidef_iff a ha (nativeSlopeResidual a) s N).symm

/-- The all-order signed physical gate is UNAFFECTED by extracting
the positive reciprocal-square height scale from the original moments.
All four finite C2/Genuine/TFVD correlations are still present. -/
theorem nativeSlopeResidual_allPSD_iff_exactFourCrossings
    (a : ℝ) (ha : 0 < a) :
    (∀ b : Bool, ∀ N : ℕ,
      (sourceMomentMatrix (nativeSlopeResidual a)
          (if b then 1 else 0) N).PosSemidef) ↔
    ∀ (M P : ℕ) (b : Bool) (N : ℕ) (x : Fin N → ℝ),
      0 ≤ (nativeEveryJetExactFourTerms M P b N x).re := by
  rw [← nativeBothHankelTowers_allPSD_iff_allExactFourTerms_nonneg]
  exact forall₂_congr fun b N =>
    nativeSlopeResidual_matrix_posSemidef_iff a ha (if b then 1 else 0) N

/-- Equivalently: extracting the same quadratic scale does not prove
the needed positive mass domination. It is exactly the genuine original
signed theta mass balance (positive minus negative) with NO RH premise. -/
theorem nativeSlopeResidual_allPSD_iff_thetaMassDomination
    (a : ℝ) (ha : 0 < a) :
    (∀ b : Bool, ∀ N : ℕ,
      (sourceMomentMatrix (nativeSlopeResidual a)
          (if b then 1 else 0) N).PosSemidef) ↔
      ∀ (b : Bool) (N : ℕ) (x : Fin N → ℝ),
        nativeThetaNegativeMass
            (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) ≤
        nativeThetaPositiveMass
            (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) := by
  rw [← nativeBothHankelTowers_allPosSemidef_iff_exactThetaMassDominance]
  exact forall₂_congr fun b N =>
    nativeSlopeResidual_matrix_posSemidef_iff a ha (if b then 1 else 0) N

end
end CarryWheelNativeSignedGate
