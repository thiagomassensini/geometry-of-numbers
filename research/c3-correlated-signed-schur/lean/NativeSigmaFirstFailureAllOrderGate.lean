import TransverseSignThresholdCenterClosure
import SigmaNeighborhood
import NativeExactTailAllJetSignedMassGate

/-!
# The ORIGINAL displaced sigma log-derivative moments and the
# exact logical threshold -> center PSD bridge (without RH).

We reuse the already-proved native identity:
  sigmaMatrix 0 s N = sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s N
and continuousAt sigmaMatrix at d=0 for EVERY fixed finite N.

The single sign premise below states the real threshold-divergence:
for each arbitrary N and sector, sufficiently close nonzero d have
NO negative vector in that WHOLE N-dimensional matrix.

The first negative SHIFTED 2x2 WINDOW moving to infinity is
not this premise. We have not proven the premise from C2 or TFVD.
-/

namespace CarryWheelNativeSignedGate

open CarryMovingSigma CarrySelfAdjointOperator
open scoped Matrix

noncomputable section

/-- No negative ORIGINAL full Hankel prefix of any preassigned size
in a sufficiently small punctured transverse neighborhood.
This is the exact "the first negative DIMENSION goes to infinity"
gate; it is *not* currently proved for the native source. -/
def SigmaNativeFullFailureDimensionEscapes : Prop :=
  ∀ (b : Bool) (N : ℕ), ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ,
    0 < |d| → |d| < δ →
      (sigmaMatrix d (if b then 1 else 0) N).PosSemidef

/-- An all-order center nonnegativity theorem, independent of RH,
deduced from the authentic sigma-continuity of the C2 completed jets.
The only open premise is the full-first-negative-dimension escape. -/
theorem sigma_native_all_center_Hankel_posSemidef_of_failure_escape
    (hEscape : SigmaNativeFullFailureDimensionEscapes) :
    ∀ (b : Bool) (N : ℕ),
      (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
        (if b then 1 else 0) N).PosSemidef := by
  intro b N
  let s : ℕ := if b then 1 else 0
  have hSymm : (sigmaMatrix 0 s N).IsSymm :=
    sigma_matrix_symm 0 s N
  have hHerm : (sigmaMatrix 0 s N).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr hSymm
  have hcenter : (sigmaMatrix 0 s N).PosSemidef :=
    center_matrix_posSemidef_of_punctured_posSemidef
      N (fun d => sigmaMatrix d s N)
      (sigma_matrix_continuous_center s N)
      hHerm (hEscape b N)
  simpa only [sigma_matrix_center] using hcenter


/-- This is WHERE the transverse first-failure law would feed the EXACT
C2/TFVD four-crossing identity. It gives full nonnegative source energy
for every finite jet, every parity, every arbitrary pair of cutoffs,
but is conditional on the STILL OPEN divergence of the FIRST FULL
NEGATIVE HANKEL DIMENSION. -/
theorem sigma_failure_escape_implies_exact_allJet_tfvd_nonnegative
    (hEscape : SigmaNativeFullFailureDimensionEscapes) :
    ∀ (M P : ℕ) (b : Bool) (N : ℕ) (x : Fin N → ℝ),
      0 ≤ (nativeEveryJetExactFourTerms M P b N x).re := by
  apply (nativeBothHankelTowers_allPSD_iff_allExactFourTerms_nonneg).mp
  exact sigma_native_all_center_Hankel_posSemidef_of_failure_escape hEscape

/-- The same gate reads as positive source theta mass at least negative
source theta mass for EVERY ORIGINAL completed jet polynomial. -/
theorem sigma_failure_escape_implies_allJet_theta_mass_dominance
    (hEscape : SigmaNativeFullFailureDimensionEscapes) :
    ∀ (b : Bool) (N : ℕ) (x : Fin N → ℝ),
      nativeThetaNegativeMass
        (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) ≤
      nativeThetaPositiveMass
        (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) := by
  apply (nativeBothHankelTowers_allPosSemidef_iff_exactThetaMassDominance).mp
  exact sigma_native_all_center_Hankel_posSemidef_of_failure_escape hEscape

end
end CarryWheelNativeSignedGate
