import NativeExactTailSchurThetaGreenConservation
import NativeMixedU

/-!
# Unconditional exact 4-term TFVD + theta-Green conservation FOR ALL FINITE JETS.

This is stronger in quantifier scope than the critical-Schur-only crosswalk:
it does NOT require the old prefix to be invertible or positive.
It preserves both cutoffs, all mixed crossing terms, and the original
source Cauchy lift of every finite real vector x.

No RH, spectral zeros, positivity, or approximation is assumed.
-/

namespace CarryWheelNativeSignedGate

open CarrySourceBezout CarrySelfAdjointOperator XiThetaCosine
open scoped BigOperators Matrix

noncomputable section

/-- Every vector in any original completed-native Hankel section is
canonically lifted into the original division-free TFVD/Bézout source
coordinates. The full signed quadratic contains all FOUR crossed terms. -/
def nativeEveryJetExactFourTerms
    (M P : ℕ) (b : Bool) (N : ℕ) (x : Fin N → ℝ) : ℂ :=
  literalTerm M P true true b N
      (mixedSourceLift N x) (mixedSourceLift N x) +
  literalTerm M P true false b N
      (mixedSourceLift N x) (mixedSourceLift N x) +
  literalTerm M P false true b N
      (mixedSourceLift N x) (mixedSourceLift N x) +
  literalTerm M P false false b N
      (mixedSourceLift N x) (mixedSourceLift N x)

/-- Full EXACT original four-term source quadratic equals the canonical
completed log-derivative Hankel quadratic for any finite N and any x,
without positive/invertible old prefix or cutoff limit. -/
theorem nativeEveryJetExactFourTerms_eq_canonicalMomentQuadratic
    (M P : ℕ) (b : Bool) (N : ℕ) (x : Fin N → ℝ) :
    nativeEveryJetExactFourTerms M P b N x =
      (sourceMomentQuadratic nativeH (if b then 1 else 0) N x : ℝ) := by
  have h := native_mixed_tfvd_four_terms M P b N x x
  simpa only [nativeEveryJetExactFourTerms, sourceMomentQuadratic,
    matrixPair, Pi.star_apply, star_trivial] using h.symm

/-- The source's fully signed Taylor-jet quadratic is exactly the
theta-Green integral of the ORIGINAL polynomial transform, in any
dimension and for every x. In particular none of the four pieces
is required to be positive. -/
theorem nativeEveryJetExactFourTerms_re_eq_thetaGreenIntegral
    (M P : ℕ) (b : Bool) (N : ℕ) (x : Fin N → ℝ) :
    (nativeEveryJetExactFourTerms M P b N x).re =
      ∫ u in Set.Ioi (0 : ℝ),
        (nativeThetaGreenPolynomial
          (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x)).eval u *
        thetaTail u := by
  rw [nativeEveryJetExactFourTerms_eq_canonicalMomentQuadratic,
    Complex.ofReal_re]
  exact nativeSourceMomentQuadratic_eq_thetaGreen_integral
    (if b then 1 else 0) N x

/-- Exact canonical all-jet source energy has a positive and a
NEGATIVE theta mass (the completed source itself, not a chosen
zero-supported measure). This is an identity, not a sign assertion. -/
theorem nativeEveryJetExactFourTerms_re_eq_thetaMassDifference
    (M P : ℕ) (b : Bool) (N : ℕ) (x : Fin N → ℝ) :
    (nativeEveryJetExactFourTerms M P b N x).re =
      nativeThetaPositiveMass
          (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) -
      nativeThetaNegativeMass
          (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) := by
  rw [nativeEveryJetExactFourTerms_eq_canonicalMomentQuadratic,
    Complex.ofReal_re,
    ← nativeThetaQuadraticPolynomial_integral (if b then 1 else 0) N x]
  exact nativeXiPolynomialIntegral_eq_masses
    (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x)

/-- EXACT all-order nonnegative-energy target stated as a
source-mass comparison. We have not proved the comparison. -/
theorem nativeEveryJetExactFourTerms_nonneg_iff_thetaMassDominance
    (M P : ℕ) (b : Bool) (N : ℕ) (x : Fin N → ℝ) :
    0 ≤ (nativeEveryJetExactFourTerms M P b N x).re ↔
      nativeThetaNegativeMass
          (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) ≤
      nativeThetaPositiveMass
          (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) := by
  rw [nativeEveryJetExactFourTerms_re_eq_thetaMassDifference]
  exact sub_nonneg

/-- For every finite N, the native Hankel PosSemidef statement is
EQUIVALENT to the original, completed, all-jets signed theta mass
domination. This is the precise ALL-ORDER geometry-first SIGN GATE,
not a claim that the gate has yet been discharged. -/
theorem nativeHankel_posSemidef_iff_allExactThetaMassDominance
    (b : Bool) (N : ℕ) :
    (sourceMomentMatrix nativeH (if b then 1 else 0) N).PosSemidef ↔
      ∀ x : Fin N → ℝ,
        nativeThetaNegativeMass
            (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) ≤
        nativeThetaPositiveMass
            (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h x
    have hx := h.2 x
    have hx' : 0 ≤ (nativeEveryJetExactFourTerms 0 0 b N x).re := by
      rw [nativeEveryJetExactFourTerms_eq_canonicalMomentQuadratic,
        Complex.ofReal_re]
      simpa only [sourceMomentQuadratic] using hx
    exact
      (nativeEveryJetExactFourTerms_nonneg_iff_thetaMassDominance
        0 0 b N x).mp hx'
  · intro hall
    refine ⟨sourceMomentMatrix_isHermitian nativeH (if b then 1 else 0) N, ?_⟩
    intro x
    have h := (nativeEveryJetExactFourTerms_nonneg_iff_thetaMassDominance
      0 0 b N x).mpr (hall x)
    rw [nativeEveryJetExactFourTerms_eq_canonicalMomentQuadratic,
      Complex.ofReal_re] at h
    simpa only [sourceMomentQuadratic] using h

/-- The complete all-order PSD obligation for the TWO ORIGINAL
completed-native Hankel towers is exactly the all-jets positive-minus-
negative theta mass domination. This statement does not assert the
domination or invoke any hypothesis on the zeros of F. -/
theorem nativeBothHankelTowers_allPosSemidef_iff_exactThetaMassDominance :
    (∀ (b : Bool) (N : ℕ),
        (sourceMomentMatrix nativeH (if b then 1 else 0) N).PosSemidef) ↔
      ∀ (b : Bool) (N : ℕ) (x : Fin N → ℝ),
        nativeThetaNegativeMass
            (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) ≤
        nativeThetaPositiveMass
            (nativeThetaQuadraticPolynomial (if b then 1 else 0) N x) := by
  constructor
  · intro h b N x
    exact
      (nativeHankel_posSemidef_iff_allExactThetaMassDominance b N).mp (h b N) x
  · intro h b N
    exact
      (nativeHankel_posSemidef_iff_allExactThetaMassDominance b N).mpr (h b N)

/-- The full exact-source ALL-ORDER sign law. The completed
native two-tower PSD target is EQUIVALENT to nonnegativity of the
entire physical four-term TFVD/Bézout form for every dimension and
test vector, at every arbitrary pair of source cutoffs M,P.
No tail approximation, sign assumption, RH, or chosen spectral measure.

This is an exact equivalence, NOT a proof of its right hand side. -/
theorem nativeBothHankelTowers_allPSD_iff_allExactFourTerms_nonneg :
    (∀ (b : Bool) (N : ℕ),
        (sourceMomentMatrix nativeH (if b then 1 else 0) N).PosSemidef) ↔
      ∀ (M P : ℕ) (b : Bool) (N : ℕ) (x : Fin N → ℝ),
        0 ≤ (nativeEveryJetExactFourTerms M P b N x).re := by
  constructor
  · intro h M P b N x
    have hm :=
      (nativeHankel_posSemidef_iff_allExactThetaMassDominance b N).mp (h b N) x
    exact
      (nativeEveryJetExactFourTerms_nonneg_iff_thetaMassDominance
        M P b N x).mpr hm
  · intro h b N
    apply (nativeHankel_posSemidef_iff_allExactThetaMassDominance b N).mpr
    intro x
    exact
      (nativeEveryJetExactFourTerms_nonneg_iff_thetaMassDominance
        0 0 b N x).mp (h 0 0 b N x)

/-- The entire head/tail decomposition remains exact when switching
material cutoffs on arbitrary source vectors, without any old Schur
inverse; any cutoff-dependent change is an internal redistribution. -/
theorem nativeEveryJetExactFourTerms_cutoff_invariant
    (M P M' P' : ℕ) (b : Bool) (N : ℕ) (x : Fin N → ℝ) :
    nativeEveryJetExactFourTerms M P b N x =
      nativeEveryJetExactFourTerms M' P' b N x := by
  rw [nativeEveryJetExactFourTerms_eq_canonicalMomentQuadratic,
    nativeEveryJetExactFourTerms_eq_canonicalMomentQuadratic]

end
end CarryWheelNativeSignedGate
