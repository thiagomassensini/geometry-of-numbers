import AllOrderTfvdHeadMarginBootstrap
import CarrySelfAdjointOperator.NativeSourceSchurThetaMasses
import CarrySelfAdjointOperator.NativeSourceThetaGreenTransport

/-!
# Exact native Schur pivot as ALL FOUR original completed TFVD crossings
# and as the original theta positive-minus-negative mass balance.

This is the actual original source:
   bracket -> Genuine -> N -> F=A*N -> -F'/(2F) -> Hankel/Schur.

The head+tail source is EXACT at every finite pair of cutoffs M,P,
not an approximation. The mixed/source Bezout kernel is BILINEAR, not
an automatically positive Gram. This module therefore does not assume
or claim the missing positive mass domination.

No RH, no zeros, no inserted positive measure.
-/

namespace CarryWheelNativeSignedGate

open CarrySourceBezout CarrySelfAdjointOperator XiThetaCosine
open scoped BigOperators Matrix

noncomputable section

/-- The actual ordered HT+TH+TT corrections on the ORIGINAL critical
Schur vector, with two independent source cutoffs. -/
def nativeCriticalExactCrossings
    (M P : ℕ) (b : Bool) (n : ℕ) : ℂ :=
  literalResidualTerm M P true false b n +
  literalResidualTerm M P false true b n +
  literalResidualTerm M P false false b n

/-- The FULL actual original completed critical TFVD quadratic
form, preserving all four ordered interactions. -/
def nativeCriticalExactFourTerms
    (M P : ℕ) (b : Bool) (n : ℕ) : ℂ :=
  literalResidualTerm M P true true b n +
    nativeCriticalExactCrossings M P b n

theorem nativeCriticalExactFourTerms_eq_nativeSchurRemainder
    (M P : ℕ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    nativeCriticalExactFourTerms M P b n =
      (nativeC 0 * nativeSourceSchurRemainder (if b then 1 else 0) n : ℝ) := by
  simpa only [nativeCriticalExactFourTerms, nativeCriticalExactCrossings, add_assoc]
    using native_residual_literal_four_terms M P b n hA

/-- Source-first: no tail estimate and no limit. The original exact
four-term sum is INDEPENDENT of both TFVD cutoffs. -/
theorem nativeCriticalExactFourTerms_cutoff_invariant
    (M P M' P' : ℕ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    nativeCriticalExactFourTerms M P b n =
      nativeCriticalExactFourTerms M' P' b n := by
  rw [nativeCriticalExactFourTerms_eq_nativeSchurRemainder M P b n hA,
    nativeCriticalExactFourTerms_eq_nativeSchurRemainder M' P' b n hA]

/-- Exact conservation law for changing the head cutoff:
any variation of HH is canceled PRECISELY by the variations of the three
other correlations, even if the individual terms are large or signed. -/
theorem nativeCriticalExactCrossings_compensate_head_change
    (M P M' P' : ℕ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    literalResidualTerm M P true true b n -
      literalResidualTerm M' P' true true b n =
    nativeCriticalExactCrossings M' P' b n -
      nativeCriticalExactCrossings M P b n := by
  have h := nativeCriticalExactFourTerms_cutoff_invariant M P M' P' b n hA
  unfold nativeCriticalExactFourTerms at h
  -- The two exact decompositions have the same full source.
  exact (sub_eq_sub_iff_add_eq_add).2 (by linear_combination h)

theorem nativeCriticalExactFourTerms_eq_thetaMassDifference
    (M P : ℕ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    nativeCriticalExactFourTerms M P b n =
      ((nativeC 0 *
        (nativeThetaPositiveMass (nativeSchurThetaPolynomial
            (if b then 1 else 0) n) -
         nativeThetaNegativeMass (nativeSchurThetaPolynomial
            (if b then 1 else 0) n))) : ℝ) := by
  rw [nativeCriticalExactFourTerms_eq_nativeSchurRemainder M P b n hA,
    nativeSourceSchurRemainder_eq_thetaMasses]

/-- The same exact completed TFVD four-term residual equals the
original full theta-Green flux integral in the actual Schur direction.
Neither integrand nor individual ordered cross is assumed nonnegative. -/
theorem nativeCriticalExactFourTerms_eq_thetaGreenIntegral
    (M P : ℕ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    nativeCriticalExactFourTerms M P b n =
      ((nativeC 0 *
        ∫ u in Set.Ioi (0 : ℝ),
          (nativeThetaGreenPolynomial
            (nativeSchurThetaPolynomial (if b then 1 else 0) n)).eval u *
          thetaTail u) : ℝ) := by
  rw [nativeCriticalExactFourTerms_eq_nativeSchurRemainder M P b n hA,
    nativeSourceSchurRemainder_eq_thetaGreen_integral]

/-- Quantitative sign FRONTIER, with no assumptions of positivity from RH.
The exact C2/TFVD critical residual is positive if and only if the
COMPLETED theta positive mass dominates its strictly retained negative
mass. This equivalence does NOT prove that domination. -/
theorem nativeCriticalExactFourTerms_pos_iff_thetaMassDominance
    (M P : ℕ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    0 < (nativeCriticalExactFourTerms M P b n).re ↔
      nativeThetaNegativeMass
        (nativeSchurThetaPolynomial (if b then 1 else 0) n) <
      nativeThetaPositiveMass
        (nativeSchurThetaPolynomial (if b then 1 else 0) n) := by
  rw [nativeCriticalExactFourTerms_eq_thetaMassDifference M P b n hA]
  simp only [Complex.ofReal_re]
  rw [mul_pos_iff_of_pos_left nativeC0_pos_geometric]
  exact sub_pos

/-- There really is negative theta mass in each original ODD Schur
sector: the conservation identity does not make the underlying source
pointwise nonnegative or annihilate the return channel. -/
theorem nativeCritical_odd_negative_theta_mass_nonzero (n : ℕ) :
    0 < nativeThetaNegativeMass (nativeSchurThetaPolynomial 1 n) :=
  nativeSchurThetaPolynomial_odd_negativeMass_pos n

end
end CarryWheelNativeSignedGate
