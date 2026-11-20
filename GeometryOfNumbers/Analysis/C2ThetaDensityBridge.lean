import Mathlib
import GeometryOfNumbers.Analysis.C2ThetaBezoutAlgebra

/-!
# Source-first interface for the C2 Mellin → theta → Bézout route

This file defines the actual nonnegative theta summand from the native
C2-derived theta representation and the coefficient moments entering the
all-order algebra.  Convergence/identity of the theta integral with the
completed native characteristic is explicitly **not** assumed to be proved.
The series and integrals below are raw definitions; the bridge to `F=A*N`
is a separate analytic theorem obligation.
-/

open scoped BigOperators
open MeasureTheory

namespace GeometryOfNumbers.Analysis

noncomputable section

/-- The n-th material term (n+1>=1) of the even theta density on y>=0. -/
def c2ThetaDensityTerm (n : ℕ) (y : ℝ) : ℝ :=
  2 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) *
    Real.exp (5 * y / 2) *
    (2 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * y) - 3) *
    Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * y))

/-- Every actual theta summand is positive on the nonnegative half-axis.
This is only a head/term sign, not the all-order Bezout sign. -/
theorem c2ThetaDensityTerm_pos (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 < c2ThetaDensityTerm n y := by
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hsq : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ 2) := by nlinarith
  have he : (1 : ℝ) ≤ Real.exp (2 * y) := by
    have h := Real.add_one_le_exp (2*y)
    linarith
  have hmul : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * y) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr he)]
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hfactor : 0 < 2 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2*y) - 3 := by
    have h := mul_nonneg (sub_nonneg.mpr hmul)
      (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
    nlinarith
  unfold c2ThetaDensityTerm
  positivity

/-- Every nonempty finite theta prefix has strictly positive density. -/
def c2ThetaDensityHead (K : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range K, c2ThetaDensityTerm n y

theorem c2ThetaDensityHead_pos {K : ℕ} (hK : 0 < K)
    {y : ℝ} (hy : 0 ≤ y) :
    0 < c2ThetaDensityHead K y := by
  unfold c2ThetaDensityHead
  apply Finset.sum_pos
  · intro n hn
    exact c2ThetaDensityTerm_pos n hy
  · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hK)

/-- Raw theta series. Summability is a further analytic obligation. -/
def c2ThetaDensity (y : ℝ) : ℝ :=
  ∑' n : ℕ, c2ThetaDensityTerm n y

/-- Positive-half-line raw even moments of the actual theta density. -/
def c2ThetaRawEvenMoment (j : ℕ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), y ^ (2*j) * c2ThetaDensity y

/-- Taylor coefficients in W(X) where W(z²)=F(1/2+iz) once the analytic
identity with the original completed C2 source has been established. -/
def c2ThetaRawW (j : ℕ) : ℝ :=
  (-1 : ℝ)^j * 2 * c2ThetaRawEvenMoment j /
    (Nat.factorial (2*j) : ℝ)

/-- Applying the proven finite algebra to the actual theta moment inputs. -/
theorem c2ThetaRawBezout_congruence (n shift : ℕ) (h : ℕ → ℝ) :
    c2ThetaBezoutConvolution n shift c2ThetaRawW h =
      c2ThetaToeplitz n c2ThetaRawW * c2ThetaHankel n shift h *
        (c2ThetaToeplitz n c2ThetaRawW).transpose :=
  c2ThetaBezoutConvolution_eq_congruence n shift c2ThetaRawW h

/-- The sign transport holds conditionally on the nonvanishing of the
actual theta raw integral and on a coefficient identification of H=-W'/W.
It does not claim the Hankel block to be positive. -/
theorem c2ThetaRawBezout_posDef_iff
    (n shift : ℕ) (h : ℕ → ℝ) (hw : c2ThetaRawW 0 ≠ 0) :
    (c2ThetaBezoutConvolution n shift c2ThetaRawW h).PosDef ↔
      (c2ThetaHankel n shift h).PosDef :=
  c2ThetaBezoutConvolution_posDef_iff n shift c2ThetaRawW h hw

/-- Exact low-degree Taylor readouts of the native theta moment formula. -/
@[simp] theorem c2ThetaRawW_zero :
    c2ThetaRawW 0 = 2 * c2ThetaRawEvenMoment 0 := by
  norm_num [c2ThetaRawW]

@[simp] theorem c2ThetaRawW_one :
    c2ThetaRawW 1 = -(c2ThetaRawEvenMoment 1) := by
  norm_num [c2ThetaRawW]
  ring

@[simp] theorem c2ThetaRawW_two :
    c2ThetaRawW 2 = c2ThetaRawEvenMoment 2 / 12 := by
  norm_num [c2ThetaRawW]
  ring

/-- Concrete first odd theta-Bézout entry.  Its sign requires a nontrivial
inequality between second and fourth raw moments of the theta density. -/
theorem c2ThetaRawBezout_odd_origin
    (h : ℕ → ℝ)
    (h0 : c2ThetaRawW 0 * h 0 = -c2ThetaRawW 1)
    (h1 : c2ThetaRawW 0 * h 1 + c2ThetaRawW 1 * h 0 =
      -(2 : ℝ) * c2ThetaRawW 2) :
    (c2ThetaBezoutConvolution 1 1 c2ThetaRawW h) 0 0 =
      (c2ThetaRawEvenMoment 1)^2 -
        (c2ThetaRawEvenMoment 0 * c2ThetaRawEvenMoment 2) / 3 := by
  rw [c2ThetaBezout_odd_origin c2ThetaRawW h h0 h1]
  simp only [c2ThetaRawW_zero, c2ThetaRawW_one, c2ThetaRawW_two]
  ring

end
end GeometryOfNumbers.Analysis

#print axioms GeometryOfNumbers.Analysis.c2ThetaDensityTerm_pos
#print axioms GeometryOfNumbers.Analysis.c2ThetaRawBezout_congruence
#print axioms GeometryOfNumbers.Analysis.c2ThetaRawBezout_odd_origin
