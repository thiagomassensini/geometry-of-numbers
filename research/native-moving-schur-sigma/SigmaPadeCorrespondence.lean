import SigmaSignedPencil
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Exact pencil and Padé algebra for the original sigma jets

All coefficients below are read from `completedSigmaLogJet`.  The module
defines no moment sequence from zeros or from fitted spectral data.
-/

namespace CarrySigmaPade

open CarryMovingSigma CarrySigmaSource PowerSeries
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The determinant of the original window `G_s(d)`. -/
def sigmaPadeD (d : ℝ) (s : ℕ) : ℝ :=
  completedSigmaLogJet d s * completedSigmaLogJet d (s + 2) -
    (completedSigmaLogJet d (s + 1)) ^ 2

/-- The first mixed Hankel minor used by the pencil polynomial. -/
def sigmaPadeB (d : ℝ) (s : ℕ) : ℝ :=
  completedSigmaLogJet d s * completedSigmaLogJet d (s + 3) -
    completedSigmaLogJet d (s + 1) * completedSigmaLogJet d (s + 2)

/-- The shifted determinant of the original sigma window. -/
def sigmaPadeC (d : ℝ) (s : ℕ) : ℝ :=
  completedSigmaLogJet d (s + 1) * completedSigmaLogJet d (s + 3) -
    (completedSigmaLogJet d (s + 2)) ^ 2

/-- The normalized Padé coefficients, defined only when the original Gram
determinant is nonzero. -/
def sigmaPadeAlpha (d : ℝ) (s : ℕ) : ℝ :=
  sigmaPadeB d s / sigmaPadeD d s

def sigmaPadeBeta (d : ℝ) (s : ℕ) : ℝ :=
  sigmaPadeC d s / sigmaPadeD d s

/-- The original shifted sigma matrix is the Hankel matrix of the same jets. -/
theorem sigmaPencilGram_det (d : ℝ) (s : ℕ) :
    (sigmaPencilGram d s).det = sigmaPadeD d s := by
  simp [sigmaPencilGram, sigmaMatrix, CarrySelfAdjointOperator.sourceMomentMatrix,
    sigmaPadeD, Matrix.det_fin_two]
  ring

/-- Exact characteristic polynomial of the signed original pencil. -/
def sigmaPencilCharacteristic (d : ℝ) (s : ℕ) (lambda : ℝ) : ℝ :=
  (sigmaPencilShifted d s - lambda • sigmaPencilGram d s).det

theorem sigmaPencilCharacteristic_eq_quadratic (d : ℝ) (s : ℕ) (lambda : ℝ) :
    sigmaPencilCharacteristic d s lambda =
      sigmaPadeD d s * lambda ^ 2 - sigmaPadeB d s * lambda +
        sigmaPadeC d s := by
  simp [sigmaPencilCharacteristic, sigmaPencilShifted, sigmaPencilGram,
    sigmaMatrix, CarrySelfAdjointOperator.sourceMomentMatrix,
    sigmaPadeD, sigmaPadeB, sigmaPadeC, Matrix.det_fin_two]
  ring

/-- First Padé cancellation: the coefficient of order `s+2` in `q_s G_d`
vanishes exactly. -/
theorem sigmaPade_cancellation_succ_succ (d : ℝ) (s : ℕ)
    (hD : sigmaPadeD d s ≠ 0) :
    completedSigmaLogJet d (s + 2) -
        sigmaPadeAlpha d s * completedSigmaLogJet d (s + 1) +
        sigmaPadeBeta d s * completedSigmaLogJet d s = 0 := by
  unfold sigmaPadeAlpha sigmaPadeBeta sigmaPadeB sigmaPadeC sigmaPadeD at *
  have hD' : completedSigmaLogJet d (s + 2) * completedSigmaLogJet d s -
      (completedSigmaLogJet d (s + 1)) ^ 2 ≠ 0 := by
    intro hz
    apply hD
    calc
      completedSigmaLogJet d s * completedSigmaLogJet d (s + 2) -
          (completedSigmaLogJet d (s + 1)) ^ 2 =
        completedSigmaLogJet d (s + 2) * completedSigmaLogJet d s -
          (completedSigmaLogJet d (s + 1)) ^ 2 := by ring
      _ = 0 := hz
  field_simp [hD, hD']
  ring

/-- Second Padé cancellation: the coefficient of order `s+3` in `q_s G_d`
vanishes exactly. -/
theorem sigmaPade_cancellation_succ_succ_succ (d : ℝ) (s : ℕ)
    (hD : sigmaPadeD d s ≠ 0) :
    completedSigmaLogJet d (s + 3) -
        sigmaPadeAlpha d s * completedSigmaLogJet d (s + 2) +
        sigmaPadeBeta d s * completedSigmaLogJet d (s + 1) = 0 := by
  unfold sigmaPadeAlpha sigmaPadeBeta sigmaPadeB sigmaPadeC sigmaPadeD at *
  have hD' : completedSigmaLogJet d (s + 2) * completedSigmaLogJet d s -
      (completedSigmaLogJet d (s + 1)) ^ 2 ≠ 0 := by
    intro hz
    apply hD
    calc
      completedSigmaLogJet d s * completedSigmaLogJet d (s + 2) -
          (completedSigmaLogJet d (s + 1)) ^ 2 =
        completedSigmaLogJet d (s + 2) * completedSigmaLogJet d s -
          (completedSigmaLogJet d (s + 1)) ^ 2 := by ring
      _ = 0 := hz
  field_simp [hD, hD']
  ring

/-- The Padé denominator normalized at the origin. -/
def sigmaPadeDenominator (d : ℝ) (s : ℕ) (u : ℝ) : ℝ :=
  1 - sigmaPadeAlpha d s * u + sigmaPadeBeta d s * u ^ 2

/-- The actual original sigma logarithmic jets packaged as a formal power
series. -/
def sigmaOriginalMomentSeries (d : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (completedSigmaLogJet d)

/-- The quadratic Padé denominator as a formal power series. -/
def sigmaPadeDenominatorSeries (d : ℝ) (s : ℕ) : PowerSeries ℝ :=
  1 - PowerSeries.C (sigmaPadeAlpha d s) * PowerSeries.X +
    PowerSeries.C (sigmaPadeBeta d s) * PowerSeries.X ^ 2

/-- The numerator is the low-degree truncation of the product of the exact
quadratic denominator and the original moment series. -/
def sigmaPadeNumeratorSeries (d : ℝ) (s : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n =>
    if n ≤ s + 1 then
      PowerSeries.coeff n
        (sigmaPadeDenominatorSeries d s * sigmaOriginalMomentSeries d)
    else 0)

/-- Multiplication by the original quadratic denominator has the expected
three-term coefficient convolution at order `s+2`. -/
theorem sigmaPadeProductCoeff_succ_succ (d : ℝ) (s : ℕ) :
    PowerSeries.coeff (s + 2)
        (sigmaPadeDenominatorSeries d s * sigmaOriginalMomentSeries d) =
      completedSigmaLogJet d (s + 2) -
        sigmaPadeAlpha d s * completedSigmaLogJet d (s + 1) +
        sigmaPadeBeta d s * completedSigmaLogJet d s := by
  let f := sigmaOriginalMomentSeries d
  let alpha := sigmaPadeAlpha d s
  let beta := sigmaPadeBeta d s
  have hdecomp : sigmaPadeDenominatorSeries d s * f =
      f - PowerSeries.C alpha * (PowerSeries.X * f) +
        PowerSeries.C beta * (PowerSeries.X ^ 2 * f) := by
    dsimp [sigmaPadeDenominatorSeries]
    ring
  have hX2 : PowerSeries.X ^ 2 * f = PowerSeries.X * (PowerSeries.X * f) := by
    rw [pow_two]
    ac_rfl
  rw [hdecomp, hX2]
  simp only [map_add, map_sub]
  simp [f, alpha, beta, sigmaOriginalMomentSeries,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]

/-- The matching three-term convolution at order `s+3`. -/
theorem sigmaPadeProductCoeff_succ_succ_succ (d : ℝ) (s : ℕ) :
    PowerSeries.coeff (s + 3)
        (sigmaPadeDenominatorSeries d s * sigmaOriginalMomentSeries d) =
      completedSigmaLogJet d (s + 3) -
        sigmaPadeAlpha d s * completedSigmaLogJet d (s + 2) +
        sigmaPadeBeta d s * completedSigmaLogJet d (s + 1) := by
  let f := sigmaOriginalMomentSeries d
  let alpha := sigmaPadeAlpha d s
  let beta := sigmaPadeBeta d s
  have hdecomp : sigmaPadeDenominatorSeries d s * f =
      f - PowerSeries.C alpha * (PowerSeries.X * f) +
        PowerSeries.C beta * (PowerSeries.X ^ 2 * f) := by
    dsimp [sigmaPadeDenominatorSeries]
    ring
  have hX2 : PowerSeries.X ^ 2 * f = PowerSeries.X * (PowerSeries.X * f) := by
    rw [pow_two]
    ac_rfl
  rw [hdecomp, hX2]
  simp only [map_add, map_sub]
  simp [f, alpha, beta, sigmaOriginalMomentSeries,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]

/-- A coefficient definition of a normalized Padé approximant.  It records
the numerator and denominator degree bounds and the vanishing order of
`q*f-p`; no positivity or analytic continuation is part of this algebraic
notion. -/
def IsPadeApproximant (f p q : PowerSeries ℝ) (L M : ℕ) : Prop :=
  PowerSeries.coeff 0 q = 1 ∧
  (∀ n, M < n → PowerSeries.coeff n q = 0) ∧
  (∀ n, L < n → PowerSeries.coeff n p = 0) ∧
  (∀ n, n ≤ L + M → PowerSeries.coeff n (q * f - p) = 0)

theorem sigmaPadeDenominatorSeries_coeff_zero (d : ℝ) (s : ℕ) :
    PowerSeries.coeff 0 (sigmaPadeDenominatorSeries d s) = 1 := by
  simp [sigmaPadeDenominatorSeries]

theorem sigmaPadeDenominatorSeries_coeff_one (d : ℝ) (s : ℕ) :
    PowerSeries.coeff 1 (sigmaPadeDenominatorSeries d s) =
      -sigmaPadeAlpha d s := by
  simp [sigmaPadeDenominatorSeries]

theorem sigmaPadeDenominatorSeries_coeff_two (d : ℝ) (s : ℕ) :
    PowerSeries.coeff 2 (sigmaPadeDenominatorSeries d s) =
      sigmaPadeBeta d s := by
  simp [sigmaPadeDenominatorSeries]

theorem sigmaPadeDenominatorSeries_coeff_eq_zero_of_two_lt
    (d : ℝ) (s n : ℕ) (hn : 2 < n) :
    PowerSeries.coeff n (sigmaPadeDenominatorSeries d s) = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hconst : PowerSeries.coeff n (1 : PowerSeries ℝ) = 0 := by
    simp [hn0]
  have hX : PowerSeries.coeff n (PowerSeries.X : PowerSeries ℝ) = 0 := by
    rw [← pow_one (PowerSeries.X : PowerSeries ℝ), PowerSeries.coeff_X_pow]
    simp [hn1]
  have hX2 : PowerSeries.coeff n (PowerSeries.X ^ 2 : PowerSeries ℝ) = 0 := by
    simp [PowerSeries.coeff_X_pow, hn2]
  rw [sigmaPadeDenominatorSeries]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    hconst, hX, hX2, mul_zero]
  ring

private theorem sigmaPadeNumeratorSeries_coeff_eq_zero_of_large
    (d : ℝ) (s n : ℕ) (hn : s + 1 < n) :
    PowerSeries.coeff n (sigmaPadeNumeratorSeries d s) = 0 := by
  simp [sigmaPadeNumeratorSeries, not_le.mpr hn]

/-- The two exact convolution equations make the product of the normalized
denominator with the original jet series agree with a numerator of degree at
most `s+1` through order `s+3`.  This is precisely a coefficient-form
`[s+1/2]` Padé approximant of the original sigma generating series. -/
theorem sigmaOriginalMomentSeries_is_pade (d : ℝ) (s : ℕ)
    (hD : sigmaPadeD d s ≠ 0) :
    IsPadeApproximant (sigmaOriginalMomentSeries d)
      (sigmaPadeNumeratorSeries d s) (sigmaPadeDenominatorSeries d s)
      (s + 1) 2 := by
  refine ⟨sigmaPadeDenominatorSeries_coeff_zero d s, ?_, ?_, ?_⟩
  · intro n hn
    exact sigmaPadeDenominatorSeries_coeff_eq_zero_of_two_lt d s n hn
  · intro n hn
    exact sigmaPadeNumeratorSeries_coeff_eq_zero_of_large d s n hn
  · intro n hn
    by_cases hnL : n ≤ s + 1
    · simp [sigmaPadeNumeratorSeries, hnL]
    · have hcases : n = s + 2 ∨ n = s + 3 := by omega
      rcases hcases with h₂ | h₃
      · subst n
        calc
          PowerSeries.coeff (s + 2)
              (sigmaPadeDenominatorSeries d s * sigmaOriginalMomentSeries d -
                sigmaPadeNumeratorSeries d s) =
              PowerSeries.coeff (s + 2)
                  (sigmaPadeDenominatorSeries d s * sigmaOriginalMomentSeries d) -
                PowerSeries.coeff (s + 2) (sigmaPadeNumeratorSeries d s) := by simp
          _ = 0 := by
            rw [sigmaPadeProductCoeff_succ_succ,
              sigmaPade_cancellation_succ_succ d s hD]
            simp [sigmaPadeNumeratorSeries]
      · subst n
        calc
          PowerSeries.coeff (s + 3)
              (sigmaPadeDenominatorSeries d s * sigmaOriginalMomentSeries d -
                sigmaPadeNumeratorSeries d s) =
              PowerSeries.coeff (s + 3)
                  (sigmaPadeDenominatorSeries d s * sigmaOriginalMomentSeries d) -
                PowerSeries.coeff (s + 3) (sigmaPadeNumeratorSeries d s) := by simp
          _ = 0 := by
            rw [sigmaPadeProductCoeff_succ_succ_succ,
              sigmaPade_cancellation_succ_succ_succ d s hD]
            simp [sigmaPadeNumeratorSeries]

/-- Complexification of the same real sigma Gram window. -/
def sigmaPencilGramComplex (d : ℝ) (s : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (sigmaPencilGram d s i j : ℂ)

/-- Complexification of the next original sigma window. -/
def sigmaPencilShiftedComplex (d : ℝ) (s : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (sigmaPencilShifted d s i j : ℂ)

/-- The characteristic determinant for a complex generalized eigenvalue. -/
def sigmaPencilCharacteristicComplex (d : ℝ) (s : ℕ) (lambda : ℂ) : ℂ :=
  (sigmaPencilShiftedComplex d s - lambda • sigmaPencilGramComplex d s).det

/-- The real coefficient quadratic, now evaluated over the complex plane. -/
theorem sigmaPencilCharacteristicComplex_eq_quadratic
    (d : ℝ) (s : ℕ) (lambda : ℂ) :
    sigmaPencilCharacteristicComplex d s lambda =
      (sigmaPadeD d s : ℂ) * lambda ^ 2 -
        (sigmaPadeB d s : ℂ) * lambda + (sigmaPadeC d s : ℂ) := by
  simp [sigmaPencilCharacteristicComplex, sigmaPencilShiftedComplex,
    sigmaPencilGramComplex, sigmaPencilShifted, sigmaPencilGram,
    sigmaMatrix, CarrySelfAdjointOperator.sourceMomentMatrix,
    sigmaPadeD, sigmaPadeB, sigmaPadeC, Matrix.det_fin_two]
  ring

/-- The normalized Padé denominator evaluated over the complex plane. -/
def sigmaPadeDenominatorComplex (d : ℝ) (s : ℕ) (u : ℂ) : ℂ :=
  1 - (sigmaPadeAlpha d s : ℂ) * u +
    (sigmaPadeBeta d s : ℂ) * u ^ 2

/-- The exact pencil determinant is the reversed Padé denominator after
multiplication by `D_s * lambda^2`. -/
theorem sigmaPencilCharacteristicComplex_eq_reciprocal_pade
    (d : ℝ) (s : ℕ) (hD : sigmaPadeD d s ≠ 0)
    (lambda : ℂ) (hLambda : lambda ≠ 0) :
    sigmaPencilCharacteristicComplex d s lambda =
      (sigmaPadeD d s : ℂ) * lambda ^ 2 *
        sigmaPadeDenominatorComplex d s lambda⁻¹ := by
  rw [sigmaPencilCharacteristicComplex_eq_quadratic]
  have hDC : (sigmaPadeD d s : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hD
  unfold sigmaPadeDenominatorComplex sigmaPadeAlpha sigmaPadeBeta
  push_cast
  field_simp [hDC, hLambda]

/-- When the shifted determinant `C_s` is nonzero, every generalized pencil
root is nonzero and is exactly the reciprocal of a root of the normalized
Padé denominator.  The `C_s ≠ 0` condition excludes the projective root at
infinity (equivalently a zero pencil eigenvalue). -/
theorem sigmaPencil_root_iff_reciprocal_pade_root
    (d : ℝ) (s : ℕ)
    (hD : sigmaPadeD d s ≠ 0) (hC : sigmaPadeC d s ≠ 0)
    (lambda : ℂ) :
    sigmaPencilCharacteristicComplex d s lambda = 0 ↔
      lambda ≠ 0 ∧ sigmaPadeDenominatorComplex d s lambda⁻¹ = 0 := by
  constructor
  · intro hroot
    have hLambda : lambda ≠ 0 := by
      intro hz
      subst lambda
      have hroot' : (sigmaPadeC d s : ℂ) = 0 := by
        simpa [sigmaPencilCharacteristicComplex_eq_quadratic] using hroot
      exact (Complex.ofReal_ne_zero.mpr hC) hroot'
    refine ⟨hLambda, ?_⟩
    rw [sigmaPencilCharacteristicComplex_eq_reciprocal_pade d s hD lambda hLambda]
      at hroot
    have hscale : (sigmaPadeD d s : ℂ) * lambda ^ 2 ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hD) (pow_ne_zero 2 hLambda)
    exact (mul_eq_zero.mp hroot).resolve_left hscale
  · rintro ⟨hLambda, hpade⟩
    rw [sigmaPencilCharacteristicComplex_eq_reciprocal_pade d s hD lambda hLambda,
      hpade]
    simp

/-- Complete root classification under `D_s ≠ 0`, including the exceptional
zero pencil root.  That root occurs exactly when the Padé denominator drops
degree and has its remaining projective root at infinity. -/
theorem sigmaPencil_root_classification
    (d : ℝ) (s : ℕ) (hD : sigmaPadeD d s ≠ 0) (lambda : ℂ) :
    sigmaPencilCharacteristicComplex d s lambda = 0 ↔
      (lambda = 0 ∧ sigmaPadeC d s = 0) ∨
      (lambda ≠ 0 ∧ sigmaPadeDenominatorComplex d s lambda⁻¹ = 0) := by
  constructor
  · intro hroot
    by_cases hLambda : lambda = 0
    · left
      refine ⟨hLambda, ?_⟩
      subst lambda
      have hCcomplex : (sigmaPadeC d s : ℂ) = 0 := by
        simpa [sigmaPencilCharacteristicComplex_eq_quadratic] using hroot
      exact Complex.ofReal_injective hCcomplex
    · have hfactor :=
        sigmaPencilCharacteristicComplex_eq_reciprocal_pade d s hD lambda hLambda
      rw [hfactor] at hroot
      have hscale : (sigmaPadeD d s : ℂ) * lambda ^ 2 ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hD) (pow_ne_zero 2 hLambda)
      exact Or.inr ⟨hLambda, (mul_eq_zero.mp hroot).resolve_left hscale⟩
  · rintro (⟨hLambda, hC⟩ | ⟨hLambda, hPade⟩)
    · subst lambda
      rw [sigmaPencilCharacteristicComplex_eq_quadratic]
      simp [hC]
    · rw [sigmaPencilCharacteristicComplex_eq_reciprocal_pade
        d s hD lambda hLambda, hPade]
      simp

#print axioms sigmaPencilGram_det
#print axioms sigmaPencilCharacteristic_eq_quadratic
#print axioms sigmaPade_cancellation_succ_succ
#print axioms sigmaPade_cancellation_succ_succ_succ
#print axioms sigmaOriginalMomentSeries_is_pade
#print axioms sigmaPencilCharacteristicComplex_eq_quadratic
#print axioms sigmaPencilCharacteristicComplex_eq_reciprocal_pade
#print axioms sigmaPencil_root_iff_reciprocal_pade_root
#print axioms sigmaPencil_root_classification

end
end CarrySigmaPade
