import ResidualReturn
import CarrySelfAdjointOperator.CompletedNativeChiralPickFactorization
import Mathlib.Tactic

/-!
# Exact radial Schur complement of the original physical return

The formula holds for every radial sample and all cross terms, including
when the anchor deficit is zero. It uses the original carrier and quotient.
-/

namespace CarryCauchyResidual

open CarrySelfAdjointOperator CarryReturnDeflation CarryPositiveSquare
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

private theorem sourceReturn_zero (k : ℕ) : sourceReturn k 0 = oneReturn k := rfl

private theorem cauchy_sub_anchor (k i j : ℕ) :
    cauchy k i j * (((i : ℂ) / ((i : ℂ) + 2)) * ((j : ℂ) / ((j : ℂ) + 2)) - 1) =
      -(cauchy k i 0 * cauchy k 0 j / (anchorMass k : ℂ)) := by
  have hk : (k : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
  have hi : (i : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show (i : ℝ) + 2 ≠ 0 by positivity)
  have hj : (j : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show (j : ℝ) + 2 ≠ 0 by positivity)
  have hij : (i : ℂ) + (j : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show (i : ℝ) + (j : ℝ) + 2 ≠ 0 by positivity)
  simp only [cauchy, anchorMass, Nat.cast_zero, add_zero, zero_add,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast,
    Complex.ofReal_ofNat]
  field_simp [hk, hi, hj, hij]
  ring

theorem nativeRadialPick_apply (k N : ℕ) (i j : Fin N) :
    canonicalCompletedNativeRadialChiralPickSampleMatrix k N i j =
      cauchy k i j * (1 - conj (sourceReturn k i) * sourceReturn k j) := by
  change completedNativeHermiteBiehlerChiralPickKernel
    (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint k j) = _
  unfold completedNativeHermiteBiehlerChiralPickKernel
  rw [mul_div_right_comm, canonicalCompletedC3RadialTilt_I_div_separation]
  push_cast
  rw [cauchy]
  unfold sourceReturn
  ring

/-- Cross-multiplied identity for all slots of the physical residual.
The only denominator is the positive Cauchy mass of the original anchor. -/
theorem residual_basis_eq_scaled_pick_schur (k N : ℕ) (i j : Fin (N + 1)) :
    remainingPair k (N + 1) (Pi.single i 1) (Pi.single j 1) =
      (oneDeficit k : ℂ) * canonicalCompletedNativeRadialChiralPickSampleMatrix k (N + 1) i j -
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k (N + 1) i 0 *
        canonicalCompletedNativeRadialChiralPickSampleMatrix k (N + 1) 0 j) /
        (anchorMass k : ℂ) := by
  simp only [residual_basis_kernel, nativeRadialPick_apply, incidentCoefficient,
    returnedCoefficient, feedbackDenominator, map_div₀, map_mul, map_sub,
    map_add, map_natCast, map_ofNat, map_one, starRingEnd_self_apply,
    Fin.val_zero, sourceReturn_zero, ← native_deficit k, deficit]
  have hc := cauchy_sub_anchor k i j
  calc
    _ = (1 - conj (oneReturn k) * oneReturn k) *
          (cauchy k i j * (1 - conj (sourceReturn k i) * sourceReturn k j)) +
        (cauchy k i j *
          (((i : ℂ) / ((i : ℂ) + 2)) * ((j : ℂ) / ((j : ℂ) + 2)) - 1)) *
          ((1 - oneReturn k * conj (sourceReturn k i)) *
            (1 - conj (oneReturn k) * sourceReturn k j)) := by ring
    _ = _ := by rw [hc]; ring

theorem nativeRadialPick_anchor (k N : ℕ) :
    canonicalCompletedNativeRadialChiralPickSampleMatrix k (N + 1) 0 0 =
      (anchorMass k : ℂ) * (oneDeficit k : ℂ) := by
  rw [nativeRadialPick_apply]
  simp only [Fin.val_zero, sourceReturn_zero, ← native_deficit k, deficit]
  congr 1
  simp only [anchorMass, cauchy, Nat.cast_zero, zero_add,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast,
    Complex.ofReal_ofNat]

/-- Equivalence with the ordinary first Pick Schur entry when the anchor
deficit is nonzero. Every later pivot of the tail inherits the same scale. -/
theorem residual_basis_eq_pick_schur (k N : ℕ) (i j : Fin (N + 1))
    (hd : oneDeficit k ≠ 0) :
    remainingPair k (N + 1) (Pi.single i 1) (Pi.single j 1) =
      (oneDeficit k : ℂ) *
        (canonicalCompletedNativeRadialChiralPickSampleMatrix k (N + 1) i j -
        (canonicalCompletedNativeRadialChiralPickSampleMatrix k (N + 1) i 0 *
          canonicalCompletedNativeRadialChiralPickSampleMatrix k (N + 1) 0 j) /
          canonicalCompletedNativeRadialChiralPickSampleMatrix k (N + 1) 0 0) := by
  have hd' : (oneDeficit k : ℂ) ≠ 0 := by exact_mod_cast hd
  have hm : (anchorMass k : ℂ) ≠ 0 := by exact_mod_cast (anchorMass_pos k).ne'
  rw [residual_basis_eq_scaled_pick_schur, nativeRadialPick_anchor]
  field_simp [hm, hd']

/-- The scalar polarized kernel of an odd radial germ. -/
def radialResponseKernel (f : ℂ → ℂ) (x y : ℂ) : ℂ :=
  (f x + f y) / (x + y)

/-- Reciprocal reduction at the zero with slope `a`. For an odd analytic
germ with nonzero slope, the apparent singularity at zero is removable. -/
def radialReciprocalReduction (f : ℂ → ℂ) (a x : ℂ) : ℂ :=
  1 / f x - 1 / (a * x)

/-- One exact center Schur step in the radial response. When `a = f'(0)`,
the subtracted term is the outer product of the center crossings. -/
theorem radialResponseKernel_centered_schur (f : ℂ → ℂ) (a x y : ℂ)
    (ha : a ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (hfx : f x ≠ 0) (hfy : f y ≠ 0) :
    radialResponseKernel f x y - (f x / x) * (f y / y) / a =
      f x * f y * radialResponseKernel (radialReciprocalReduction f a) x y := by
  unfold radialResponseKernel radialReciprocalReduction
  field_simp
  ring

/-- Cancellation of the gauge term in the fifth coefficient once the
first surviving direction is eliminated with its actual crossing. -/
theorem fifthCoefficient_sub_crossing (h₀ h₁ h₂ : ℝ) :
    128 * (h₀ * h₂ - h₁ ^ 2 + 4 * h₀ ^ 3 * h₁) -
      (128 * h₀ ^ 2 * h₁) ^ 2 / (32 * h₀ * h₁) =
    128 * (h₀ * h₂ - h₁ ^ 2) := by
  by_cases h₀z : h₀ = 0
  · simp [h₀z]
  by_cases h₁z : h₁ = 0
  · simp [h₁z]
  field_simp
  ring

#print axioms radialResponseKernel_centered_schur
#print axioms fifthCoefficient_sub_crossing

#print axioms residual_basis_eq_scaled_pick_schur
#print axioms residual_basis_eq_pick_schur

end
end CarryCauchyResidual
