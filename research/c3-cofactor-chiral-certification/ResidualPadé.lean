import GeneralCofactorIdentity
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Division-free residual identity for Hankel cofactors

For an arbitrary real moment sequence, the fixed-length reversal of the
cofactor vector produces the first Hankel defect, even when the prefix is
singular.  The second section transports the identity through a formal
logarithmic-derivative recurrence without dividing by the prefix determinant.
-/

namespace C3ResidualPade

open scoped BigOperators Matrix
open Polynomial

noncomputable section
set_option autoImplicit false

def hankelPrefix (h : ℕ → ℝ) (s n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => h (s + i.val + j.val)

def hankelBorder (h : ℕ → ℝ) (s n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => h (s + i.val + j.val)

def hankelCoupling (h : ℕ → ℝ) (s n : ℕ) : Fin n → ℝ :=
  fun i => h (s + n + i.val)

def cofactor (h : ℕ → ℝ) (s n : ℕ) : Fin (n + 1) → ℝ :=
  C3GeneralCofactor.cofactorVector (hankelPrefix h s n) (hankelCoupling h s n)

def shiftedMoments (h : ℕ → ℝ) (s : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun j => h (s + j))

def cofactorReversedPolynomial (h : ℕ → ℝ) (s n : ℕ) : Polynomial ℝ :=
  ∑ j : Fin (n + 1), Polynomial.monomial (n - j.val) (cofactor h s n j)

/-- The reversal is taken over all n+1 cofactors, regardless of the degree
that the resulting polynomial happens to have. -/
def cofactorReversed (h : ℕ → ℝ) (s n : ℕ) : PowerSeries ℝ :=
  ∑ j : Fin (n + 1), PowerSeries.C (cofactor h s n j) *
    PowerSeries.X ^ (n - j.val)

theorem cofactorReversed_eq_fixedPolynomial (h : ℕ → ℝ) (s n : ℕ) :
    cofactorReversed h s n = (cofactorReversedPolynomial h s n : PowerSeries ℝ) := by
  ext k
  simp [cofactorReversed, cofactorReversedPolynomial, Polynomial.coeff_monomial, eq_comm]

def cofactorNumerator (h : ℕ → ℝ) (s n : ℕ) : PowerSeries ℝ :=
  (PowerSeries.trunc n (cofactorReversed h s n * shiftedMoments h s) : Polynomial ℝ)

theorem cofactorReversed_coeff_zero (h : ℕ → ℝ) (s n : ℕ) :
    PowerSeries.coeff 0 (cofactorReversed h s n) = (hankelPrefix h s n).det := by
  simp only [cofactorReversed, map_sum, PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp [cofactor, C3GeneralCofactor.cofactorVector]
  · intro j hj hne
    have hlast : j.val ≠ n := by
      intro he
      exact hne (Fin.ext he)
    have hjlt : j.val < n := by omega
    have hcond : 0 ≠ n - j.val := by omega
    simp [hcond]
  · simp

def hankelDefect (h : ℕ → ℝ) (s n : ℕ) : ℝ :=
  (hankelBorder h s n).det

def hankelPivot (h : ℕ → ℝ) (s n : ℕ) : ℝ :=
  h (s + 2*n) - dotProduct (hankelCoupling h s n)
    ((hankelPrefix h s n)⁻¹ *ᵥ hankelCoupling h s n)

theorem hankelBorder_eq_cofactorBorder (h : ℕ → ℝ) (s n : ℕ) :
    hankelBorder h s n =
      C3GeneralCofactor.border (hankelPrefix h s n) (hankelCoupling h s n)
        (h (s + 2*n)) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [hankelBorder, C3GeneralCofactor.border, hankelPrefix, hankelCoupling]
      congr 1
      omega
    · simp [hankelBorder, C3GeneralCofactor.border, hankelPrefix, hankelCoupling]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [hankelBorder, C3GeneralCofactor.border, hankelPrefix, hankelCoupling]
      congr 1
      omega
    · simp [hankelBorder, C3GeneralCofactor.border, hankelPrefix, hankelCoupling]

theorem hankelBorder_mulVec_cofactor (h : ℕ → ℝ) (s n : ℕ) :
    (hankelBorder h s n).mulVec (cofactor h s n) =
      C3GeneralCofactor.lastScalarVector (hankelDefect h s n) := by
  rw [hankelBorder_eq_cofactorBorder]
  rw [hankelDefect, hankelBorder_eq_cofactorBorder, cofactor]
  exact C3GeneralCofactor.border_mulVec_cofactor (hankelPrefix h s n)
    (hankelCoupling h s n) (h (s + 2*n))

theorem hankelDefect_eq_det_mul_pivot (h : ℕ → ℝ) (s n : ℕ)
    (hτ : (hankelPrefix h s n).det ≠ 0) :
    hankelDefect h s n = (hankelPrefix h s n).det * hankelPivot h s n := by
  let A := hankelPrefix h s n
  let b := hankelCoupling h s n
  let d := h (s + 2*n)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hτ
  have hcr := Matrix.det_smul_inv_mulVec_eq_cramer A b hunit
  rw [Matrix.cramer_eq_adjugate_mulVec] at hcr
  have hdot : dotProduct b (A.det • (A⁻¹ *ᵥ b)) =
      A.det * dotProduct b (A⁻¹ *ᵥ b) := by
    unfold dotProduct
    calc
      (∑ i, b i * (A.det • (A⁻¹ *ᵥ b)) i) =
          ∑ i, A.det * (b i * (A⁻¹ *ᵥ b) i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
      _ = A.det * ∑ i, b i * (A⁻¹ *ᵥ b) i := by rw [Finset.mul_sum]
  calc
    hankelDefect h s n =
        (C3GeneralCofactor.border A b d).det := by
          rw [hankelDefect, hankelBorder_eq_cofactorBorder]
    _ = A.det * d - dotProduct b (A.adjugate.mulVec b) := by
          rw [C3GeneralCofactor.border_det]
          rfl
    _ = A.det * (d - dotProduct b (A⁻¹ *ᵥ b)) := by
          rw [← hcr, hdot]
          ring
    _ = (hankelPrefix h s n).det * hankelPivot h s n := by
          simp [hankelPivot, A, b, d]

theorem cofactorReversed_mul_shiftedMoments_coeff (h : ℕ → ℝ) (s n r : ℕ) :
    PowerSeries.coeff (n + r) (cofactorReversed h s n * shiftedMoments h s) =
      ∑ j : Fin (n + 1), cofactor h s n j * h (s + r + j.val) := by
  rw [cofactorReversed]
  rw [Finset.sum_mul]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [shiftedMoments, PowerSeries.coeff_mk]
  have hjn : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  have hdecomp : n - j.val + j.val = n := Nat.sub_add_cancel hjn
  have hle : n - j.val ≤ n + r := by omega
  rw [if_pos hle]
  have hidx : n + r - (n - j.val) = r + j.val := calc
    n + r - (n - j.val) = (n - j.val + j.val) + r - (n - j.val) :=
      congrArg (fun a : ℕ => a + r - (n - j.val)) hdecomp.symm
    _ = (n - j.val) + (j.val + r) - (n - j.val) := by rw [Nat.add_assoc]
    _ = j.val + r := Nat.add_sub_cancel_left _ _
    _ = r + j.val := Nat.add_comm _ _
  simpa [Nat.add_assoc] using
    congrArg (fun x : ℕ => cofactor h s n j * h (s + x)) hidx

theorem cofactorReversed_mul_shiftedMoments_eq_row (h : ℕ → ℝ) (s n : ℕ)
    (r : Fin (n + 1)) :
    PowerSeries.coeff (n + r.val) (cofactorReversed h s n * shiftedMoments h s) =
      ((hankelBorder h s n).mulVec (cofactor h s n)) r := by
  rw [cofactorReversed_mul_shiftedMoments_coeff]
  change (∑ j : Fin (n + 1), cofactor h s n j * h (s + r.val + j.val)) =
    ∑ j : Fin (n + 1), hankelBorder h s n r j * cofactor h s n j
  apply Finset.sum_congr rfl
  intro j hj
  simp [hankelBorder]
  ring

theorem cofactorReversed_mul_shiftedMoments_eq_lastScalar (h : ℕ → ℝ) (s n : ℕ)
    (r : Fin (n + 1)) :
    PowerSeries.coeff (n + r.val) (cofactorReversed h s n * shiftedMoments h s) =
      C3GeneralCofactor.lastScalarVector (hankelDefect h s n) r := by
  rw [cofactorReversed_mul_shiftedMoments_eq_row, hankelBorder_mulVec_cofactor]

theorem cofactorDefect_coeff_from_n (h : ℕ → ℝ) (s n r : ℕ) (hr : r ≤ n) :
    PowerSeries.coeff (n + r)
        (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n) =
      if r < n then 0 else hankelDefect h s n := by
  have htrunc : n + r ≥ n := by omega
  rw [map_sub]
  unfold cofactorNumerator
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  rw [if_neg (by omega : ¬ n + r < n), sub_zero]
  by_cases hrn : r < n
  · rw [if_pos hrn]
    let i : Fin n := ⟨r, hrn⟩
    have hrow := congrFun (hankelBorder_mulVec_cofactor h s n) i.castSucc
    have hzero : ((hankelBorder h s n).mulVec (cofactor h s n)) i.castSucc = 0 := by
      simpa [C3GeneralCofactor.lastScalarVector] using hrow
    have hcoef := cofactorReversed_mul_shiftedMoments_eq_row h s n i.castSucc
    simpa [i] using hcoef.trans hzero
  · have heq : r = n := by omega
    rw [if_neg hrn]
    subst r
    have hrow := congrFun (hankelBorder_mulVec_cofactor h s n) (Fin.last n)
    have hlast : ((hankelBorder h s n).mulVec (cofactor h s n)) (Fin.last n) =
        hankelDefect h s n := by
      simpa [C3GeneralCofactor.lastScalarVector] using hrow
    have hcoef := cofactorReversed_mul_shiftedMoments_eq_row h s n (Fin.last n)
    simpa [Fin.val_last] using hcoef.trans hlast

theorem cofactorDefect_coeff_low (h : ℕ → ℝ) (s n k : ℕ) (hk : k < 2*n) :
    PowerSeries.coeff k
        (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n) = 0 := by
  by_cases hkn : k < n
  · rw [map_sub]
    unfold cofactorNumerator
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc,
      if_pos hkn]
    simp
  · have hn : n ≤ k := Nat.le_of_not_gt hkn
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hr : r < n := by omega
    simpa [hr] using cofactorDefect_coeff_from_n h s n r (by omega)

theorem cofactorDefect_coeff_leading (h : ℕ → ℝ) (s n : ℕ) :
    PowerSeries.coeff (2*n)
        (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n) =
      hankelDefect h s n := by
  have hh := cofactorDefect_coeff_from_n h s n n (le_refl n)
  simpa [Nat.two_mul] using hh

def characteristicSeries (c : ℕ → ℝ) : PowerSeries ℝ := PowerSeries.mk c

def momentSeries (h : ℕ → ℝ) : PowerSeries ℝ := PowerSeries.mk h

def momentPrefix (h : ℕ → ℝ) (s : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => if k < s then h k else 0)

def transportedResidual (c h : ℕ → ℝ) (s n : ℕ) : PowerSeries ℝ :=
  -(cofactorReversed h s n * PowerSeries.derivative ℝ (characteristicSeries c)) -
    ((cofactorReversed h s n * momentPrefix h s +
        PowerSeries.X ^ s * cofactorNumerator h s n) * characteristicSeries c)

def normalizedDenominator (h : ℕ → ℝ) (s n : ℕ)
    (_hτ : (hankelPrefix h s n).det ≠ 0) : PowerSeries ℝ :=
  ((hankelPrefix h s n).det)⁻¹ • cofactorReversed h s n

def normalizedNumerator (h : ℕ → ℝ) (s n : ℕ)
    (_hτ : (hankelPrefix h s n).det ≠ 0) : PowerSeries ℝ :=
  ((hankelPrefix h s n).det)⁻¹ • cofactorNumerator h s n

def normalizedResidual (c h : ℕ → ℝ) (s n : ℕ)
    (hτ : (hankelPrefix h s n).det ≠ 0) : PowerSeries ℝ :=
  -(normalizedDenominator h s n hτ * PowerSeries.derivative ℝ (characteristicSeries c)) -
    ((normalizedDenominator h s n hτ * momentPrefix h s +
        PowerSeries.X ^ s * normalizedNumerator h s n hτ) * characteristicSeries c)

theorem momentSeries_shift_decomposition (h : ℕ → ℝ) (s : ℕ) :
    momentSeries h = momentPrefix h s + PowerSeries.X ^ s * shiftedMoments h s := by
  apply PowerSeries.ext
  intro k
  by_cases hks : k < s
  · simp [momentSeries, momentPrefix, shiftedMoments, hks,
      PowerSeries.coeff_X_pow_mul']
  · have hsk : s ≤ k := Nat.le_of_not_gt hks
    simp [momentSeries, momentPrefix, shiftedMoments, hks,
      hsk, PowerSeries.coeff_X_pow_mul']

theorem transportedResidual_factor (c h : ℕ → ℝ) (s n : ℕ)
    (hrec : characteristicSeries c * momentSeries h =
      -(PowerSeries.derivative ℝ (characteristicSeries c))) :
    transportedResidual c h s n =
      characteristicSeries c * (PowerSeries.X ^ s *
        (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n)) := by
  unfold transportedResidual
  calc
    -(cofactorReversed h s n * PowerSeries.derivative ℝ (characteristicSeries c)) -
        ((cofactorReversed h s n * momentPrefix h s +
          PowerSeries.X ^ s * cofactorNumerator h s n) * characteristicSeries c) =
      cofactorReversed h s n *
          (-(PowerSeries.derivative ℝ (characteristicSeries c))) -
        ((cofactorReversed h s n * momentPrefix h s +
          PowerSeries.X ^ s * cofactorNumerator h s n) * characteristicSeries c) := by ring
    _ = cofactorReversed h s n * (characteristicSeries c * momentSeries h) -
        ((cofactorReversed h s n * momentPrefix h s +
          PowerSeries.X ^ s * cofactorNumerator h s n) * characteristicSeries c) := by
          rw [← hrec]
    _ = characteristicSeries c * (PowerSeries.X ^ s *
        (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n)) := by
          rw [momentSeries_shift_decomposition]
          ring

theorem normalizedResidual_eq_smul (c h : ℕ → ℝ) (s n : ℕ)
    (hτ : (hankelPrefix h s n).det ≠ 0) :
    normalizedResidual c h s n hτ =
      ((hankelPrefix h s n).det)⁻¹ • transportedResidual c h s n := by
  unfold normalizedResidual normalizedDenominator normalizedNumerator transportedResidual
  simp only [PowerSeries.smul_eq_C_mul]
  ring

theorem normalizedDenominator_coeff_zero (h : ℕ → ℝ) (s n : ℕ)
    (hτ : (hankelPrefix h s n).det ≠ 0) :
    PowerSeries.coeff 0 (normalizedDenominator h s n hτ) = 1 := by
  rw [normalizedDenominator, PowerSeries.coeff_smul, smul_eq_mul,
    cofactorReversed_coeff_zero]
  exact inv_mul_cancel₀ hτ

theorem singularCofactorReversed_coeff_zero (h : ℕ → ℝ) (s n : ℕ)
    (hτ : (hankelPrefix h s n).det = 0) :
    PowerSeries.coeff 0 (cofactorReversed h s n) = 0 := by
  rw [cofactorReversed_coeff_zero]
  exact hτ

private theorem trunc_eq_zero_of_coeff_prefix (f : PowerSeries ℝ) (m : ℕ)
    (hf : ∀ k < m, PowerSeries.coeff k f = 0) :
    PowerSeries.trunc m f = 0 := by
  apply Polynomial.ext
  intro k
  rw [PowerSeries.coeff_trunc]
  by_cases hk : k < m
  · simp [hk, hf k hk]
  · simp [hk]

theorem coeff_mul_zero_prefix (f g : PowerSeries ℝ) (m k : ℕ) (hk : k < m)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) :
    PowerSeries.coeff k (f * g) = 0 := by
  rw [PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc₂ f g hk hk]
  rw [trunc_eq_zero_of_coeff_prefix g m hg]
  simp

private theorem trunc_succ_eq_monomial (g : PowerSeries ℝ) (m : ℕ)
    (hg : ∀ k < m, PowerSeries.coeff k g = 0) :
    ((PowerSeries.trunc (m + 1) g : Polynomial ℝ) : PowerSeries ℝ) =
      PowerSeries.monomial m (PowerSeries.coeff m g) := by
  ext k
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_monomial]
  by_cases hk : k < m
  · simp [hg k hk, ne_of_lt hk]
  · by_cases hkm : k = m
    · subst k
      simp
    · have hmk : m + 1 ≤ k := by omega
      simp [not_lt.mpr hmk, hkm]

theorem coeff_mul_leading (f g : PowerSeries ℝ) (m : ℕ)
    (hg : ∀ k < m, PowerSeries.coeff k g = 0) :
    PowerSeries.coeff m (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff m g := by
  rw [PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc₂ f g (Nat.lt_succ_self m)
    (Nat.lt_succ_self m)]
  rw [trunc_succ_eq_monomial g m hg]
  have hmon : PowerSeries.monomial m (PowerSeries.coeff m g) =
      PowerSeries.C (PowerSeries.coeff m g) * PowerSeries.X ^ m := by
    ext k
    simp [PowerSeries.coeff_monomial, eq_comm]
  rw [hmon, ← mul_assoc]
  have hcoeff : PowerSeries.coeff m
      (((PowerSeries.trunc (m + 1) f : Polynomial ℝ) : PowerSeries ℝ) *
        PowerSeries.C (PowerSeries.coeff m g) * PowerSeries.X ^ m) =
      PowerSeries.coeff 0
        (((PowerSeries.trunc (m + 1) f : Polynomial ℝ) : PowerSeries ℝ) *
          PowerSeries.C (PowerSeries.coeff m g)) := by
    simpa using (PowerSeries.coeff_mul_X_pow
      (((PowerSeries.trunc (m + 1) f : Polynomial ℝ) : PowerSeries ℝ) *
        PowerSeries.C (PowerSeries.coeff m g)) m 0)
  rw [hcoeff]
  rw [PowerSeries.coeff_mul_C]
  have hzero : PowerSeries.coeff 0
      ((PowerSeries.trunc (m + 1) f : Polynomial ℝ) : PowerSeries ℝ) =
        PowerSeries.coeff 0 f := by
    simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  rw [hzero]

theorem coeff_X_pow_mul_zero_prefix (g : PowerSeries ℝ) (s m k : ℕ)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) (hk : k < s + m) :
    PowerSeries.coeff k (PowerSeries.X ^ s * g) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hsk : s ≤ k
  · have hkm : k - s < m := by omega
    simp [hsk, hg (k-s) hkm]
  · simp [hsk]

theorem coeff_X_pow_mul_leading (g : PowerSeries ℝ) (s m : ℕ) :
    PowerSeries.coeff (s + m) (PowerSeries.X ^ s * g) = PowerSeries.coeff m g := by
  rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega : s ≤ s + m)]
  rw [Nat.add_sub_cancel_left]

theorem transportedResidual_coeff_low (c h : ℕ → ℝ) (s n k : ℕ)
    (hrec : characteristicSeries c * momentSeries h =
      -(PowerSeries.derivative ℝ (characteristicSeries c)))
    (hk : k < 2*n + s) :
    PowerSeries.coeff k (transportedResidual c h s n) = 0 := by
  rw [transportedResidual_factor c h s n hrec]
  have hY : ∀ j < 2*n+s, PowerSeries.coeff j
      (PowerSeries.X ^ s *
        (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n)) = 0 := by
    intro j hj
    have hj' : j < s + 2*n := by omega
    exact coeff_X_pow_mul_zero_prefix
      (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n)
      s (2*n) j (fun i hi => cofactorDefect_coeff_low h s n i hi) hj'
  exact coeff_mul_zero_prefix (characteristicSeries c)
    (PowerSeries.X ^ s *
      (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n))
    (2*n+s) k hk hY

theorem transportedResidual_coeff_leading (c h : ℕ → ℝ) (s n : ℕ)
    (hrec : characteristicSeries c * momentSeries h =
      -(PowerSeries.derivative ℝ (characteristicSeries c))) :
    PowerSeries.coeff (2*n+s) (transportedResidual c h s n) =
      c 0 * hankelDefect h s n := by
  rw [transportedResidual_factor c h s n hrec]
  have hY : ∀ j < 2*n+s,
      PowerSeries.coeff j (PowerSeries.X ^ s *
        (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n)) = 0 := by
    intro j hj
    have hj' : j < s + 2*n := by omega
    exact coeff_X_pow_mul_zero_prefix
      (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n)
      s (2*n) j (fun i hi => cofactorDefect_coeff_low h s n i hi) hj'
  rw [coeff_mul_leading (characteristicSeries c)
    (PowerSeries.X ^ s *
      (cofactorReversed h s n * shiftedMoments h s - cofactorNumerator h s n))
    (2*n+s) hY]
  rw [show 2*n+s = s+(2*n) by omega,
    coeff_X_pow_mul_leading]
  rw [cofactorDefect_coeff_leading]
  simp [characteristicSeries]

theorem normalizedResidual_coeff_low (c h : ℕ → ℝ) (s n k : ℕ)
    (hτ : (hankelPrefix h s n).det ≠ 0)
    (hrec : characteristicSeries c * momentSeries h =
      -(PowerSeries.derivative ℝ (characteristicSeries c)))
    (hk : k < 2*n+s) :
    PowerSeries.coeff k (normalizedResidual c h s n hτ) = 0 := by
  rw [normalizedResidual_eq_smul]
  simp only [PowerSeries.coeff_smul, smul_eq_mul,
    transportedResidual_coeff_low c h s n k hrec hk]
  simp

theorem normalizedResidual_coeff_leading (c h : ℕ → ℝ) (s n : ℕ)
    (hτ : (hankelPrefix h s n).det ≠ 0)
    (hrec : characteristicSeries c * momentSeries h =
      -(PowerSeries.derivative ℝ (characteristicSeries c))) :
    PowerSeries.coeff (2*n+s) (normalizedResidual c h s n hτ) =
      c 0 * hankelPivot h s n := by
  rw [normalizedResidual_eq_smul]
  simp only [PowerSeries.coeff_smul, smul_eq_mul,
    transportedResidual_coeff_leading c h s n hrec]
  rw [hankelDefect_eq_det_mul_pivot h s n hτ]
  field_simp [hτ]

end
end C3ResidualPade
