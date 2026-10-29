import GeometryOfNumbers.Analysis.FiniteJacobiTransport
import Mathlib.Analysis.Matrix.Order

/-! Test the literal transformation g(n)=h(n)^2. No source, norm, or canonical
moment is redefined: g is a separately named candidate. -/
namespace CarryEntrywiseSquare
open GeometryOfNumbers.Analysis
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false

def squaredMoments (h : ℕ → ℝ) (n : ℕ) : ℝ := h n ^ 2

theorem hankel_square (h : ℕ → ℝ) (N : ℕ) :
    hankelGram (squaredMoments h) N = hankelGram h N ⊙ hankelGram h N := by
  ext i j
  simp [hankelGram, squaredMoments, Matrix.hadamard_apply, pow_two]

theorem shifted_square (h : ℕ → ℝ) (N : ℕ) :
    shiftedHankel (squaredMoments h) N = shiftedHankel h N ⊙ shiftedHankel h N := by
  ext i j
  simp [shiftedHankel, squaredMoments, Matrix.hadamard_apply, pow_two]

/-- This uses positivity of the OLD matrix: it does not prove it upstream. -/
theorem squared_psd_of_psd (h : ℕ → ℝ) (N : ℕ)
    (hp : (hankelGram h N).PosSemidef) :
    (hankelGram (squaredMoments h) N).PosSemidef := by
  rw [hankel_square]
  exact hp.hadamard hp

theorem squared_shifted_psd_of_psd (h : ℕ → ℝ) (N : ℕ)
    (hp : (shiftedHankel h N).PosSemidef) :
    (shiftedHankel (squaredMoments h) N).PosSemidef := by
  rw [shifted_square]
  exact hp.hadamard hp

/-- The actual scalar generalized eigenvalue in dimension one. -/
def singletonEigenvalue (h : ℕ → ℝ) : ℝ := h 1 / h 0

theorem singleton_congruence (B M : Matrix (Fin 1) (Fin 1) ℝ) :
    (B * M * B.transpose) 0 0 = B 0 0 ^ 2 * M 0 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply]
  ring

/-- Every exact real whitening of the original pair gives this ratio.
The conclusion is independent of the choice of orthogonal coordinates. -/
theorem actual_singleton_section (h : ℕ → ℝ) (hzero : h 0 ≠ 0)
    (w : FiniteGramWhitening h 1) :
    finiteJacobiSection h 1 w 0 0 = singletonEigenvalue h := by
  have hw := congrFun (congrFun w.gram_identity 0) 0
  change (w.inverseFactor * hankelGram h 1 * w.inverseFactor.transpose) 0 0 = 1 at hw
  rw [singleton_congruence] at hw
  simp only [hankelGram_apply, Fin.val_zero, zero_add] at hw
  change (w.inverseFactor * shiftedHankel h 1 * w.inverseFactor.transpose) 0 0 = _
  rw [singleton_congruence]
  simp only [shiftedHankel_apply, Fin.val_zero, zero_add]
  apply (eq_div_iff hzero).2
  linear_combination h 1 * hw

theorem singleton_square (h : ℕ → ℝ) :
    singletonEigenvalue (squaredMoments h) = singletonEigenvalue h ^ 2 := by
  simp [singletonEigenvalue, squaredMoments, div_pow]

theorem inverse_sqrt_gt_one {x : ℝ} (hx : 0 < x) (hxone : x < 1) :
    1 < (Real.sqrt x)⁻¹ := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hss := Real.sq_sqrt (le_of_lt hx)
  have hsone : Real.sqrt x < 1 := by nlinarith
  rw [← one_div]
  exact (lt_div_iff₀ hs).2 (by simpa using hsone)

/-- The candidate eigenvalue is on the opposite side of 1 from the target
height whenever 0<h1<h0. This is an exact obstruction, not a numerical test. -/
theorem singleton_square_not_height (h : ℕ → ℝ)
    (hzero : 0 < h 0) (hone : 0 < h 1) (hlt : h 1 < h 0) :
    singletonEigenvalue (squaredMoments h) < 1 ∧
      1 < (Real.sqrt (singletonEigenvalue h))⁻¹ := by
  have hp : 0 < singletonEigenvalue h := div_pos hone hzero
  have hl : singletonEigenvalue h < 1 := (div_lt_one hzero).2 hlt
  constructor
  · rw [singleton_square]
    nlinarith
  · exact inverse_sqrt_gt_one hp hl

/-- Applying the OLD height transform after squaring gives the square of
the OLD height in dimension one, not that height as a Jacobi eigenvalue. -/
theorem singleton_squared_height (h : ℕ → ℝ)
    (hp : 0 < singletonEigenvalue h) :
    (Real.sqrt (singletonEigenvalue (squaredMoments h)))⁻¹ =
      ((Real.sqrt (singletonEigenvalue h))⁻¹)^2 := by
  rw [singleton_square, Real.sqrt_sq (le_of_lt hp)]
  rw [inv_pow, Real.sq_sqrt (le_of_lt hp)]

/-- A global mass factor cancels from this eigenvalue, so it cannot repair
the discrepancy by merely normalizing h0. -/
theorem singleton_mass_cancels (h : ℕ → ℝ) (a : ℝ) (ha : a ≠ 0) :
    singletonEigenvalue (fun n => a * h n) = singletonEigenvalue h := by
  simp [singletonEigenvalue, mul_div_mul_left, ha]

/-- The original logarithmic recurrence has a UNIQUE sequence: if h0 lies
strictly between zero and one, its pointwise square cannot satisfy the same
recurrence for the same completed characteristic. -/
theorem square_changes_logarithmic_sequence (phi h : ℕ → ℝ)
    (hphi : phi 0 ≠ 0) (hrel : IsLogDerivativeMomentSequence phi h)
    (hp : 0 < h 0) (hlt : h 0 < 1) :
    ¬ IsLogDerivativeMomentSequence phi (squaredMoments h) := by
  intro hs
  have he := congrFun (hrel.unique hphi hs) 0
  change h 0 = h 0 ^ 2 at he
  nlinarith

/-- Two independent finite spectral indices remain present. Pointwise
squaring produces pairwise PRODUCTS of the old nodes, with no inverse roots.
No positive measure representation of the native moments is assumed here. -/
theorem finite_product_moments {I : Type*} [Fintype I]
    (w nodes : I → ℝ) (n : ℕ) :
    (∑ a, w a * nodes a ^ n)^2 =
      ∑ a, ∑ b, (w a * w b) * (nodes a * nodes b)^n := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_pow]
  ring

/-- A Gram square has a tensor-pair feature, once a Gram is already known.
This keeps every cross term; it does not assert native Gram identification. -/
theorem paired_feature {I : Type*} [Fintype I] (u v : I → ℝ) :
    (∑ a, u a * v a)^2 =
      ∑ a, ∑ b, (u a * u b) * (v a * v b) := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Squaring all entries does not force a Hankel to be positive. -/
def badMoments (n : ℕ) : ℝ := if n = 1 then 2 else 1

theorem squared_bad_quadratic :
    dotProduct (![1,-1] : Fin 2 → ℝ)
      (hankelGram (squaredMoments badMoments) 2 *ᵥ ![1,-1]) = -6 := by
  norm_num [dotProduct, Matrix.mulVec, hankelGram, squaredMoments,
    badMoments, Fin.sum_univ_succ]

theorem squared_bad_not_psd :
    ¬ (hankelGram (squaredMoments badMoments) 2).PosSemidef := by
  intro hp
  have hh := hp.dotProduct_mulVec_nonneg (![1,-1] : Fin 2 → ℝ)
  norm_num only [star_trivial, squared_bad_quadratic] at hh

/-- Conversely, squaring can conceal a negative original direction. -/
def maskedMoments (n : ℕ) : ℝ := if n = 2 then -2 else 1

theorem masked_original_not_psd : ¬ (hankelGram maskedMoments 2).PosSemidef := by
  intro hp
  have hh := hp.dotProduct_mulVec_nonneg (![0,1] : Fin 2 → ℝ)
  norm_num [star_trivial, dotProduct, Matrix.mulVec, hankelGram,
    maskedMoments, Fin.sum_univ_succ] at hh

theorem masked_square_psd :
    (hankelGram (squaredMoments maskedMoments) 2).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (hankelGram_isSymm _ _)
  · intro x
    simp [star_trivial, dotProduct, Matrix.mulVec, hankelGram,
      squaredMoments, maskedMoments]
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1)]

end
end CarryEntrywiseSquare
