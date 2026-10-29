import GeometryOfNumbers.Analysis.MomentGramPositivity
import GeometryOfNumbers.Analysis.FiniteNativeMaterialClock
import GeometryOfNumbers.Analysis.RealCarryTfvd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Roots

/-!
# The integer moment Gram: a genuine Hankel realized by a positive geometric family

The complete vertical observation Gram (`CompleteVerticalObservationGram`) is positive
definite by construction, yet is proven **not** a Hankel / not a moment Gram
(`completeVerticalObservabilityGram_not_hankel`; the no-go
`NO_GO_FULL_TFVD_CHANNEL_GRAM_HANKEL`, already `⟨J₀,J₂⟩ ≠ ⟨J₁,J₁⟩` at order three).  That
no-go leaves open the need for *"a genuinely different completed geometric family and an
independently established moment readout"*.

This file supplies exactly that, for the native **integer** geometry.  The feature family is
the weighted power system of the first `M` integers,

  `integerFeature k = (n ↦ √(wₙ)·xₙ^k) ∈ EuclideanSpace ℝ (Fin M)`,

with the native critical vertical amplitude `criticalVerticalAmplitudeRatio (n+1) = (n+1)^(−1/2)`
at the scale-compatible half `σ = ½` (its square is the vertical norm
`wₙ = (n+1)⁻¹ = (n+1)^(−2σ)`) and the native log-clock frequencies
`xₙ = finiteRealSpectralFrequency n = log(n+1)` (the self-adjoint diagonal generator `L_N`).
Its Gram reproduces the integer moment kernel

  `integerMoments (i+j) = ⟪integerFeature i, integerFeature j⟫`,

so `IsMomentGramRepresentation (integerMoments M) (integerFeature M)` holds.  Feeding this to
the repository's own positivity channel (`hankelGram_posSemidef_of_gramRepresentation`,
`hankelGram_posDef_of_gramRepresentation`) makes every finite integer Hankel section positive
— **unconditionally**, with no zeros and no `ζ`.  Unlike the observation Gram, this one *is* a
genuine Hankel (`hankelGram` depends only on `i+j`), so it is precisely the positive,
moment-readout geometric family the no-go asked for.  The weights being positive by
construction is the geometric content: the norm of the integer vertical tower resolved at the
half.
-/

namespace GeometryOfNumbers.Analysis

open scoped BigOperators

noncomputable section

variable (M : ℕ)

/-- Integer log-frequency node: the native material log-clock frequency
`finiteRealSpectralFrequency n = log(n+1)` (the self-adjoint diagonal generator `L_N`). -/
def integerNode (n : Fin M) : ℝ := NativeMaterialClock.finiteRealSpectralFrequency n

/-- Integer vertical-norm weight: the square of the native critical vertical amplitude
`criticalVerticalAmplitudeRatio (n+1) = (n+1)^(−1/2)` at the scale-compatible half `σ=½`,
so `wₙ = (n+1)⁻¹ = (n+1)^(−2σ)` is the resolved norm of the integer vertical tower. -/
def integerWeight (n : Fin M) : ℝ :=
  criticalVerticalAmplitudeRatio ((n : ℕ) + 1) (Nat.succ_pos _) ^ 2

/-- The integer moment sequence `mₖ = Σ_{n<M} wₙ·xₙ^k` (a finite, genuine moment readout). -/
def integerMoments (k : ℕ) : ℝ := ∑ n : Fin M, integerWeight M n * integerNode M n ^ k

/-- The weighted power feature vectors `k ↦ (n ↦ √(wₙ)·xₙ^k)` in `EuclideanSpace ℝ (Fin M)`. -/
def integerFeature (k : ℕ) : EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 fun n => Real.sqrt (integerWeight M n) * integerNode M n ^ k

theorem integerWeight_pos (n : Fin M) : 0 < integerWeight M n := by
  simp only [integerWeight]
  exact pow_pos (criticalVerticalAmplitudeRatio_pos ((n : ℕ) + 1) (Nat.succ_pos _)) 2

theorem integerNode_injective : Function.Injective (integerNode M) := by
  intro a b hab
  simp only [integerNode, NativeMaterialClock.finiteRealSpectralFrequency] at hab
  have ha : ((a.1 + 1 : ℕ) : ℝ) ∈ Set.Ioi (0 : ℝ) :=
    Set.mem_Ioi.mpr (by exact_mod_cast Nat.succ_pos a.1)
  have hb : ((b.1 + 1 : ℕ) : ℝ) ∈ Set.Ioi (0 : ℝ) :=
    Set.mem_Ioi.mpr (by exact_mod_cast Nat.succ_pos b.1)
  have heq : ((a.1 + 1 : ℕ) : ℝ) = ((b.1 + 1 : ℕ) : ℝ) := Real.log_injOn_pos ha hb hab
  have hnat : (a.1 + 1 : ℕ) = (b.1 + 1 : ℕ) := Nat.cast_injective heq
  exact Fin.ext (by omega)

/-- **The integer feature Gram reproduces the integer moment kernel.**  This is the exact input
the repository's positivity channel expects: an independently established moment readout
realized by one Hilbert feature family. -/
theorem integer_isMomentGramRepresentation :
    IsMomentGramRepresentation (integerMoments M) (integerFeature M) := by
  intro i j
  rw [Matrix.gram_apply]
  simp only [integerFeature]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [integerMoments, dotProduct, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [pow_add]
  set s := Real.sqrt (integerWeight M n)
  have hsq : s * s = integerWeight M n := Real.mul_self_sqrt (integerWeight_pos M n).le
  rw [← hsq]; ring

/-- **Every finite integer Hankel section is positive semidefinite — unconditionally.** -/
theorem integerHankel_posSemidef (N : ℕ) :
    (hankelGram (integerMoments M) N).PosSemidef :=
  hankelGram_posSemidef_of_gramRepresentation (integer_isMomentGramRepresentation M) N

/-- Raw (un-lifted) weighted power functions `k ↦ (n ↦ √(wₙ)·xₙ^k) : Fin M → ℝ`. -/
def integerRawFeature (k : ℕ) : Fin M → ℝ :=
  fun n => Real.sqrt (integerWeight M n) * integerNode M n ^ k

/-- **Linear independence of the integer feature prefix** for `N ≤ M`: the weighted power
vectors of distinct integer log-nodes are independent (a weighted Vandermonde system). -/
theorem integerFeature_linearIndependent {N : ℕ} (hNM : N ≤ M) :
    LinearIndependent ℝ (fun i : Fin N => integerFeature M (i : ℕ)) := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    rw [Fintype.linearIndependent_iff]
    intro g _ k
    exact k.elim0
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Transport the EuclideanSpace relation to the raw function space via `ofLp`.
  have key : ∑ k : Fin N, g k • integerRawFeature M (k : ℕ) = 0 := by
    have h1 : (WithLp.linearEquiv 2 ℝ (Fin M → ℝ)) (∑ k : Fin N, g k • integerFeature M (k : ℕ))
        = ∑ k : Fin N, g k • integerRawFeature M (k : ℕ) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_smul]; rfl
    rw [hg, map_zero] at h1
    exact h1.symm
  -- Pointwise: the polynomial `∑ gₖ Xᵏ` vanishes at every node `xₙ`.
  have hpoly : ∀ n : Fin M, ∑ k : Fin N, g k * integerNode M n ^ (k : ℕ) = 0 := by
    intro n
    have hn := congrFun key n
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, integerRawFeature] at hn
    have hfac : Real.sqrt (integerWeight M n) * ∑ k : Fin N, g k * integerNode M n ^ (k : ℕ) = 0 := by
      rw [Finset.mul_sum, ← hn]
      exact Finset.sum_congr rfl fun k _ => by ring
    exact (mul_eq_zero.mp hfac).resolve_left
      (ne_of_gt (Real.sqrt_pos.mpr (integerWeight_pos M n)))
  -- A degree `< N ≤ M` polynomial with `M` distinct roots is zero, so every coefficient is zero.
  set P : Polynomial ℝ := ∑ k : Fin N, Polynomial.C (g k) * Polynomial.X ^ (k : ℕ) with hP
  have hcoeff : ∀ k : Fin N, P.coeff (k : ℕ) = g k := by
    intro k
    rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hbk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun h => hbk (Fin.ext h.symm)), mul_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hPeval : ∀ n : Fin M, P.eval (integerNode M n) = 0 := by
    intro n
    rw [hP]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact hpoly n
  have hPzero : P = 0 := by
    by_contra hPne
    have hdeg : P.natDegree < N := by
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ((Finset.sup_lt_iff hNpos).mpr ?_)
      intro k _
      calc (Polynomial.C (g k) * Polynomial.X ^ (k : ℕ)).natDegree
          ≤ (Polynomial.X ^ (k : ℕ)).natDegree := Polynomial.natDegree_C_mul_le _ _
        _ = (k : ℕ) := Polynomial.natDegree_X_pow _
        _ < N := k.isLt
    have hmem : ∀ n : Fin M, integerNode M n ∈ P.roots.toFinset := by
      intro n
      simp only [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
      exact hPeval n
    have hcard : (Finset.univ : Finset (Fin M)).card ≤ P.roots.toFinset.card :=
      Finset.card_le_card_of_injOn _ (fun n _ => hmem n)
        (fun a _ b _ hab => integerNode_injective M hab)
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have hle : M ≤ P.natDegree :=
      le_trans hcard (le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' P))
    omega
  intro k
  have hck := hcoeff k
  rw [hPzero, Polynomial.coeff_zero] at hck
  exact hck.symm

/-- **The integer Hankel is positive definite in every order `N ≤ M` — unconditionally.**
This is the canonical, genuine-Hankel positivity the no-go called for: supplied by the
integer vertical-norm geometry, with no zeros and no `ζ`.  The strict positivity is exactly
the invertible-Cholesky / canonical-operator input. -/
theorem integerHankel_posDef {N : ℕ} (hNM : N ≤ M) :
    (hankelGram (integerMoments M) N).PosDef :=
  hankelGram_posDef_of_gramRepresentation (integer_isMomentGramRepresentation M) N
    (integerFeature_linearIndependent M hNM)

end

end GeometryOfNumbers.Analysis
