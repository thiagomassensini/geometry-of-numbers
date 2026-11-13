import SigmaZeroObstruction
import FiniteHankelFailure
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# First finite Hankel failure for the original sigma source

This module derives a least failing Hankel order from the already proved
positive-height-zero obstruction. It keeps the source moments and the explicit
nonzero-shift hypotheses unchanged.
-/

open scoped Matrix
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma CarryMomentLogConvex
  FiniteHankelFailure InnerProductSpace WithLp

namespace CarrySigmaObstruction

/-- The quadratic form of a real source moment matrix, expressed as an operator on its
Euclidean coordinate space, is exactly its original matrix quadratic form. -/
private theorem sourceMomentQuadratic_eq_euclidean_inner
    (h : ℕ → ℝ) (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    sourceMomentQuadratic h 0 n (ofLp x) =
      ⟪x, (sourceMomentMatrix h 0 n).toEuclideanLin x⟫_ℝ := by
  change sourceMomentQuadratic h 0 n (ofLp x) =
    ⟪x, Matrix.toLpLin 2 2 (sourceMomentMatrix h 0 n) x⟫_ℝ
  rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [sourceMomentQuadratic, star_trivial]
  exact dotProduct_comm _ _

/-- The coupling vector has the same pairing in source coordinates and in EuclideanSpace. -/
private theorem sourceMomentCoupling_eq_euclidean_inner
    (h : ℕ → ℝ) (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    sourceMomentCoupling h 0 n ⬝ᵥ ofLp x =
      ⟪toLp 2 (sourceMomentCoupling h 0 n), x⟫_ℝ := by
  change sourceMomentCoupling h 0 n ⬝ᵥ ofLp x =
    ⟪toLp 2 (sourceMomentCoupling h 0 n), toLp 2 (ofLp x)⟫_ℝ
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial]
  exact dotProduct_comm _ _

/-- A failing next moment matrix over a positive semidefinite prefix is classified exactly by
the two singular-safe block mechanisms. This statement is source-independent: `h` is any real
sequence. The prefix is represented by its original moment matrix, and the new column by its
original source coupling. -/
theorem sourceMoment_succ_failure_classification
    (h : ℕ → ℝ) (n : ℕ)
    (hprefix : (sourceMomentMatrix h 0 n).PosSemidef)
    (hnext : ¬ (sourceMomentMatrix h 0 (n + 1)).PosSemidef) :
    (∃ w : Fin n → ℝ,
        sourceMomentMatrix h 0 n *ᵥ w = 0 ∧
          sourceMomentCoupling h 0 n ⬝ᵥ w ≠ 0) ∨
      ∃ y : Fin n → ℝ,
        sourceMomentMatrix h 0 n *ᵥ y = sourceMomentCoupling h 0 n ∧
          h (2 * n) - sourceMomentCoupling h 0 n ⬝ᵥ y < 0 := by
  let A : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (sourceMomentMatrix h 0 n).toEuclideanLin
  let b : EuclideanSpace ℝ (Fin n) := toLp 2 (sourceMomentCoupling h 0 n)
  have hAsymm : A.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    exact sourceMomentMatrix_isHermitian h 0 n
  have hAnonneg : ∀ x, 0 ≤ ⟪x, A x⟫_ℝ := by
    intro x
    have hx := hprefix.dotProduct_mulVec_nonneg (ofLp x)
    have hq : 0 ≤ sourceMomentQuadratic h 0 n (ofLp x) := by
      simpa [sourceMomentQuadratic, Pi.star_apply, star_trivial] using hx
    rw [sourceMomentQuadratic_eq_euclidean_inner] at hq
    exact hq
  have hblockbad : ¬ ∀ x t, 0 ≤ blockQuadratic A b (h (2 * n)) x t := by
    intro hblock
    apply hnext
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨sourceMomentMatrix_isHermitian h 0 (n + 1), ?_⟩
    intro z
    have hinnerold : sourceMomentQuadratic h 0 n (Fin.init z) =
        ⟪toLp 2 (Fin.init z), A (toLp 2 (Fin.init z))⟫_ℝ := by
      simpa [A] using sourceMomentQuadratic_eq_euclidean_inner h n
        (toLp 2 (Fin.init z))
    have hinnercross : sourceMomentCoupling h 0 n ⬝ᵥ Fin.init z =
        ⟪b, toLp 2 (Fin.init z)⟫_ℝ := by
      simpa [b] using sourceMomentCoupling_eq_euclidean_inner h n
        (toLp 2 (Fin.init z))
    have hform : sourceMomentQuadratic h 0 (n + 1) z =
        blockQuadratic A b (h (2 * n)) (toLp 2 (Fin.init z)) (z (Fin.last n)) := by
      rw [← Fin.snoc_init_self z, sourceMomentQuadratic_snoc, hinnerold, hinnercross]
      simp [blockQuadratic, A, b]
    have hq := hblock (toLp 2 (Fin.init z)) (z (Fin.last n))
    have hsource : 0 ≤ sourceMomentQuadratic h 0 (n + 1) z := by
      rw [hform]
      exact hq
    simpa [sourceMomentQuadratic, sourceMomentMatrix, Pi.star_apply, star_trivial] using hsource
  have hclassified := block_failure_classification A b (h (2 * n)) hAsymm hAnonneg hblockbad
  rcases hclassified with hcross | hresidual
  · left
    obtain ⟨w, hAw, hbw⟩ := hcross
    refine ⟨ofLp w, ?_, ?_⟩
    · have hw := congrArg ofLp hAw
      simpa [A, Matrix.ofLp_toLpLin] using hw
    · have hpair : sourceMomentCoupling h 0 n ⬝ᵥ ofLp w = ⟪b, w⟫_ℝ := by
        simpa [b] using sourceMomentCoupling_eq_euclidean_inner h n w
      rw [hpair]
      exact hbw
  · right
    obtain ⟨y, hAy, hres⟩ := hresidual
    refine ⟨ofLp y, ?_, ?_⟩
    · have hy := congrArg ofLp hAy
      simpa [A, b, Matrix.ofLp_toLpLin] using hy
    · have hpair : sourceMomentCoupling h 0 n ⬝ᵥ ofLp y =
          ⟪y, A y⟫_ℝ := by
        calc
          sourceMomentCoupling h 0 n ⬝ᵥ ofLp y = ⟪b, y⟫_ℝ := by
            simpa [b] using sourceMomentCoupling_eq_euclidean_inner h n y
          _ = ⟪y, b⟫_ℝ := real_inner_comm _ _
          _ = ⟪y, A y⟫_ℝ := by rw [hAy]
      simpa [hpair] using hres

/-- The size-one failure is the legitimate zero-prefix case: its only mechanism is
`h 0 < 0`. There is no kernel-crossing vector in the empty prefix. -/
theorem sourceMoment_size_one_failure_neg_zero (h : ℕ → ℝ)
    (hbad : ¬ (sourceMomentMatrix h 0 1).PosSemidef) : h 0 < 0 := by
  have hprefix : (sourceMomentMatrix h 0 0).PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨by simpa using sourceMomentMatrix_isHermitian h 0 0, ?_⟩
    intro v
    simp
  obtain hcross | ⟨y, hy, hres⟩ :=
    sourceMoment_succ_failure_classification h 0 hprefix hbad
  · obtain ⟨w, _hw, hcross⟩ := hcross
    have hzero : sourceMomentCoupling h 0 0 ⬝ᵥ w = 0 := by simp
    rw [hzero] at hcross
    exact (hcross rfl).elim
  · simpa [sourceMomentCoupling] using hres

/-- Under the original positive-height-zero hypotheses, the source sigma Hankel
sequence has a least non-PSD size. Every smaller prefix remains positive
semidefinite, and the least failing matrix has an explicit negative direction. -/
theorem exists_first_sigma_hankel_failure_of_zero
    (d γ : ℝ) (hγ : 0 < γ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ))
    (hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0) :
    ∃ N : ℕ,
      0 < N ∧
      ¬ (hankelMatrix (completedSigmaLogJet d) N).PosSemidef ∧
      (∀ m < N, (hankelMatrix (completedSigmaLogJet d) m).PosSemidef) ∧
      ∃ v : Fin N → ℝ, v ≠ 0 ∧
        v ⬝ᵥ (hankelMatrix (completedSigmaLogJet d) N *ᵥ v) < 0 := by
  obtain ⟨Nbad, vbad, hvbad, hqbad⟩ :=
    exists_sigmaMatrix_negative_direction_of_zero d γ hγ hd₀ hd₁ hzero
  have hnotbad : ¬ (CarryMovingSigma.sigmaMatrix d 0 Nbad).PosSemidef := by
    intro hpsd
    have hnonneg := hpsd.dotProduct_mulVec_nonneg vbad
    have hnonneg' : 0 ≤ vbad ⬝ᵥ (CarryMovingSigma.sigmaMatrix d 0 Nbad *ᵥ vbad) := by
      simpa [Pi.star_apply, star_trivial] using hnonneg
    linarith
  obtain ⟨N, hNbad, hNsmall⟩ :=
    FiniteHankelFailure.exists_least_bad_size (fun n => CarryMovingSigma.sigmaMatrix d 0 n)
      ⟨Nbad, hnotbad⟩
  have hNpos : 0 < N := by
    by_contra hnotpos
    have hNzero : N = 0 := by omega
    subst N
    have hsymm0 : (CarryMovingSigma.sigmaMatrix d 0 0).IsSymm :=
      CarryMovingSigma.sigma_matrix_symm d 0 0
    have hHerm0 : (CarryMovingSigma.sigmaMatrix d 0 0).IsHermitian := by
      simpa using hsymm0
    have hpsd0 : (CarryMovingSigma.sigmaMatrix d 0 0).PosSemidef :=
      Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm0, by intro v; simp⟩
    exact hNbad hpsd0
  have hNbadH : ¬ (hankelMatrix (completedSigmaLogJet d) N).PosSemidef := by
    simpa [completedSigmaLogJet_sigmaMatrix_eq_hankel] using hNbad
  have hNsmallH : ∀ m < N,
      (hankelMatrix (completedSigmaLogJet d) m).PosSemidef := by
    intro m hm
    simpa [completedSigmaLogJet_sigmaMatrix_eq_hankel] using hNsmall m hm
  have hsymm : (CarryMovingSigma.sigmaMatrix d 0 N).IsSymm := CarryMovingSigma.sigma_matrix_symm d 0 N
  have hHerm : (CarryMovingSigma.sigmaMatrix d 0 N).IsHermitian := by simpa using hsymm
  have hnotQuad : ¬ ∀ v : Fin N → ℝ,
      0 ≤ star v ⬝ᵥ (CarryMovingSigma.sigmaMatrix d 0 N *ᵥ v) := by
    intro hquad
    apply hNbad
    exact Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm, hquad⟩
  push Not at hnotQuad
  obtain ⟨v, hv⟩ := hnotQuad
  have hvneg : v ⬝ᵥ (CarryMovingSigma.sigmaMatrix d 0 N *ᵥ v) < 0 := by
    simpa [Pi.star_apply, star_trivial] using hv
  have hvne : v ≠ 0 := by
    intro hv0
    subst v
    simp at hvneg
  have hvnegH : v ⬝ᵥ (hankelMatrix (completedSigmaLogJet d) N *ᵥ v) < 0 := by
    simpa [completedSigmaLogJet_sigmaMatrix_eq_hankel] using hvneg
  exact ⟨N, hNpos, hNbadH, hNsmallH, v, hvne, hvnegH⟩

/-! The classification above is stated for every real source sequence. The next result
transfers it to the original sigma sequence while retaining the positive-height-zero
hypotheses of the established obstruction theorem. -/

/-- The least failing original sigma Hankel matrix is classified by its actual previous
moment block and its actual next-moment coupling. The zero at positive height and the
nonzero-shift interval remain explicit hypotheses. -/
theorem first_sigma_failure_classification_of_zero
    (d γ : ℝ) (hγ : 0 < γ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ))
    (hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0) :
    ∃ N : ℕ, 0 < N ∧
      (∀ m < N, (hankelMatrix (completedSigmaLogJet d) m).PosSemidef) ∧
      ((∃ w : Fin (N - 1) → ℝ,
          sourceMomentMatrix (completedSigmaLogJet d) 0 (N - 1) *ᵥ w = 0 ∧
            sourceMomentCoupling (completedSigmaLogJet d) 0 (N - 1) ⬝ᵥ w ≠ 0) ∨
        ∃ y : Fin (N - 1) → ℝ,
          sourceMomentMatrix (completedSigmaLogJet d) 0 (N - 1) *ᵥ y =
              sourceMomentCoupling (completedSigmaLogJet d) 0 (N - 1) ∧
            completedSigmaLogJet d (2 * (N - 1)) -
              sourceMomentCoupling (completedSigmaLogJet d) 0 (N - 1) ⬝ᵥ y < 0) := by
  obtain ⟨N, hNpos, _hNbad, hNsmall, _hv⟩ :=
    exists_first_sigma_hankel_failure_of_zero d γ hγ hd₀ hd₁ hzero
  let n := N - 1
  have hn : n + 1 = N := by dsimp [n]; omega
  have hprefix :
      (sourceMomentMatrix (completedSigmaLogJet d) 0 n).PosSemidef := by
    have h := hNsmall n (by dsimp [n]; omega)
    have hmat : sourceMomentMatrix (completedSigmaLogJet d) 0 n =
        hankelMatrix (completedSigmaLogJet d) n := by
      ext i j
      simp [sourceMomentMatrix, hankelMatrix]
    rw [hmat]
    exact h
  have hnext :
      ¬ (sourceMomentMatrix (completedSigmaLogJet d) 0 (n + 1)).PosSemidef := by
    have hmat : sourceMomentMatrix (completedSigmaLogJet d) 0 (n + 1) =
        hankelMatrix (completedSigmaLogJet d) (n + 1) := by
      ext i j
      simp [sourceMomentMatrix, hankelMatrix]
    rw [hmat, hn]
    exact _hNbad
  have hclass := sourceMoment_succ_failure_classification
    (completedSigmaLogJet d) n hprefix hnext
  refine ⟨N, hNpos, hNsmall, ?_⟩
  simpa [n] using hclass

#print axioms exists_first_sigma_hankel_failure_of_zero
#print axioms sourceMoment_succ_failure_classification
#print axioms sourceMoment_size_one_failure_neg_zero
#print axioms first_sigma_failure_classification_of_zero

end CarrySigmaObstruction
