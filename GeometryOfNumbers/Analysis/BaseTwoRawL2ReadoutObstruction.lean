import GeometryOfNumbers.Analysis.BaseTwoCompletedGradientSignalLift
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # The complete C2 edge readout is not bounded on raw material ℓ²

This excludes only a continuous extension agreeing on every finite-support
input. It does not exclude a geometrically completed boundary lift defined
on the stronger seeded ℓ¹ source or a source-specific boundary realization.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

abbrev MaterialEdgeL2 : Type := ℓ²(ℕ, ℂ)

/-- The two actual edges of the existing base-two cell. -/
def baseTwoSignedEdge (i : ℕ × Fin 2) : ℕ :=
  if i.2 = 0 then baseTwoCellLeftEdge i.1 else baseTwoCellRightEdge i.1

theorem baseTwoSignedEdge_injective : Function.Injective baseTwoSignedEdge := by
  intro i j h
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [baseTwoSignedEdge] at h ⊢ <;> omega

/-- Material-edge coefficients; no vertical-depth meaning is assigned. -/
def baseTwoRawEdgeCoefficient (n : ℕ) : ℂ :=
  if n % 4 = 2 then -1 else if n % 4 = 3 then 1 else 0

theorem baseTwoRawEdgeCoefficient_signedEdge (i : ℕ × Fin 2) :
    baseTwoRawEdgeCoefficient (baseTwoSignedEdge i) =
      if i.2 = 0 then -1 else 1 := by
  rcases i with ⟨i, a⟩
  fin_cases a <;> simp [baseTwoRawEdgeCoefficient, baseTwoSignedEdge, Nat.add_mod]

/-- The coefficient sequence is exactly the already proved seeded ℓ¹
readout on coordinate deltas, not a parallel choice of functional. -/
theorem baseTwoCompletedUndressedReadout_single (n : ℕ) :
    baseTwoCompletedUndressedReadout (0, (lp.single 1 n (1 : ℂ) : MaterialGradientL1)) =
      baseTwoRawEdgeCoefficient n := by
  rw [baseTwoCompletedUndressedReadout_apply]
  simp only [zero_add, lp.single_apply, baseTwoCellLeftEdge_eq, baseTwoCellRightEdge_eq]
  rw [tsum_eq_single (n / 4) (fun k hk => by
    have hl : n ≠ 4*k+2 := by omega
    have hr : n ≠ 4*k+3 := by omega
    simp only [Pi.single_eq_of_ne (Ne.symm hl), Pi.single_eq_of_ne (Ne.symm hr), sub_self])]
  by_cases hl : n % 4 = 2
  · have hnl : n = 4*(n/4)+2 := by omega
    have hnr : n ≠ 4*(n/4)+3 := by omega
    simp only [baseTwoRawEdgeCoefficient, if_pos hl, Pi.single_apply, if_pos hnl.symm, if_neg (Ne.symm hnr), zero_sub]
  · by_cases hr : n % 4 = 3
    · have hnr : n = 4*(n/4)+3 := by omega
      have hnl : n ≠ 4*(n/4)+2 := by omega
      simp only [baseTwoRawEdgeCoefficient, if_neg hl, if_pos hr, Pi.single_apply, if_pos hnr.symm, if_neg (Ne.symm hnl), sub_zero]
    · have hnl : n ≠ 4*(n/4)+2 := by omega
      have hnr : n ≠ 4*(n/4)+3 := by omega
      simp only [baseTwoRawEdgeCoefficient, if_neg hl, if_neg hr, Pi.single_eq_of_ne (Ne.symm hnl), Pi.single_eq_of_ne (Ne.symm hnr), sub_self]

private def edgePrefix (N : ℕ) : Finset ℕ :=
  ((Finset.range N).product (Finset.univ : Finset (Fin 2))).image baseTwoSignedEdge

/-- Explicit finite-support witness: -1 on left edges and +1 on right edges
of the first N complete cells, zero elsewhere. -/
def baseTwoRawL2Witness (N : ℕ) : MaterialEdgeL2 :=
  ∑ n ∈ edgePrefix N, lp.single 2 n (baseTwoRawEdgeCoefficient n)

theorem baseTwoRawL2Witness_apply (N n : ℕ) :
    baseTwoRawL2Witness N n =
      if n ∈ edgePrefix N then baseTwoRawEdgeCoefficient n else 0 := by
  simp only [baseTwoRawL2Witness, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  simp

theorem baseTwoRawL2Witness_signedEdge (N : ℕ) (i : ℕ × Fin 2) :
    baseTwoRawL2Witness N (baseTwoSignedEdge i) =
      if i.1 < N then (if i.2 = 0 then -1 else 1) else 0 := by
  have hm : baseTwoSignedEdge i ∈ edgePrefix N ↔ i.1 < N := by
    rw [edgePrefix, Finset.mem_image]
    constructor
    · rintro ⟨j, hj, he⟩
      have hij : j = i := baseTwoSignedEdge_injective he
      subst j
      exact Finset.mem_range.mp (Finset.mem_product.mp hj).1
    · intro hi
      exact ⟨i, Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_univ _⟩, rfl⟩
  simp only [baseTwoRawL2Witness_apply, hm, baseTwoRawEdgeCoefficient_signedEdge]

theorem baseTwoRawL2Witness_norm_sq (N : ℕ) :
    ‖baseTwoRawL2Witness N‖ ^ 2 = 2 * (N : ℝ) := by
  have h := lp.norm_sum_single (E := fun _ : ℕ => ℂ)
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) baseTwoRawEdgeCoefficient (edgePrefix N)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [baseTwoRawL2Witness, h]
  rw [edgePrefix, Finset.sum_image (fun i _ j _ hij => baseTwoSignedEdge_injective hij)]
  simp only [baseTwoRawEdgeCoefficient_signedEdge]
  have hu (i : ℕ × Fin 2) : ‖(if i.2 = 0 then -1 else 1 : ℂ)‖ ^ 2 = 1 := by
    rcases i with ⟨i, a⟩
    fin_cases a <;> norm_num
  simp_rw [hu]
  simp [Finset.card_product, mul_comm]

theorem baseTwoRawL2Witness_norm (N : ℕ) :
    ‖baseTwoRawL2Witness N‖ = Real.sqrt (2 * (N : ℝ)) := by
  rw [← baseTwoRawL2Witness_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem baseTwoRawL2Witness_readout (R : MaterialEdgeL2 →L[ℂ] ℂ)
    (hR : ∀ n : ℕ, R (lp.single 2 n (1 : ℂ)) = baseTwoRawEdgeCoefficient n)
    (N : ℕ) : R (baseTwoRawL2Witness N) = (2 * N : ℕ) := by
  have hs (n : ℕ) :
      R (lp.single 2 n (baseTwoRawEdgeCoefficient n)) =
        baseTwoRawEdgeCoefficient n * baseTwoRawEdgeCoefficient n := by
    have hv : lp.single 2 n (baseTwoRawEdgeCoefficient n) =
        baseTwoRawEdgeCoefficient n • (lp.single 2 n (1 : ℂ) : MaterialEdgeL2) := by
      ext j
      by_cases h : j = n <;> simp [lp.single_apply, h]
    rw [hv, R.map_smul, hR, smul_eq_mul]
  rw [baseTwoRawL2Witness, map_sum]
  simp only [hs]
  rw [edgePrefix, Finset.sum_image (fun i _ j _ hij => baseTwoSignedEdge_injective hij)]
  simp only [baseTwoRawEdgeCoefficient_signedEdge]
  have hu (i : ℕ × Fin 2) :
      (if i.2 = 0 then -1 else 1 : ℂ) * (if i.2 = 0 then -1 else 1) = 1 := by
    rcases i with ⟨i, a⟩
    fin_cases a <;> norm_num
  simp_rw [hu]
  simp [Finset.card_product, Nat.cast_mul, mul_comm]

/-- No bounded raw ℓ² extension even agrees on the coordinate deltas. Hence
agreement with the edge sum on all finitely supported sequences is impossible. -/
theorem baseTwoRawL2Readout_not_exists :
    ¬ ∃ R : MaterialEdgeL2 →L[ℂ] ℂ,
      ∀ n : ℕ, R (lp.single 2 n (1 : ℂ)) = baseTwoRawEdgeCoefficient n := by
  rintro ⟨R, hR⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (‖R‖ ^ 2 + 1)
  have hNpos : (0 : ℝ) < N := by nlinarith [sq_nonneg ‖R‖]
  have hb := R.le_opNorm (baseTwoRawL2Witness N)
  rw [baseTwoRawL2Witness_readout R hR N] at hb
  have hb' : 2 * (N : ℝ) ≤ ‖R‖ * ‖baseTwoRawL2Witness N‖ := by
    simpa using hb
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ 2*(N:ℝ)) hb'
  have hn := baseTwoRawL2Witness_norm_sq N
  nlinarith [sq_nonneg ‖R‖]

/-- This excludes extension of the current ℓ¹ readout itself, already on
finite-support deltas. Linear agreement on all finite supports implies these
identities and therefore cannot hold. -/
theorem baseTwoCompletedReadout_no_rawL2_extension :
    ¬ ∃ R : MaterialEdgeL2 →L[ℂ] ℂ, ∀ n : ℕ,
      R (lp.single 2 n (1 : ℂ)) = baseTwoCompletedUndressedReadout
        (0, (lp.single 1 n (1 : ℂ) : MaterialGradientL1)) := by
  rintro ⟨R, hR⟩
  apply baseTwoRawL2Readout_not_exists
  exact ⟨R, fun n => (hR n).trans (baseTwoCompletedUndressedReadout_single n)⟩

/-- Any bounded Hilbert channel transform followed by a bounded boundary
readout would yield the forbidden raw extension. This is not a no-go for
transforms on the stronger ℓ¹ domain with separately derived boundary data. -/
theorem baseTwoRawL2_no_bounded_boundary_factorization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : MaterialEdgeL2 →L[ℂ] E) (beta : E →L[ℂ] ℂ) :
    ¬ (∀ n : ℕ, beta (T (lp.single 2 n (1 : ℂ))) = baseTwoRawEdgeCoefficient n) := by
  intro h
  exact baseTwoRawL2Readout_not_exists ⟨beta.comp T, h⟩

end GeometryOfNumbers.Analysis.BaseTwoCompletion
