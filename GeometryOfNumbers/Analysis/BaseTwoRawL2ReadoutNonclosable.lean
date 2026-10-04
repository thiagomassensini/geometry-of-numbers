import GeometryOfNumbers.Analysis.BaseTwoRawL2ReadoutObstruction
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # The raw complete-cell edge readout is not closable

Any partial linear operator agreeing on all finite coordinate deltas has a
vertical nonzero graph limit. This excludes only the raw ℓ² readout, not the
explicit boundary Hilbert realization after geometric synthesis.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal Topology
open Filter
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- Normalize the existing signed complete-cell witness to raw output one.
Using N+1 avoids a zero normalization denominator. -/
def baseTwoRawL2NormalizedWitness (N : ℕ) : MaterialEdgeL2 :=
  (((2 * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) • baseTwoRawL2Witness (N + 1)

theorem baseTwoRawL2NormalizedWitness_norm_sq (N : ℕ) :
    ‖baseTwoRawL2NormalizedWitness N‖ ^ 2 = (2 * ((N : ℝ) + 1))⁻¹ := by
  have hp : 0 < 2 * ((N : ℝ) + 1) := by positivity
  rw [baseTwoRawL2NormalizedWitness, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp),
    baseTwoRawL2Witness_norm_sq]
  push_cast
  field_simp

/-- Input tends to zero in ℓ² although its raw finite-support output is one. -/
theorem baseTwoRawL2NormalizedWitness_tendsto :
    Tendsto baseTwoRawL2NormalizedWitness atTop (𝓝 (0 : MaterialEdgeL2)) := by
  have hn : Tendsto (fun N : ℕ => 2 * ((N : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_mono (fun N => by have := Nat.cast_nonneg (α := ℝ) N; linarith)
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hi := tendsto_inv_atTop_zero.comp hn
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hi
  have he : (fun N : ℕ => Real.sqrt ((2 * ((N : ℝ) + 1))⁻¹)) =
      fun N => ‖baseTwoRawL2NormalizedWitness N‖ := by
    funext N
    rw [← baseTwoRawL2NormalizedWitness_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  simp only [Function.comp_def] at hs
  rw [he] at hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa using hs

/-- Every partial linear extension agreeing on deltas contains the exact
finite witness graph points. No continuity assumption is used. -/
theorem baseTwoRawL2Witness_mem_graph
    (T : MaterialEdgeL2 →ₗ.[ℂ] ℂ)
    (hT : ∀ n : ℕ, (lp.single 2 n (1 : ℂ), baseTwoRawEdgeCoefficient n) ∈ T.graph)
    (N : ℕ) : (baseTwoRawL2Witness N, ((2 * N : ℕ) : ℂ)) ∈ T.graph := by
  classical
  have hs (s : Finset ℕ) :
      (∑ n ∈ s, lp.single 2 n (baseTwoRawEdgeCoefficient n),
        ∑ n ∈ s, baseTwoRawEdgeCoefficient n * baseTwoRawEdgeCoefficient n) ∈ T.graph := by
    have he : (∑ n ∈ s, lp.single 2 n (baseTwoRawEdgeCoefficient n),
        ∑ n ∈ s, baseTwoRawEdgeCoefficient n * baseTwoRawEdgeCoefficient n) =
        ∑ n ∈ s, (lp.single 2 n (baseTwoRawEdgeCoefficient n),
          baseTwoRawEdgeCoefficient n * baseTwoRawEdgeCoefficient n) := by
      apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum]
    rw [he]
    apply Submodule.sum_mem
    intro n _
    have h := T.graph.smul_mem (baseTwoRawEdgeCoefficient n) (hT n)
    convert h using 1
    ext j
    · by_cases hj : j = n <;> simp [lp.single_apply, hj]
    · rfl
  let s := ((Finset.range N).product (Finset.univ : Finset (Fin 2))).image baseTwoSignedEdge
  have he : (∑ n ∈ s, baseTwoRawEdgeCoefficient n * baseTwoRawEdgeCoefficient n) =
      ((2 * N : ℕ) : ℂ) := by
    dsimp [s]
    rw [Finset.sum_image (fun i _ j _ hij => baseTwoSignedEdge_injective hij)]
    simp only [baseTwoRawEdgeCoefficient_signedEdge]
    have hu (i : ℕ × Fin 2) :
        (if i.2 = 0 then -1 else 1 : ℂ) * (if i.2 = 0 then -1 else 1) = 1 := by
      rcases i with ⟨i, a⟩
      fin_cases a <;> norm_num
    simp_rw [hu]
    simp [Finset.card_product, Nat.cast_mul, mul_comm]
  change (∑ n ∈ s, lp.single 2 n (baseTwoRawEdgeCoefficient n),
    ((2 * N : ℕ) : ℂ)) ∈ T.graph
  rw [← he]
  exact hs s

theorem baseTwoRawL2NormalizedWitness_mem_graph
    (T : MaterialEdgeL2 →ₗ.[ℂ] ℂ)
    (hT : ∀ n : ℕ, (lp.single 2 n (1 : ℂ), baseTwoRawEdgeCoefficient n) ∈ T.graph)
    (N : ℕ) : (baseTwoRawL2NormalizedWitness N, (1 : ℂ)) ∈ T.graph := by
  have hp : (2 * ((N : ℝ) + 1)) ≠ 0 := by positivity
  have h := T.graph.smul_mem (((2 * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ)
    (baseTwoRawL2Witness_mem_graph T hT (N + 1))
  convert h using 1
  simp only [Prod.smul_mk, smul_eq_mul]
  congr 1
  push_cast
  norm_cast
  field_simp

/-- Literal graph-closure obstruction: (0,1) belongs to the closure. -/
theorem baseTwoRawL2Readout_vertical_graph_limit
    (T : MaterialEdgeL2 →ₗ.[ℂ] ℂ)
    (hT : ∀ n : ℕ, (lp.single 2 n (1 : ℂ), baseTwoRawEdgeCoefficient n) ∈ T.graph) :
    (0, (1 : ℂ)) ∈ T.graph.topologicalClosure := by
  have ht := baseTwoRawL2NormalizedWitness_tendsto.prodMk_nhds
    (tendsto_const_nhds (x := (1 : ℂ)))
  exact T.graph.isClosed_topologicalClosure.mem_of_tendsto ht
    (Eventually.of_forall fun N => T.graph.le_topologicalClosure
      (baseTwoRawL2NormalizedWitness_mem_graph T hT N))

/-- No partial operator agreeing with the raw readout on finite supports can
be closable. In particular the densely defined finite-support operator is not. -/
theorem baseTwoRawL2Readout_not_closable
    (T : MaterialEdgeL2 →ₗ.[ℂ] ℂ)
    (hT : ∀ n : ℕ, (lp.single 2 n (1 : ℂ), baseTwoRawEdgeCoefficient n) ∈ T.graph) :
    ¬ T.IsClosable := by
  rintro ⟨Q, hQ⟩
  have hv := baseTwoRawL2Readout_vertical_graph_limit T hT
  rw [hQ] at hv
  have hz := Q.graph_fst_eq_zero_snd hv rfl
  norm_num at hz

end GeometryOfNumbers.Analysis.BaseTwoCompletion
