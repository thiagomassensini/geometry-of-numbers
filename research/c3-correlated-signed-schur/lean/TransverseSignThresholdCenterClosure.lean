import Mathlib.Topology.Constructions
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# A divergent first-failure threshold implies positivity at the center
# only when the threshold is defined for FULL finite quadratic forms.

This is an abstract continuity/closed-cone lemma, NOT a proof of
threshold divergence for C2 nor a theorem that 2x2 windows control
all Hankel PSD.

No RH, zeros or infinite-dimensional positivity premise.
-/

namespace CarryWheelNativeSignedGate

open Filter Topology Matrix
open scoped Matrix

noncomputable section

/-- If a continuous real signed observable is nonnegative for all
sufficiently small NONZERO transverse shifts, the center is nonnegative.
This is the limit mechanism behind a diverging failure threshold. -/
theorem center_nonneg_of_punctured_transverse_nonneg
    (q : ℝ → ℝ) (hq : ContinuousAt q 0)
    (hnear : ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ,
      0 < |d| → |d| < δ → 0 ≤ q d) :
    0 ≤ q 0 := by
  obtain ⟨δ, hδ, hd⟩ := hnear
  let t : ℕ → ℝ := fun k => (1 : ℝ) / ((k : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 (0 : ℝ)) := by
    simpa only [t] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hAbs : Tendsto (fun k => |t k|) atTop (𝓝 (0 : ℝ)) := by
    simpa using ht.abs
  have hsmall : ∀ᶠ k in atTop, |t k| < δ :=
    hAbs.eventually (eventually_lt_nhds hδ)
  have hpositive : ∀ᶠ k in atTop, 0 ≤ q (t k) := by
    filter_upwards [hsmall] with k hk
    have htpos : 0 < |t k| := by
      dsimp [t]
      positivity
    exact hd (t k) htpos hk
  have hlimit : q 0 ∈ Set.Ici (0 : ℝ) :=
    isClosed_Ici.mem_of_tendsto (hq.tendsto.comp ht) hpositive
  exact hlimit


/-- A diverging first NEGATIVE FULL-HANKEL DIMENSION delivers
central PSD when each fixed finite matrix is continuous. The
hypothesis is genuinely stronger than a first negative 2x2
shifted-window index tending to infinity. -/
theorem center_matrix_posSemidef_of_punctured_posSemidef
    (N : ℕ) (A : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hcont : ContinuousAt A 0)
    (hHerm : (A 0).IsHermitian)
    (hnear : ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ,
      0 < |d| → |d| < δ → (A d).PosSemidef) :
    (A 0).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro x
  let q : ℝ → ℝ := fun d => star x ⬝ᵥ (A d *ᵥ x)
  have hqcont : ContinuousAt q 0 := by
    let ev : Matrix (Fin N) (Fin N) ℝ → ℝ :=
      fun M => star x ⬝ᵥ (M *ᵥ x)
    have hev : Continuous ev := by
      dsimp [ev, Matrix.mulVec, dotProduct]
      fun_prop
    exact hev.continuousAt.comp hcont
  apply center_nonneg_of_punctured_transverse_nonneg q hqcont
  obtain ⟨δ, hδ, hsmall⟩ := hnear
  refine ⟨δ, hδ, ?_⟩
  intro d hd0 hdδ
  exact (hsmall d hd0 hdδ).dotProduct_mulVec_nonneg x


end
end CarryWheelNativeSignedGate
