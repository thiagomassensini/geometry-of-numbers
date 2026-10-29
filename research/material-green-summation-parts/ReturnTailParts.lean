import NativeGreenParts
import GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen

/-! Exact two-cutoff ledger for the still-retained GLOBAL cell return.
Material-interior cutoff N and whole-cell cutoffs M,L are distinct.
The companion subtraction is kept in every ordered head/tail term. -/
namespace CarryMaterialParts
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCompleteTfvd CarryForcingResidual CarryNativePhase CarryMixedGreen CarryCompletedGreenBalance
open CarryMaterialResponseComparison Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Literal original reduced boundary balance, not a new positive metric. -/
def reducedCellForm (t u : ℝ) (x y : ℂ × ℂ) : ℂ :=
  ((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*carryMaterialPairGreen x y-
    (((carryMaterialResponseScale*(u-t):ℝ):ℂ)/2)*conj x.1*y.1

theorem reduced_cell_four_terms (t u : ℝ) (x a y b : ℂ × ℂ) :
    reducedCellForm t u (x+a) (y+b) = reducedCellForm t u x y+
      reducedCellForm t u x b+reducedCellForm t u a y+reducedCellForm t u a b := by
  simp only [reducedCellForm, carryMaterialPairGreen, Prod.fst_add, Prod.snd_add,
    inner_add_left, inner_add_right, map_add]
  ring

theorem reduced_return_cell_form (eta t u : ℝ) :
    carryValveReducedReturnBalance eta t u =
      reducedCellForm t u (carryValveScalarPair eta t) (carryValveScalarPair eta u) := by
  rw [carryValveReducedReturnBalance, carryValveReturnGreen_eq]
  simp only [reducedCellForm, carryMaterialPairGreen, carryValveScalarPair, RCLike.inner_apply]
  ring

theorem reduced_prefix_cell_form (eta t u : ℝ) (M L : ℕ) :
    carryValvePrefixReducedBalance eta M L t u =
      reducedCellForm t u (carryValvePrefixPair eta M t) (carryValvePrefixPair eta L u) := rfl

/-- Both cross terms and the signed companion subtraction occur even in
head/tail and tail/tail terms. No positivity or margin is an input. -/
theorem reduced_return_four_cells (eta : ℝ) (heta : eta ≠ 0) (M L : ℕ) (t u : ℝ) :
    carryValveReducedReturnBalance eta t u =
      reducedCellForm t u (carryValvePrefixPair eta M t) (carryValvePrefixPair eta L u)+
      reducedCellForm t u (carryValvePrefixPair eta M t) (carryValveTailPair eta L u)+
      reducedCellForm t u (carryValveTailPair eta M t) (carryValvePrefixPair eta L u)+
      reducedCellForm t u (carryValveTailPair eta M t) (carryValveTailPair eta L u) := by
  rw [reduced_return_cell_form, carryValvePair_prefix_tail eta heta M t,
    carryValvePair_prefix_tail eta heta L u, reduced_cell_four_terms]

/-- This is the exact remainder that survives the material-bulk cancellation.
Zero material tail does not remove any of these GLOBAL return-tail crosses. -/
theorem reduced_return_tail_defect (eta : ℝ) (heta : eta ≠ 0) (M L : ℕ) (t u : ℝ) :
    carryValveReducedReturnBalance eta t u-carryValvePrefixReducedBalance eta M L t u =
      reducedCellForm t u (carryValvePrefixPair eta M t) (carryValveTailPair eta L u)+
      reducedCellForm t u (carryValveTailPair eta M t) (carryValvePrefixPair eta L u)+
      reducedCellForm t u (carryValveTailPair eta M t) (carryValveTailPair eta L u) := by
  rw [reduced_return_four_cells eta heta M L t u, reduced_prefix_cell_form]
  ring

/-- Exact finite material cutoff on the SAME original reduced source. -/
def nativeBalancedPrefix (N : ℕ) (t u : ℝ) : ℂ :=
  prefixGreen N (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u)-
    prefixGreen N (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
      (carryMaterialPairComplement (carryMaterialReducedCompanionPair u))

theorem native_material_cell_balance (eta : ℝ) (heta : eta ≠ 0) (N : ℕ) (t u : ℝ) :
    nativeBalancedPrefix N t u = carryValveReducedReturnBalance eta t u := by
  rw [nativeBalancedPrefix, ← full_hidden_equals_finite N,
    carryValveReducedReturnBalance_physical eta heta t u]

/-- Discrete source kernels are identical at every material observation
cutoff. This does not claim equality of a state with its scalar readout. -/
theorem native_balanced_cutoff_independent (N M : ℕ) :
    nativeBalancedPrefix N = nativeBalancedPrefix M := by
  funext t u
  simp only [nativeBalancedPrefix, finite_hidden_cancellation]

/-- Two independent jets of the COMPLETE numerator, not an isolated channel
or an asserted Hilbert Gram of canonical moments. -/
theorem native_numerator_jets_cutoff (N M p q : ℕ) :
    carryKernelJet (nativeBalancedPrefix N) p q = carryKernelJet (nativeBalancedPrefix M) p q := by
  rw [native_balanced_cutoff_independent N M]

/-- The original source factor identifies the SAME canonical residual after
summation by parts, for every material cutoff, including N=0. -/
theorem native_cutoff_canonical_factor :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ N : ℕ, ∀ t ∈ U, ∀ u ∈ U,
      nativeBalancedPrefix N t u = ((u-t:ℝ):ℂ)*completedCoefficient t u := by
  let eta := criticalVerticalAmplitudeRatio 2 (by norm_num)
  have hp : 0 < eta := criticalVerticalAmplitudeRatio_pos 2 _
  have hl : eta < 1 := criticalVerticalAmplitudeRatio_lt_one 2 (by norm_num)
  obtain ⟨U,ho,hz,h⟩ := tfvd_whole_factor eta hp hl
  refine ⟨U,ho,hz,?_⟩
  intro N t ht u hu
  rw [nativeBalancedPrefix, ← native_cutoff_boundary_exact eta hp hl N]
  exact h t ht u hu

/-- The normalization is the literal original regular source chart. It is
performed after the complete source and all Green compensators are retained. -/
theorem native_cutoff_canonical_regular :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ N : ℕ, ∀ t ∈ U, ∀ u ∈ U,
      t ≠ 0 → u ≠ 0 → u ≠ t → baseTwoCanonicalResponse t ≠ 0 → baseTwoCanonicalResponse u ≠ 0 →
      nativeBalancedPrefix N t u/
        (((u-t:ℝ):ℂ)*(2:ℂ)*((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*
          conj (baseTwoCanonicalResponse t)*baseTwoCanonicalResponse u) =
        (carryMaterialRealResidual t u:ℂ) := by
  let eta := criticalVerticalAmplitudeRatio 2 (by norm_num)
  have hp : 0 < eta := criticalVerticalAmplitudeRatio_pos 2 _
  have hl : eta < 1 := criticalVerticalAmplitudeRatio_lt_one 2 (by norm_num)
  obtain ⟨U,ho,hz,h⟩ := tfvd_native_residual_regular eta hp hl
  refine ⟨U,ho,hz,?_⟩
  intro N t ht u hu ht0 hu0 hne hFt hFu
  rw [nativeBalancedPrefix, ← native_cutoff_boundary_exact eta hp hl N]
  exact h t ht u hu ht0 hu0 hne hFt hFu

end
end CarryMaterialParts
