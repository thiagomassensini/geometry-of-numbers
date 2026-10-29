import DiscreteParts

/-! Prefix/tail accounting of the ORIGINAL full Green pair. Cutoffs are
observations AFTER source synthesis, never replacements of a clock domain.
Both ordered pairings and the same hidden complement are retained. -/
namespace CarryMaterialParts
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryNativePhase CarryMixedGreen CarryCompletedGreenBalance
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev MaterialPair := MaterialCarrier × MaterialCarrier

def interiorTerm (x y : MaterialPair) (n : ℕ) : ℂ :=
  conj (x.2.snd.fst n)*y.1.snd.fst n-conj (x.1.snd.fst n)*y.2.snd.fst n

def boundaryGreen (x y : MaterialPair) : ℂ :=
  conj x.2.fst*y.1.fst-conj x.1.fst*y.2.fst +
    conj x.2.snd.snd*y.1.snd.snd-conj x.1.snd.snd*y.2.snd.snd

def prefixGreen (N : ℕ) (x y : MaterialPair) : ℂ :=
  boundaryGreen x y+∑ n ∈ Finset.range N, interiorTerm x y n

def tailGreen (N : ℕ) (x y : MaterialPair) : ℂ :=
  ∑' n, interiorTerm x y (n+N)

theorem interior_summable (x y : MaterialPair) : Summable (interiorTerm x y) := by
  have h := (lp.summable_inner (𝕜 := ℂ) x.2.snd.fst y.1.snd.fst).sub
    (lp.summable_inner (𝕜 := ℂ) x.1.snd.fst y.2.snd.fst)
  change Summable (fun n => conj (x.2.snd.fst n)*y.1.snd.fst n-
    conj (x.1.snd.fst n)*y.2.snd.fst n)
  apply h.congr
  intro n
  simp only [RCLike.inner_apply]
  ring

theorem full_green_series (x y : MaterialPair) :
    carryMaterialPairGreen x y = boundaryGreen x y+∑' n, interiorTerm x y n := by
  have ha := lp.summable_inner (𝕜 := ℂ) x.2.snd.fst y.1.snd.fst
  have hb := lp.summable_inner (𝕜 := ℂ) x.1.snd.fst y.2.snd.fst
  rw [carryMaterialPairGreen]
  simp only [WithLp.prod_inner_apply, lp.inner_eq_tsum, RCLike.inner_apply]
  rw [show (∑' n, interiorTerm x y n) =
      inner ℂ x.2.snd.fst y.1.snd.fst-inner ℂ x.1.snd.fst y.2.snd.fst by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← ha.tsum_sub hb]
    congr 1
    funext n
    simp only [interiorTerm, RCLike.inner_apply]
    ring]
  simp only [boundaryGreen, lp.inner_eq_tsum, RCLike.inner_apply]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

theorem full_green_head_tail (N : ℕ) (x y : MaterialPair) :
    carryMaterialPairGreen x y = prefixGreen N x y+tailGreen N x y := by
  rw [full_green_series]
  simpa only [prefixGreen, tailGreen, add_assoc] using congrArg (fun z : ℂ => boundaryGreen x y+z)
    ((interior_summable x y).sum_add_tsum_nat_add N).symm

/-- The hidden readout complement retains the EXACT SAME interior in both slots. -/
theorem hidden_interior_exact (x y : MaterialPair) (n : ℕ) :
    interiorTerm (carryMaterialPairComplement x) (carryMaterialPairComplement y) n =
      interiorTerm x y n := by
  simp only [interiorTerm, carryMaterialPairComplement, carryMaterialReadoutComplement_apply]
  rfl

theorem hidden_tail_exact (N : ℕ) (x y : MaterialPair) :
    tailGreen N (carryMaterialPairComplement x) (carryMaterialPairComplement y) = tailGreen N x y := by
  simp only [tailGreen, hidden_interior_exact]

theorem finite_hidden_cancellation (N : ℕ) (x y : MaterialPair) :
    prefixGreen N x y-prefixGreen N (carryMaterialPairComplement x) (carryMaterialPairComplement y) =
      boundaryGreen x y-boundaryGreen (carryMaterialPairComplement x) (carryMaterialPairComplement y) := by
  simp only [prefixGreen, hidden_interior_exact]
  ring

/-- No tail estimate, limiting interchange or sign assumption is needed. -/
theorem full_hidden_equals_finite (N : ℕ) (x y : MaterialPair) :
    carryMaterialPairGreen x y-
      carryMaterialPairGreen (carryMaterialPairComplement x) (carryMaterialPairComplement y) =
      prefixGreen N x y-prefixGreen N (carryMaterialPairComplement x) (carryMaterialPairComplement y) := by
  rw [full_green_head_tail N x y,
    full_green_head_tail N (carryMaterialPairComplement x) (carryMaterialPairComplement y), hidden_tail_exact]
  ring

/-- This boundary-only identity is a polarized consequence of the existing
readout ledger. New finite-cutoff accounting above exposes its bulk cancellation. -/
theorem boundary_readout_exact (x y : MaterialPair) :
    boundaryGreen x y-boundaryGreen (carryMaterialPairComplement x) (carryMaterialPairComplement y) =
      (1/2:ℂ)*carryMaterialPairGreen (carryMaterialPairReadout x) (carryMaterialPairReadout y) := by
  have h := carryMaterialPairGreen_readout_ledger x y
  have hh : carryMaterialPairGreen x y-
      carryMaterialPairGreen (carryMaterialPairComplement x) (carryMaterialPairComplement y) =
      (1/2:ℂ)*carryMaterialPairGreen (carryMaterialPairReadout x) (carryMaterialPairReadout y) := by
    linear_combination h
  rw [full_hidden_equals_finite 0 x y, finite_hidden_cancellation] at hh
  exact hh

end
end CarryMaterialParts
