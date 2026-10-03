import GeometryOfNumbers.Analysis.PrimeResidualDepthCrosswalk

/-!
# Intrinsic depth does not equal a positive-vertex sample index

This audit adds no source, diagonal, encoder, or positional depth definition.
It uses the existing residual-depth/factorization crosswalk. The sample index
2 labels material quantity 3, whose binary carry threshold is only zero.
An arbitrary positional chart window can still be chosen at depth 2; the
theorems below concern intrinsic zero-residual depth, not such a choice.
-/

namespace GeometryOfNumbers.Analysis

theorem sampleTwo_materialThree_binaryDepth_iff (k : ℕ) :
    Geometry.HasCarryDepthAtLeast 2 (2 + 1) k ↔ k = 0 := by
  rw [primeResidualDepth_iff_le_factorization Nat.prime_two (by decide)]
  change k ≤ (3 : ℕ).factorization 2 ↔ k = 0
  rw [Nat.Prime.factorization (by decide : Nat.Prime 3)]
  simp

/-- It is false that every sample index is a supported intrinsic binary depth
of its material point n+1. No theorem of nonexistence of arbitrary encoders
or chart reindexings is asserted. -/
theorem materialSampleIndex_not_intrinsicBinaryDepth :
    ¬ ∀ n : ℕ, Geometry.HasCarryDepthAtLeast 2 (n + 1) n := by
  intro h
  have hz := (sampleTwo_materialThree_binaryDepth_iff 2).mp (h 2)
  cases hz

end GeometryOfNumbers.Analysis
