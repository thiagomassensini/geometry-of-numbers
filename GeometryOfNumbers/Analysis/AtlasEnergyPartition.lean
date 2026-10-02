import GeometryOfNumbers.Analysis.CenterLegCameraForm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Finprod

/-!
# An explicit interface for coordinate energy distribution between bases

This is a NEW semantic input, not a partition derived from the residual tower.
A finite support envelope is supplied at each input coordinate; nonnegative
weights vanish outside it and sum to one. No rule selects these weights.
Base labels range over all natural bases at least two, without primality.
They label weighted cameras, not a newly proved carry realization in each base.
No equation identifying their label with 2*half+1 is assumed.

The input coordinates resolved here are the existing positive radii 1,...,half.
Every active base retains a separate real-plane state in each such channel.
The resulting finite-coordinate energy identity uses x²+y², not a bundled norm.
No infinite-input summability or completion is asserted.
-/

namespace GeometryOfNumbers.Analysis

open Geometry
open scoped BigOperators

noncomputable section

abbrev AtlasBase := {b : Nat // 2 ≤ b}

/-- Admissible transport DATA. Canonical selection from carry remains open.
The support is an envelope; exact nonzero support need not be supplied. -/
structure AdmissibleAtlasPartition where
  weight : AtlasBase → Nat → ℝ
  support : Nat → Finset AtlasBase
  nonneg : ∀ b n, 0 ≤ weight b n
  off_support : ∀ b n, b ∉ support n → weight b n = 0
  sum_eq_one : ∀ n, ∑ b ∈ support n, weight b n = 1

theorem atlasPartition_support_finite (P : AdmissibleAtlasPartition) (n : Nat) :
    (Function.support (fun b => P.weight b n)).Finite := by
  apply (P.support n).finite_toSet.subset
  intro b hb
  by_contra hnot
  exact hb (P.off_support b n hnot)

/-- Literal all-base summation is finite at each coordinate. -/
theorem atlasPartition_finsum_eq_one (P : AdmissibleAtlasPartition) (n : Nat) :
    (∑ᶠ b : AtlasBase, P.weight b n) = 1 := by
  rw [finsum_eq_sum_of_support_subset _ (s := P.support n) (by
    intro b hb
    by_contra hnot
    exact hb (P.off_support b n hnot))]
  exact P.sum_eq_one n

theorem atlasPartition_support_nonempty (P : AdmissibleAtlasPartition) (n : Nat) :
    (P.support n).Nonempty := by
  by_contra h
  have hz := Finset.not_nonempty_iff_eq_empty.mp h
  have hu := P.sum_eq_one n
  simp [hz] at hu

/-- The finite union required by the already existing radius enumeration. -/
def atlasActiveBases (P : AdmissibleAtlasPartition) : Nat → Finset AtlasBase
  | 0 => ∅
  | half + 1 => atlasActiveBases P half ∪ P.support (half + 1)

theorem atlasPartition_support_subset_active (P : AdmissibleAtlasPartition)
    (half n : Nat) (hn : 1 ≤ n) (hbound : n ≤ half) :
    P.support n ⊆ atlasActiveBases P half := by
  induction half with
  | zero => omega
  | succ half ih =>
    by_cases htop : n = half + 1
    · subst n
      exact Finset.subset_union_right
    · exact (ih (by omega)).trans Finset.subset_union_left

theorem atlasPartition_sum_active_eq_one (P : AdmissibleAtlasPartition)
    (half n : Nat) (hn : 1 ≤ n) (hbound : n ≤ half) :
    ∑ b ∈ atlasActiveBases P half, P.weight b n = 1 := by
  rw [← P.sum_eq_one n]
  symm
  exact Finset.sum_subset (atlasPartition_support_subset_active P half n hn hbound)
    (fun b _ hnot => P.off_support b n hnot)

def atlasCoordinate (P : AdmissibleAtlasPartition) (b : AtlasBase)
    (n : Nat) (v : RealPlaneState) : RealPlaneState :=
  scaleRealPlane (Real.sqrt (P.weight b n)) v

theorem atlasCoordinate_energy (P : AdmissibleAtlasPartition) (b : AtlasBase)
    (n : Nat) (v : RealPlaneState) :
    realPlaneEnergy (atlasCoordinate P b n v) = P.weight b n * realPlaneEnergy v := by
  rw [atlasCoordinate, scaleRealPlane_energy, Real.sq_sqrt (P.nonneg b n)]

theorem atlasCoordinate_off_support (P : AdmissibleAtlasPartition) (b : AtlasBase)
    (n : Nat) (v : RealPlaneState) (hb : b ∉ P.support n) :
    atlasCoordinate P b n v = (0, 0) := by
  simp [atlasCoordinate, P.off_support b n hb, scaleRealPlane]

/-- Pointwise conservation is derived from the partition, not an energy field. -/
theorem atlasCoordinate_energy_sum (P : AdmissibleAtlasPartition) (n : Nat)
    (v : RealPlaneState) :
    ∑ b ∈ P.support n, realPlaneEnergy (atlasCoordinate P b n v) = realPlaneEnergy v := by
  simp_rw [atlasCoordinate_energy]
  rw [← Finset.sum_mul, P.sum_eq_one, one_mul]

theorem atlasCoordinate_energy_finsum (P : AdmissibleAtlasPartition) (n : Nat)
    (v : RealPlaneState) :
    (∑ᶠ b : AtlasBase, realPlaneEnergy (atlasCoordinate P b n v)) = realPlaneEnergy v := by
  rw [finsum_eq_sum_of_support_subset _ (s := P.support n) (by
    intro b hb
    by_contra hnot
    exact hb (by
      change realPlaneEnergy (atlasCoordinate P b n v) = 0
      rw [atlasCoordinate_energy, P.off_support b n hnot, zero_mul]))]
  exact atlasCoordinate_energy_sum P n v

theorem atlasCoordinate_energy_sum_active (P : AdmissibleAtlasPartition)
    (half n : Nat) (v : RealPlaneState) (hn : 1 ≤ n) (hbound : n ≤ half) :
    ∑ b ∈ atlasActiveBases P half, realPlaneEnergy (atlasCoordinate P b n v) =
      realPlaneEnergy v := by
  simp_rw [atlasCoordinate_energy]
  rw [← Finset.sum_mul, atlasPartition_sum_active_eq_one P half n hn hbound, one_mul]

/-- Interchange a finite base sum with the existing recursive channel sum. -/
theorem sumPositiveRadii_finset_sum (half : Nat) (bases : Finset AtlasBase)
    (term : AtlasBase → Nat → ℝ) :
    (∑ b ∈ bases, sumPositiveRadii half (term b)) =
      sumPositiveRadii half (fun r => ∑ b ∈ bases, term b r) := by
  induction half with
  | zero => simp [sumPositiveRadii_zero]
  | succ half ih => simp only [sumPositiveRadii_succ, Finset.sum_add_distrib, ih]

/-- Sum the INPUT energies of the weighted camera channels, before any defect. -/
def atlasResolvedEnergy (P : AdmissibleAtlasPartition) (half : Nat)
    (v : Nat → RealPlaneState) : ℝ :=
  ∑ b ∈ atlasActiveBases P half,
    sumPositiveRadii half (fun r => realPlaneEnergy (atlasCoordinate P b r (v r)))

theorem atlasResolvedEnergy_eq_input (P : AdmissibleAtlasPartition) (half : Nat)
    (v : Nat → RealPlaneState) :
    atlasResolvedEnergy P half v = sumPositiveRadii half (fun r => realPlaneEnergy (v r)) := by
  rw [atlasResolvedEnergy, sumPositiveRadii_finset_sum]
  exact sumPositiveRadii_congr half _ _ (fun r hr hbound =>
    atlasCoordinate_energy_sum_active P half r (v r) hr hbound)

theorem atlasResolvedEnergy_nonneg (P : AdmissibleAtlasPartition) (half : Nat)
    (v : Nat → RealPlaneState) : 0 ≤ atlasResolvedEnergy P half v := by
  rw [atlasResolvedEnergy_eq_input]
  exact sumPositiveRadii_real_nonneg half _ (fun _ _ _ => realPlaneEnergy_nonneg _)

end

end GeometryOfNumbers.Analysis
