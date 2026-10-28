import JetEulerVariation
import PolarizedBoundaryReadout
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace CarryBoundaryReconstruction
open CarrySelfAdjointOperator CarryMovingEulerBalance Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E]

/-- Ordered finite telescoping, with the original anchor retained. -/
theorem radial_partial_sum (f : ℕ → E) (K M : ℕ) :
    (∑ j ∈ Finset.range M, (f (K+j)-f (K+j+1)))=f K-f (K+M) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [Nat.add_succ]
    abel

/-- Convergence of ordered increments does not claim absolute summability. -/
theorem radial_partial_sum_tendsto (f : ℕ → E) (L : E)
    (hf : Tendsto f atTop (nhds L)) (K : ℕ) :
    Tendsto (fun M => ∑ j ∈ Finset.range M, (f (K+j)-f (K+j+1)))
      atTop (nhds (f K-L)) := by
  simp_rw [radial_partial_sum]
  have ht : Tendsto (fun M : ℕ => K+M) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat K
  exact tendsto_const_nhds.sub (hf.comp ht)

/-- Nonnegative complete increments justify an unconditional real sum. -/
theorem radial_drop_hasSum (f : ℕ → ℝ) (L : ℝ)
    (hf : Tendsto f atTop (nhds L)) (K : ℕ)
    (hd : ∀ j, 0≤f (K+j)-f (K+j+1)) :
    HasSum (fun j => f (K+j)-f (K+j+1)) (f K-L) :=
  (hasSum_iff_tendsto_nat_of_nonneg hd _).mpr (radial_partial_sum_tendsto f L hf K)

/-- Transparent readout of the SAME complete native jet synthesis. -/
def completePair (n k : ℕ) (x y : Fin (2*n) → ℂ) : ℂ :=
  canonicalCompletedNativeProjectiveChiralForm
    (nativeSourceProjectiveBoundaryJetSynthesis n k x)
    (nativeSourceProjectiveBoundaryJetSynthesis n k y)

/-- All finite orders, two independent complex inputs, original boundary.
No mixed crossing is set to zero before the complete source limit. -/
theorem complete_pair_boundary_reconstruction (n K : ℕ) (x y : Fin (2*n) → ℂ) :
    Tendsto (fun M => completePair n K x y-
      ∑ j ∈ Finset.range M, (completePair n (K+j) x y-completePair n (K+j+1) x y))
      atTop (nhds (originalBoundaryPair n x y)) := by
  have hf : Tendsto (fun k => completePair n k x y) atTop
      (nhds (originalBoundaryPair n x y)) :=
    nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto n x y
  have ht := radial_partial_sum_tendsto _ _ hf K
  have hh := (tendsto_const_nhds (x := completePair n K x y)).sub ht
  have he : completePair n K x y-(completePair n K x y-originalBoundaryPair n x y)=
      originalBoundaryPair n x y := by abel
  rw [he] at hh
  exact hh

end
end CarryBoundaryReconstruction
