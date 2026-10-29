import PolarizedJoint

namespace CarryTfvdJoint
open CarrySelfAdjointOperator PhysicalSewing NativeLaguerre ChiralReturn
open CarryTfvdCritical CarryCriticalSource CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- A spelling of the recombined readout, not a new source or metric. -/
def jointKernel (M P k : ℕ) (i j : ℕ) : ℂ :=
  polarizedNumerator
    (value M (canonicalCompletedC3RadialTiltPoint k i))
    (logJet M (canonicalCompletedC3RadialTiltPoint k i))
    (completionResponse (canonicalCompletedC3RadialTiltPoint k i))
    (value P (canonicalCompletedC3RadialTiltPoint k j))
    (logJet P (canonicalCompletedC3RadialTiltPoint k j))
    (completionResponse (canonicalCompletedC3RadialTiltPoint k j)) /
  (2*(canonicalCompletedC3RadialTiltPoint k j-conj (canonicalCompletedC3RadialTiltPoint k i))*
    (conj (value M (canonicalCompletedC3RadialTiltPoint k i))*
      value P (canonicalCompletedC3RadialTiltPoint k j)))

/-- The full physical graph is unchanged, uniformly over exact cutoffs and inputs. -/
theorem fullSource_eventually_graph (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ M : ℕ, ∀ x : Fin (2*n) → ℂ,
      fullSource M n k x = twoPortSynthesis (2*n) k (fixedMaterial n k x)
        (fun j => originalResponse (canonicalCompletedC3RadialTiltPoint k j)*fixedMaterial n k x j) := by
  filter_upwards [CarryRadialConservative.finite_eventually_admissible (2*n)] with k hk M x
  unfold fullSource fullSecond tfvdMaterialSecondCoefficients canonicalStates
  simp only [tfvdCanonicalResponse_eq_original M _ (hk _).1 (hk _).2.1]

/-- Finite whole-source identity, both inputs independent and all crossings.
No scalar readout is used to reconstruct the physical source. -/
theorem fullSources_eventually_jointKernel (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ M P : ℕ, ∀ x y : Fin (2*n) → ℂ,
      canonicalCompletedNativeProjectiveChiralForm (fullSource M n k x) (fullSource P n k y) =
        ∑ i, ∑ j, conj (fixedMaterial n k x i)*fixedMaterial n k y j*jointKernel M P k i j := by
  filter_upwards [fullSource_eventually_graph n,
    CarryRadialConservative.finite_eventually_admissible (2*n)] with k hg hk M P x y
  rw [hg M x,hg P y,graph_pairing_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [physical_basis_quotient (2*n) M P k i j (hk i).1 (hk j).1 (hk i).2.1 (hk j).2.1]
  rfl

/-- Same exact critical coordinates as PR41, only the old prefix is assumed invertible.
The finite expression is assembled jointly and THEN its real part is taken. -/
theorem critical_jointKernel_tendsto (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s.val n)) (cutoff : ℕ → ℕ) :
    Tendsto (fun k => (∑ i : Fin (2*(n+1)), ∑ j : Fin (2*(n+1)),
      conj (fixedMaterial (n+1) k (criticalCoordinates s n) i)*
        fixedMaterial (n+1) k (criticalCoordinates s n) j *
        jointKernel (cutoff k) (cutoff k) k i j).re) atTop
      (nhds (sourceMomentSchur h s.val n)) := by
  apply (critical_total_flux_tendsto s n hA cutoff).congr'
  filter_upwards [fullSources_eventually_jointKernel (n+1)] with k hk
  rw [← hk (cutoff k) (cutoff k) (criticalCoordinates s n) (criticalCoordinates s n),
    full_head_real_ledger]

end
end CarryTfvdJoint
