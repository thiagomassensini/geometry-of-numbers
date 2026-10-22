import SingularSchur

namespace CarryNegativeDirection
open CarrySelfAdjointOperator ChiralReturn CarryCriticalSource
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- Actual two-channel energy excess; the boundary coordinate x is FIXED as k varies. -/
def returnExcess (n k : ℕ) (x : Fin (2*n) → ℂ) : ℝ :=
  ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2-
    ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2

theorem returnExcess_tendsto (n : ℕ) (x : Fin (2*n) → ℂ) :
    Tendsto (fun k => returnExcess n k x) atTop
      (nhds (-nativeSourceFiniteBoundaryEnergy (2*n) x/2)) := by
  have ht := ((nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto n x).div_const 2).neg
  convert ht using 1
  · funext k
    unfold returnExcess
    ring
  · ring

/-- Exact fixed-coordinate persistence criterion; operator norm alone is insufficient. -/
theorem negative_boundary_iff_persistent_excess (n : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceFiniteBoundaryEnergy (2*n) x<0 ↔
      ∃ ε : ℝ, 0<ε ∧ ∀ᶠ k : ℕ in atTop, ε≤returnExcess n k x := by
  constructor
  · intro hx
    refine ⟨-nativeSourceFiniteBoundaryEnergy (2*n) x/4,by linarith,?_⟩
    exact ((returnExcess_tendsto n x).eventually (eventually_gt_nhds (by linarith))).mono
      (fun _ hk => hk.le)
  · rintro ⟨ε,hε,hb⟩
    have h := ge_of_tendsto (returnExcess_tendsto n x) hb
    linarith

theorem returnExcess_eq_neg_storage (n k : ℕ) (x : Fin (2*n) → ℂ) :
    returnExcess n k x=-(storage k (nativeSourceChiralJetInput n k x) 1).re := by
  have h := nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage n k x
  unfold returnExcess
  linarith

/-- At a regular finite stage, every amplified finite-span input has jet coordinates.
The existential x here may vary with k: this is weaker than persistent fixed-x excess. -/
theorem finite_amplification_iff_jet_excess (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, (1 < ‖radialReturnTransfer k (2*n)‖ ↔
      ∃ x : Fin (2*n) → ℂ, 0 < returnExcess n k x) := by
  filter_upwards [nativeSourceChiralJetInput_eventually_bijective n] with k hk
  constructor
  · intro ha
    by_contra hn
    have hall : ∀ x : Fin (2*n) → ℂ, returnExcess n k x ≤ 0 := by
      simpa only [not_exists,not_lt] using hn
    have hs : ∀ c : Fin (2*n) → ℂ, 0 ≤ (storage k c 1).re := by
      intro c
      obtain ⟨x,hx⟩ := hk.2 c
      have hb := hall x
      rw [returnExcess_eq_neg_storage,hx] at hb
      linarith
    exact (not_le_of_gt ha) ((radialReturnTransfer_norm_le_one_iff_storage k (2*n)).mpr hs)
  · rintro ⟨x,hx⟩
    by_contra hn
    have hs := (radialReturnTransfer_norm_le_one_iff_storage k (2*n)).mp (le_of_not_gt hn)
      (nativeSourceChiralJetInput n k x)
    rw [returnExcess_eq_neg_storage] at hx
    linarith

/-- Strict eventual amplification, stronger than merely NOT eventual contractivity. -/
theorem negative_boundary_eventually_amplifies (n : ℕ) (x : Fin (2*n) → ℂ)
    (hx : nativeSourceFiniteBoundaryEnergy (2*n) x<0) :
    ∀ᶠ k : ℕ in atTop, 1<‖radialReturnTransfer k (2*n)‖ := by
  obtain ⟨ε,hε,hb⟩ := (negative_boundary_iff_persistent_excess n x).mp hx
  filter_upwards [hb] with k hk
  by_contra hn
  have hc := (radialReturnTransfer_norm_le_one_iff_storage k (2*n)).mp (le_of_not_gt hn)
    (nativeSourceChiralJetInput n k x)
  rw [returnExcess_eq_neg_storage] at hk
  linarith

/-- The hypothetical negative witness stays physically admissible and incident-visible.
The orientation bound concerns the original COMPLETED source pairing. -/
theorem negative_boundary_regular_witness (n : ℕ) (x : Fin (2*n) → ℂ)
    (hx : nativeSourceFiniteBoundaryEnergy (2*n) x<0) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ k : ℕ in atTop,
      (∀ j : Fin (2*n), canonicalCompletedC3RadialTiltPoint k j ∈ completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0 ∧
        completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0) ∧
      ε≤returnExcess n k x ∧
      (nativeSourceProjectiveBoundaryJetSynthesis n k x).1≠0 ∧
      1<‖radialReturnTransfer k (2*n)‖ ∧
      (inner ℂ (sourceValue k (nativeSourceChiralJetInput n k x) 1)
        (sourceCompanion k (nativeSourceChiralJetInput n k x) 1)).im≤-ε/4 := by
  obtain ⟨ε,hε,hb⟩ := (negative_boundary_iff_persistent_excess n x).mp hx
  refine ⟨ε,hε,?_⟩
  filter_upwards [hb,CarryRadialConservative.finite_eventually_admissible (2*n),
    invisible_incidence_cannot_return n,negative_boundary_eventually_amplifies n x hx,
    storage_one_eventually_eq_source_cross (2*n)] with k hk hreg hi ha hs
  refine ⟨hreg,hk,?_,ha,?_⟩
  · intro hz
    have hr := (hi x hz).2
    simp only [returnExcess,hz,hr,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_self] at hk
    linarith
  · rw [returnExcess_eq_neg_storage,hs] at hk
    linarith

/-- Algebraic negativity and persistent physical excess are the SAME sign gate,
not two independent obstructions. Only PR41 invertibility is required here. -/
theorem negative_schur_iff_persistent_excess (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s.val n)) :
    sourceMomentSchur h s.val n<0 ↔
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ k : ℕ in atTop,
      ε≤returnExcess (n+1) k (criticalCoordinates s n) := by
  have he := NativeMomentOrthogonalization.native_inverseSchur_boundary_energy s n hA
  have hh : nativeSourceFiniteBoundaryEnergy (2*(n+1)) (criticalCoordinates s n)=
      4*sourceMomentSchur h s.val n := by
    fin_cases s <;> simpa [criticalCoordinates,parityCoordinates,criticalCoefficients,h] using he
  constructor
  · intro hp
    apply (negative_boundary_iff_persistent_excess (n+1) (criticalCoordinates s n)).mp
    rw [hh]
    linarith
  · intro hp
    have hn := (negative_boundary_iff_persistent_excess (n+1) (criticalCoordinates s n)).mpr hp
    rw [hh] at hn
    linarith

/-- Singular/null prefix route: an explicit fixed source witness, with NO inverse. -/
theorem canonical_null_crossing_forces_persistent_return (s : Fin 2) (n : ℕ) (z : Fin n → ℝ)
    (hz : sourceMomentQuadratic h s.val n z=0)
    (hb : sourceMomentCoupling h s.val n ⬝ᵥ z≠0) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ k : ℕ in atTop,
      ε≤returnExcess (n+1) k (parityCoordinates s (nullCouplingWitness h s.val n z)) := by
  apply (negative_boundary_iff_persistent_excess (n+1) _).mp
  rw [parityCoordinates_boundary]
  have hn := null_coupling_witness_negative h s.val n z hz hb
  linarith

/-- The compatible singular route likewise produces a fixed physical witness. -/
theorem canonical_solution_residual_forces_persistent_return (s : Fin 2) (n : ℕ) (y : Fin n → ℝ)
    (hy : sourceMomentMatrix h s.val n *ᵥ y=sourceMomentCoupling h s.val n)
    (hr : h (2*n+s.val)-sourceMomentCoupling h s.val n ⬝ᵥ y<0) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ k : ℕ in atTop,
      ε≤returnExcess (n+1) k (parityCoordinates s (Fin.snoc (-y) 1)) := by
  apply (negative_boundary_iff_persistent_excess (n+1) _).mp
  rw [parityCoordinates_boundary,solution_witness_energy h s.val n y hy]
  linarith

end
end CarryNegativeDirection
