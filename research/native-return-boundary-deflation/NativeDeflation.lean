import BoundaryFeedback
import SourceSquare

namespace CarryReturnDeflation
open CarrySelfAdjointOperator ChiralReturn CarryPositiveSquare
open CarryJetOverlap CarryFiberTransport CarryResidualEuler
open Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

abbrev Physical := CanonicalCompletedNativeChiralCauchyCarrier

/-- The FIRST ORIGINAL radial Cauchy feature. No moment chooses this vector. -/
def nativeAnchor (k : ℕ) : Physical := completedNativeRadialChiralCauchyState k 0
def anchorMass (k : ℕ) : ℝ := ((k:ℝ)+1)/2
def nativeBoundarySpan (k : ℕ) : Submodule ℂ Physical :=
  Submodule.span ℂ ({nativeAnchor k} : Set Physical)
instance nativeBoundarySpan_projection (k : ℕ) :
    (nativeBoundarySpan k).HasOrthogonalProjection := by
  unfold nativeBoundarySpan
  infer_instance

def nativeBoundaryProjection (k : ℕ) : Physical →L[ℂ] Physical :=
  (nativeBoundarySpan k).starProjection

theorem anchorMass_pos (k : ℕ) : 0 < anchorMass k := by unfold anchorMass; positivity

theorem nativeAnchor_inner (k : ℕ) :
    inner ℂ (nativeAnchor k) (nativeAnchor k) = (anchorMass k : ℂ) := by
  rw [nativeAnchor, inner_completedNativeRadialChiralCauchyState]
  norm_num [anchorMass, div_eq_mul_inv]

theorem nativeBoundaryProjection_anchor (k : ℕ) :
    nativeBoundaryProjection k (nativeAnchor k) = nativeAnchor k := by
  apply (nativeBoundarySpan k).starProjection_eq_self_iff.mpr
  exact Submodule.subset_span (by simp)

/-- Both maps are combinations of the SAME actual incident and returned
vectors, in their original Hilbert carrier. They are only decomposition
coordinates; no replacement source or return operator is asserted. -/
def nativeIn (k N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] Physical :=
  radialIncidentSynthesis k N - conj (oneReturn k) • radialReturnedSynthesis k N
def nativeOut (k N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] Physical :=
  radialReturnedSynthesis k N - oneReturn k • radialIncidentSynthesis k N
def boundaryChannel (k N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] Physical :=
  (nativeBoundaryProjection k).toLinearMap.comp (nativeIn k N)
def remainingIncident (k N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] Physical :=
  nativeIn k N - boundaryChannel k N

def remainingPair (k N : ℕ) (c d : Fin N → ℂ) : ℂ :=
  inner ℂ (remainingIncident k N c) (remainingIncident k N d) -
    inner ℂ (nativeOut k N c) (nativeOut k N d)

def nativeBalance (k N : ℕ) (c d : Fin N → ℂ) : ℂ :=
  balance (radialIncidentSynthesis k N c) (radialReturnedSynthesis k N c)
    (radialIncidentSynthesis k N d) (radialReturnedSynthesis k N d)

theorem native_deficit (k : ℕ) : deficit (oneReturn k) = (oneDeficit k : ℂ) := by
  simp only [deficit, oneDeficit, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.normSq_eq_conj_mul_self]

/-- Exact polarized native decomposition at every finite k,N. No sign,
regularity of a quotient denominator, or Hankel assumption is required. -/
theorem native_balance_split (k N : ℕ) (c d : Fin N → ℂ) :
    (oneDeficit k : ℂ)*nativeBalance k N c d =
      inner ℂ (boundaryChannel k N c) (boundaryChannel k N d) + remainingPair k N c d := by
  have hh := feedback_projection_split (nativeBoundarySpan k) (oneReturn k)
    (radialIncidentSynthesis k N c) (radialReturnedSynthesis k N c)
    (radialIncidentSynthesis k N d) (radialReturnedSynthesis k N d)
  rw [native_deficit] at hh
  exact hh

theorem native_boundary_formula (k N : ℕ) (c : Fin N → ℂ) :
    boundaryChannel k N c =
      ((anchorMass k:ℂ)⁻¹ * anchorCross (oneReturn k) (nativeAnchor k)
        (radialIncidentSynthesis k N c) (radialReturnedSynthesis k N c)) • nativeAnchor k := by
  change (nativeBoundarySpan k).starProjection
    (feedbackIn (oneReturn k) (radialIncidentSynthesis k N c) (radialReturnedSynthesis k N c)) = _
  unfold nativeBoundarySpan
  rw [singleton_projection _ _ _ (ne_of_gt (anchorMass_pos k)) (nativeAnchor_inner k),
    feedback_anchor_pair]

/-- Explicit signed remainder of the original native Schur calculation. -/
theorem native_schur_remainder (k N : ℕ) (c d : Fin N → ℂ) (hd : oneDeficit k ≠ 0) :
    remainingPair k N c d / (oneDeficit k:ℂ) = nativeBalance k N c d -
      conj (anchorCross (oneReturn k) (nativeAnchor k)
        (radialIncidentSynthesis k N c) (radialReturnedSynthesis k N c)) *
      anchorCross (oneReturn k) (nativeAnchor k)
        (radialIncidentSynthesis k N d) (radialReturnedSynthesis k N d) /
          ((oneDeficit k:ℂ)*(anchorMass k:ℂ)) := by
  have hd' : deficit (oneReturn k) ≠ 0 := by rw [native_deficit]; exact_mod_cast hd
  have hh := physical_schur_remainder (nativeAnchor k)
    (radialIncidentSynthesis k N c) (radialReturnedSynthesis k N c)
    (radialIncidentSynthesis k N d) (radialReturnedSynthesis k N d)
    (oneReturn k) (anchorMass k) (ne_of_gt (anchorMass_pos k)) (nativeAnchor_inner k) hd'
  rw [native_deficit] at hh
  exact hh

theorem native_incident_head (k N : ℕ) :
    radialIncidentSynthesis k (N+1) (Pi.single 0 1) = nativeAnchor k := by
  simp [radialIncidentSynthesis, nativeAnchor]

theorem native_returned_head (k N : ℕ) :
    radialReturnedSynthesis k (N+1) (Pi.single 0 1) = oneReturn k • nativeAnchor k := by
  simp [radialReturnedSynthesis, completedNativeRadialChiralMultiplierState, nativeAnchor, oneReturn]

theorem nativeIn_head (k N : ℕ) :
    nativeIn k (N+1) (Pi.single 0 1) = (oneDeficit k:ℂ) • nativeAnchor k := by
  change feedbackIn (oneReturn k) _ _ = _
  rw [native_incident_head, native_returned_head, feedback_anchor_in, native_deficit]

theorem nativeOut_head (k N : ℕ) : nativeOut k (N+1) (Pi.single 0 1) = 0 := by
  change feedbackOut (oneReturn k) _ _ = _
  rw [native_incident_head, native_returned_head, feedback_anchor_out]

theorem remainingIncident_head (k N : ℕ) :
    remainingIncident k (N+1) (Pi.single 0 1) = 0 := by
  change nativeIn k (N+1) (Pi.single 0 1) -
    nativeBoundaryProjection k (nativeIn k (N+1) (Pi.single 0 1)) = 0
  rw [nativeIn_head, map_smul, nativeBoundaryProjection_anchor, sub_self]

/-- Exact physical deflation: the remaining signed kernel annihilates the
first original source in BOTH slots, not merely on the diagonal. -/
theorem remainingPair_head_left (k N : ℕ) (c : Fin (N+1) → ℂ) :
    remainingPair k (N+1) (Pi.single 0 1) c = 0 := by
  simp [remainingPair, remainingIncident_head, nativeOut_head]

theorem remainingPair_head_right (k N : ℕ) (c : Fin (N+1) → ℂ) :
    remainingPair k (N+1) c (Pi.single 0 1) = 0 := by
  simp [remainingPair, remainingIncident_head, nativeOut_head]

theorem remainingPair_eraseHead (k N : ℕ) (c d : Fin (N+1) → ℂ) :
    remainingPair k (N+1) c d = remainingPair k (N+1) (eraseHead c) (eraseHead d) := by
  unfold remainingPair
  rw [linearMap_eraseHead _ (remainingIncident_head k N) c,
    linearMap_eraseHead _ (remainingIncident_head k N) d,
    linearMap_eraseHead _ (nativeOut_head k N) c,
    linearMap_eraseHead _ (nativeOut_head k N) d]

theorem native_reconstruct_incident (k N : ℕ) (c : Fin N → ℂ) :
    (oneDeficit k:ℂ) • radialIncidentSynthesis k N c =
      boundaryChannel k N c + remainingIncident k N c + conj (oneReturn k) • nativeOut k N c := by
  have hh := projected_reconstruct_incident (nativeBoundarySpan k) (oneReturn k)
    (radialIncidentSynthesis k N c) (radialReturnedSynthesis k N c)
  rw [native_deficit] at hh
  exact hh

theorem native_reconstruct_returned (k N : ℕ) (c : Fin N → ℂ) :
    (oneDeficit k:ℂ) • radialReturnedSynthesis k N c =
      nativeOut k N c + oneReturn k • (boundaryChannel k N c + remainingIncident k N c) := by
  have hh := feedback_reconstruct_returned (oneReturn k)
    (radialIncidentSynthesis k N c) (radialReturnedSynthesis k N c)
  rw [native_deficit] at hh
  simpa only [boundaryChannel, remainingIncident, LinearMap.sub_apply,
    add_sub_cancel, nativeIn, nativeOut, feedbackIn, feedbackOut,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using hh

/-- The THREE channels jointly preserve every original finite source
coefficient. A zero signed energy is never identified with a zero state. -/
theorem channels_separate_source (k N : ℕ) (hd : oneDeficit k ≠ 0)
    (c : Fin N → ℂ) (hc : boundaryChannel k N c=0)
    (hi : remainingIncident k N c=0) (ho : nativeOut k N c=0) : c=0 := by
  have hh := native_reconstruct_incident k N c
  rw [hc,hi,ho,smul_zero,add_zero,add_zero] at hh
  have hd' : (oneDeficit k:ℂ) ≠ 0 := by exact_mod_cast hd
  have hz := (smul_eq_zero.mp hh).resolve_left hd'
  exact (radialIncidentSynthesis_injective k N) (hz.trans (map_zero _).symm)

theorem nativeIn_mem_original_span (k N : ℕ) (c : Fin N → ℂ) :
    nativeIn k N c ∈ (radialIncidentSynthesis k N).range := by
  have hr : radialReturnedSynthesis k N c ∈ (radialIncidentSynthesis k N).range := by
    rw [radialReturnedSynthesis_eq_incident_multiply]
    exact ⟨_,rfl⟩
  change radialIncidentSynthesis k N c - conj (oneReturn k) • radialReturnedSynthesis k N c ∈ _
  exact Submodule.sub_mem _ ⟨c,rfl⟩ (Submodule.smul_mem _ _ hr)

theorem nativeOut_mem_original_span (k N : ℕ) (c : Fin N → ℂ) :
    nativeOut k N c ∈ (radialIncidentSynthesis k N).range := by
  have hr : radialReturnedSynthesis k N c ∈ (radialIncidentSynthesis k N).range := by
    rw [radialReturnedSynthesis_eq_incident_multiply]
    exact ⟨_,rfl⟩
  change radialReturnedSynthesis k N c - oneReturn k • radialIncidentSynthesis k N c ∈ _
  exact Submodule.sub_mem _ hr (Submodule.smul_mem _ _ ⟨c,rfl⟩)

/-- This projection stays INSIDE the original finite source span. It is
not an unrestricted ambient projection with an unproved clock-domain gate. -/
theorem boundaryChannel_mem_original_span (k N : ℕ) (c : Fin (N+1) → ℂ) :
    boundaryChannel k (N+1) c ∈ (radialIncidentSynthesis k (N+1)).range := by
  rw [native_boundary_formula]
  have he : nativeAnchor k ∈ (radialIncidentSynthesis k (N+1)).range :=
    ⟨Pi.single 0 1, native_incident_head k N⟩
  exact Submodule.smul_mem _ _ he

theorem remainingIncident_mem_original_span (k N : ℕ) (c : Fin (N+1) → ℂ) :
    remainingIncident k (N+1) c ∈ (radialIncidentSynthesis k (N+1)).range :=
  Submodule.sub_mem _ (nativeIn_mem_original_span k (N+1) c)
    (boundaryChannel_mem_original_span k N c)

theorem physical_inner_self_re (x : Physical) : (inner ℂ x x).re = ‖x‖^2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

theorem native_storage_balance (k N : ℕ) (c : Fin N → ℂ) :
    (nativeBalance k N c c).re = (storage k c 1).re := by
  rw [storage_one_eq_finiteTransfer_energy, radialReturnTransfer_exact, radialIncidentVector_norm]
  simp only [nativeBalance, balance, Complex.sub_re, physical_inner_self_re]

theorem native_energy_split (k N : ℕ) (c : Fin N → ℂ) :
    oneDeficit k*(storage k c 1).re =
      ‖boundaryChannel k N c‖^2 + (remainingPair k N c c).re := by
  have hh := congrArg Complex.re (native_balance_split k N c c)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re, physical_inner_self_re, native_storage_balance] using hh

/-- Only the already known CENTRAL source coefficient supplies this first
positive channel. No later pivot, contraction, or all-order positivity is used. -/
theorem oneDeficit_eventually_pos : ∀ᶠ k : ℕ in Filter.atTop, 0 < oneDeficit k := by
  have ht := (tendsto_order.mp one_signed_energy_tendsto).1 0
    (mul_pos (by norm_num : (0:ℝ) < 2) canonicalCompletedNativeLogDerivativeMoment_zero_pos)
  filter_upwards [ht] with k hk
  rw [one_storage_scalar] at hk
  by_contra hn
  have hd : oneDeficit k ≤ 0 := le_of_not_gt hn
  have hz := mul_nonpos_of_nonpos_of_nonneg hd (sq_nonneg ‖oneSource k‖)
  linarith

theorem boundary_energy_eventually_nonnegative (N : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ c : Fin N → ℂ,
      0 ≤ ‖boundaryChannel k N c‖^2 / oneDeficit k := by
  filter_upwards [oneDeficit_eventually_pos] with k hk c
  exact div_nonneg (sq_nonneg _) hk.le

end
end CarryReturnDeflation
