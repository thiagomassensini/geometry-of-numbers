import PrimeWheelNativeSignedGate
import CarrySelfAdjointOperator.CompletedNativeChiralTwoPointControl

/-!
# First unconditional physical Schur remainder from the original completed source

We use the already-proved (independent of RH) 2x2 chiral Pick/return
contractivity in the completed native carrier, and the EXACT projection
onto the first original Cauchy direction. Then the true signed remainder
is nonnegative on ALL linear combinations of these two physical features.

The proof does not:
* assume RH, zero localization, or an artificial measure on zeros;
* identify the scalar finite C2 connected cumulant as a Gram;
* throw away the negative nativeOut channel;
* replace the return by a different Hilbert metric or source.

The all-order source contraction, and transport of the 2x2 result to
higher canonical Schur jet pivots, remain open.
-/

namespace CarryWheelNativeSignedGate
open CarryReturnDeflation CarrySelfAdjointOperator ChiralReturn CarryPositiveSquare
open NativeMomentOrthogonalization GeometryOfNumbers.Analysis
open Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators

noncomputable section
set_option autoImplicit false

/-- The first ORIGINAL source cancels the old return after feedback, and
its remaining incident direction is inside the projected head. -/
theorem native_head_boundaryChannel (k N : ℕ) :
    boundaryChannel k (N+1) (Pi.single 0 1) =
      (oneDeficit k : ℂ) • nativeAnchor k := by
  unfold boundaryChannel
  rw [LinearMap.comp_apply, nativeIn_head, map_smul]
  change (oneDeficit k : ℂ) • nativeBoundaryProjection k (nativeAnchor k) = _
  rw [nativeBoundaryProjection_anchor]

/-- The scalar readout used by the ORIGINAL rank-one projection of
the incident feedback: it is not selected by moments or zeros. -/
def nativeHeadScalar (k N : ℕ) (c : Fin (N+1) → ℂ) : ℂ :=
  (anchorMass k : ℂ)⁻¹ *
    anchorCross (oneReturn k) (nativeAnchor k)
      (radialIncidentSynthesis k (N+1) c)
      (radialReturnedSynthesis k (N+1) c)

/-- The unique scalar to subtract from the original first source
to cancel its native boundary projection. -/
def nativeHeadCancellation (k N : ℕ) (c : Fin (N+1) → ℂ) : ℂ :=
  nativeHeadScalar k N c / (oneDeficit k : ℂ)

def nativeHeadCancelled (k N : ℕ) (c : Fin (N+1) → ℂ) : Fin (N+1) → ℂ :=
  c - nativeHeadCancellation k N c • Pi.single 0 1

theorem nativeHeadCancelled_boundary_zero (k N : ℕ)
    (hd : oneDeficit k ≠ 0) (c : Fin (N+1) → ℂ) :
    boundaryChannel k (N+1) (nativeHeadCancelled k N c) = 0 := by
  have hhead := native_head_boundaryChannel k N
  have hscalar : boundaryChannel k (N+1) c =
      nativeHeadScalar k N c • nativeAnchor k := by
    simpa only [nativeHeadScalar] using (native_boundary_formula k (N+1) c)
  have hd' : (oneDeficit k : ℂ) ≠ 0 := by exact_mod_cast hd
  have hmul : nativeHeadCancellation k N c * (oneDeficit k : ℂ) =
      nativeHeadScalar k N c := by
    exact div_mul_cancel₀ _ hd'
  unfold nativeHeadCancelled
  rw [map_sub, map_smul, hhead, hscalar, smul_smul, hmul]
  exact sub_self _

theorem nativeHeadCancelled_remainingIncident (k N : ℕ)
    (c : Fin (N+1) → ℂ) :
    remainingIncident k (N+1) (nativeHeadCancelled k N c) =
      remainingIncident k (N+1) c := by
  unfold nativeHeadCancelled
  rw [map_sub, map_smul, remainingIncident_head, smul_zero, sub_zero]

theorem nativeHeadCancelled_nativeOut (k N : ℕ)
    (c : Fin (N+1) → ℂ) :
    nativeOut k (N+1) (nativeHeadCancelled k N c) =
      nativeOut k (N+1) c := by
  unfold nativeHeadCancelled
  rw [map_sub, map_smul, nativeOut_head, smul_zero, sub_zero]

/-- The genuine physical signed return defect after head deflation
is PSD whenever the original full source return is contractive.
Crucially the SCHUR complement is positive because the projection
onto the old head was correctly removed, NOT because we drop it. -/
theorem physical_remaining_nonneg_of_original_return_contractive
    (k N : ℕ) (hd : 0 < oneDeficit k)
    (hcontr : ∀ c : Fin (N+1) → ℂ,
      ‖radialReturnedSynthesis k (N+1) c‖ ≤
        ‖radialIncidentSynthesis k (N+1) c‖)
    (c : Fin (N+1) → ℂ) :
    0 ≤ (remainingPair k (N+1) c c).re := by
  let c' := nativeHeadCancelled k N c
  have hzero : boundaryChannel k (N+1) c' = 0 :=
    nativeHeadCancelled_boundary_zero k N (ne_of_gt hd) c
  have hi : remainingIncident k (N+1) c' =
      remainingIncident k (N+1) c :=
    nativeHeadCancelled_remainingIncident k N c
  have ho : nativeOut k (N+1) c' = nativeOut k (N+1) c :=
    nativeHeadCancelled_nativeOut k N c
  have hbalance : 0 ≤ (nativeBalance k (N+1) c' c').re := by
    unfold nativeBalance balance
    rw [Complex.sub_re, physical_inner_self_re, physical_inner_self_re]
    have hh := hcontr c'
    have hsq : ‖radialReturnedSynthesis k (N+1) c'‖ ^ 2 ≤
        ‖radialIncidentSynthesis k (N+1) c'‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hh
    linarith
  have hsplit := native_balance_split k (N+1) c' c'
  rw [hzero] at hsplit
  simp only [inner_zero_left, zero_add] at hsplit
  have hreal := congrArg Complex.re hsplit
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hreal
  have hp : 0 ≤ (remainingPair k (N+1) c' c').re := by
    rw [← hreal]
    exact mul_nonneg hd.le hbalance
  simpa [remainingPair, hi, ho] using hp

/-- An exact all-order physical Schur transport theorem:
if the original Cauchy quotient satisfies the ALL-ORDER polarized Pick
inequality, then head-deflating the ORIGINAL source preserves nonnegative
signed remainder at each finite radial order, eventually in k.

THIS is the precise unproved geometric gate for all N: the hypothesis
is not a positivity assertion about a replacement Gram or a zero set.
-/
theorem native_all_orders_physical_schur_of_allOrderPick
    (hPick : CanonicalCompletedNativeRadialChiralPickEventuallyPosSemidefinite)
    (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin (N+1) → ℂ,
      0 ≤ (remainingPair k (N+1) c c).re := by
  filter_upwards [oneDeficit_eventually_pos, hPick (N+1)] with k hd hp c
  have hcontr :
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k (N+1) :=
    (canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
      k (N+1)).mpr hp
  exact physical_remaining_nonneg_of_original_return_contractive
    k N hd hcontr c

/-- Unconditional independent-of-RH source-first result: the
TRUE physical signed Schur remainder for the 2 ORIGINAL radial
Cauchy sources is eventually nonnegative for every coefficient vector. -/
theorem native_two_point_physical_remaining_eventually_nonneg :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin 2 → ℂ,
      0 ≤ (remainingPair k 2 c c).re := by
  filter_upwards [oneDeficit_eventually_pos,
    canonicalCompletedNativeChiralTwoPoint_contractive_eventually]
      with k hd hcontr c
  exact physical_remaining_nonneg_of_original_return_contractive
    k 1 hd hcontr c


/-- The first ODD canonical Schur pivot inherits positivity from the
physical 2-source deflated return, without RH, zeros, or a fitted Gram.
This is the n=0 base of the all-order positive Schur tower. -/
theorem native_odd_first_pivot_nonneg_without_RH :
    0 ≤ carryPairingPivot
      (hankelPairing (fun j => canonicalCompletedNativeLogDerivativeMoment (j+1))) 0 := by
  apply native_odd_pivot_nonneg_of_eventual_return_dominance 0
  filter_upwards [native_two_point_physical_remaining_eventually_nonneg]
      with k hk
  have h := hk (nativeSourceChiralJetInput 1 k (nativeResidualBoundary 1 0))
  rw [physical_remaining_pair_self_re] at h
  linarith

end
end CarryWheelNativeSignedGate
