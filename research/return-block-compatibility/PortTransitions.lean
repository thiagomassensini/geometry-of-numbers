import ReturnRestriction

namespace CarryReturnCompatibility
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

private theorem ker_le_of_norm_eq {A H K : Type*}
    [AddCommGroup A] [Module ℂ A]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (f : A →ₗ[ℂ] H) (g : A →ₗ[ℂ] K) (hn : ∀ x, ‖g x‖ = ‖f x‖) :
    f.ker ≤ g.ker := by
  intro x hx
  apply norm_eq_zero.mp
  rw [hn x, (show f x = 0 from hx), norm_zero]

/-- Induced map of ACTUAL source images. Equality of norms is proved from
the source-return restriction below; it is not a desired moment Gram premise. -/
def rangeTransportLinear {A H K : Type*}
    [AddCommGroup A] [Module ℂ A]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (f : A →ₗ[ℂ] H) (g : A →ₗ[ℂ] K) (hn : ∀ x, ‖g x‖ = ‖f x‖) :
    f.range →ₗ[ℂ] K :=
  ((f.ker).liftQ g (ker_le_of_norm_eq f g hn)).comp f.quotKerEquivRange.symm.toLinearMap

theorem rangeTransportLinear_source {A H K : Type*}
    [AddCommGroup A] [Module ℂ A]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (f : A →ₗ[ℂ] H) (g : A →ₗ[ℂ] K) (hn : ∀ x, ‖g x‖ = ‖f x‖) (x : A) :
    rangeTransportLinear f g hn ⟨f x,⟨x,rfl⟩⟩ = g x := by
  simp only [rangeTransportLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

theorem energyPort_prefix_norm (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (hM : ‖radialReturnTransfer k M‖ ≤ 1) (x : RadialIncidentSpan k N) :
    ‖radialReturnEnergyPort k M (incidentInclusion k h x)‖ =
      ‖radialReturnEnergyPort k N x‖ := by
  have he : ‖radialReturnEnergyPort k M (incidentInclusion k h x)‖^2 =
      ‖radialReturnEnergyPort k N x‖^2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
    exact congrArg RCLike.re (energyPort_prefix_pairing k h hM x x)
  nlinarith [norm_nonneg (radialReturnEnergyPort k M (incidentInclusion k h x)),
    norm_nonneg (radialReturnEnergyPort k N x)]

abbrev PhysicalEnergyRange (k N : ℕ) := (radialReturnEnergyPort k N).toLinearMap.range

/-- Natural isometric transition between physical energy-image subspaces.
The metrics are inherited from the ORIGINAL Cauchy carrier on both sides. -/
def energyTransition (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (hM : ‖radialReturnTransfer k M‖ ≤ 1) :
    PhysicalEnergyRange k N →ₗᵢ[ℂ] PhysicalEnergyRange k M := by
  let f := (radialReturnEnergyPort k N).toLinearMap
  let g := (radialReturnEnergyPort k M).toLinearMap.comp (incidentInclusion k h).toLinearMap
  have hn : ∀ x, ‖g x‖ = ‖f x‖ := energyPort_prefix_norm k h hM
  let L := rangeTransportLinear f g hn
  have hm (z : f.range) : L z ∈ PhysicalEnergyRange k M := by
    obtain ⟨x,hx⟩ := z.property
    have hz : (⟨f x,⟨x,rfl⟩⟩ : f.range) = z := Subtype.ext hx
    rw [← hz, rangeTransportLinear_source]
    exact ⟨incidentInclusion k h x,rfl⟩
  refine ⟨L.codRestrict _ hm, ?_⟩
  intro z
  obtain ⟨x,hx⟩ := z.property
  have hz : (⟨f x,⟨x,rfl⟩⟩ : f.range) = z := Subtype.ext hx
  rw [← hz]
  change ‖L ⟨f x,⟨x,rfl⟩⟩‖ = ‖f x‖
  rw [rangeTransportLinear_source]
  exact hn x

theorem energyTransition_source (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (hM : ‖radialReturnTransfer k M‖ ≤ 1) (x : RadialIncidentSpan k N) :
    (energyTransition k h hM
      ⟨radialReturnEnergyPort k N x,⟨x,rfl⟩⟩ : CanonicalCompletedNativeChiralCauchyCarrier) =
      radialReturnEnergyPort k M (incidentInclusion k h x) :=
  rangeTransportLinear_source _ _ _ x

/-- Exact cocycle: increasing the block in one or two steps gives the same
physical energy vector after the NATURAL image transition. -/
theorem energyTransition_trans (k : ℕ) {N M L : ℕ} (hNM : N ≤ M) (hML : M ≤ L)
    (hL : ‖radialReturnTransfer k L‖ ≤ 1) (z : PhysicalEnergyRange k N) :
    energyTransition k hML hL
      (energyTransition k hNM (radialReturnTransfer_norm_le_one_of_prefix k hML hL) z) =
        energyTransition k (hNM.trans hML) hL z := by
  obtain ⟨x,hx⟩ := z.property
  have hz : (⟨radialReturnEnergyPort k N x,⟨x,rfl⟩⟩ : PhysicalEnergyRange k N) = z := Subtype.ext hx
  rw [← hz]
  apply Subtype.ext
  have he : energyTransition k hNM (radialReturnTransfer_norm_le_one_of_prefix k hML hL)
      ⟨radialReturnEnergyPort k N x,⟨x,rfl⟩⟩ =
      (⟨radialReturnEnergyPort k M (incidentInclusion k hNM x),⟨incidentInclusion k hNM x,rfl⟩⟩ :
        PhysicalEnergyRange k M) := Subtype.ext (energyTransition_source k hNM _ x)
  rw [he, energyTransition_source, energyTransition_source]
  congr 1

theorem energyTransition_self (k N : ℕ) (hN : ‖radialReturnTransfer k N‖ ≤ 1)
    (z : PhysicalEnergyRange k N) : energyTransition k (le_refl N) hN z = z := by
  obtain ⟨x,hx⟩ := z.property
  have hz : (⟨radialReturnEnergyPort k N x,⟨x,rfl⟩⟩ : PhysicalEnergyRange k N) = z := Subtype.ext hx
  rw [← hz]
  apply Subtype.ext
  rw [energyTransition_source]
  rfl

end
end CarryReturnCompatibility
