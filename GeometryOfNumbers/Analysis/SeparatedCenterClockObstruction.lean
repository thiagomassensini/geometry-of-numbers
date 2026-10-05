import GeometryOfNumbers.Analysis.SeparatedCenterObservation
import GeometryOfNumbers.Analysis.FiniteCompletedBoundaryClock

/-! The bounded separated center-role block cannot be a faithful realization
of all finite material-clock cutoffs. No metric or moment sequence enters this
necessary frequency test. Small cutoffs are not excluded by this theorem. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open NativeMaterialClock FiniteClockJets

/-- A material frequency outside the bounded block's norm cannot survive
an injective linear intertwiner, even if that map is not isometric. -/
theorem separatedCenterBlock_no_injective_finiteClock_intertwiner
    {M : ℕ} (j : Fin M)
    (hfreq : ‖baseTwoSeparatedCenterBlock‖ < finiteRealSpectralFrequency j) :
    ¬ ∃ U : FiniteRealSpectralHilbert M →ₗ[ℂ] BaseTwoSeparatedCenterHilbert,
      Function.Injective U ∧ ∀ x,
        U (finiteMaterialClock M x) = baseTwoSeparatedCenterBlock (U x) := by
  rintro ⟨U,hU,hint⟩
  let e := finiteMaterialBasis j
  have he : e ≠ 0 := by
    intro h
    have hc := congrArg (fun x : FiniteRealSpectralHilbert M => x j) h
    simp [e,finiteMaterialBasis] at hc
  have hUe : U e ≠ 0 := by
    intro h
    apply he
    apply hU
    simpa using h
  have hlambda : 0 ≤ finiteRealSpectralFrequency j := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ j.val+1 by omega)
  have heig : baseTwoSeparatedCenterBlock (U e) =
      (finiteRealSpectralFrequency j : ℂ) • U e := by
    rw [← hint e]
    change U (finiteMaterialClock M (finiteMaterialBasis j)) = _
    rw [finiteMaterialClock_basis,U.map_smul]
    rfl
  have hb := baseTwoSeparatedCenterBlock.le_opNorm (U e)
  rw [heig,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlambda] at hb
  have hn := norm_pos_iff.mpr hUe
  nlinarith

/-- The same obstruction applies to the existing exact seed/gradient coordinate
change, rather than only to raw nodal coordinates. -/
theorem separatedCenterBlock_no_injective_seedGradient_intertwiner
    {K : ℕ} (j : Fin (K+1))
    (hfreq : ‖baseTwoSeparatedCenterBlock‖ < finiteRealSpectralFrequency j) :
    ¬ ∃ U : FiniteSeedGradientCarrier K →ₗ[ℂ] BaseTwoSeparatedCenterHilbert,
      Function.Injective U ∧ ∀ y,
        U (finiteSeedGradientClock K y) = baseTwoSeparatedCenterBlock (U y) := by
  rintro ⟨U,hU,hint⟩
  apply separatedCenterBlock_no_injective_finiteClock_intertwiner j hfreq
  refine ⟨U.comp (finiteSeedGradientEncode K),
    hU.comp (finiteSeedGradientEquiv K).injective, ?_⟩
  intro x
  change U (finiteSeedGradientEncode K (finiteMaterialClock (K+1) x)) = _
  rw [← finiteSeedGradientClock_intertwining K x]
  exact hint _

/-- A synchronized base-two cutoff 4N edges / 4N+1 samples contains an
excluded frequency. This is an existence proof using exp/log monotonicity. -/
theorem separatedCenterBlock_exists_excluded_baseTwo_cutoff :
    ∃ N : ℕ, ∃ j : Fin (4*N+1),
      ‖baseTwoSeparatedCenterBlock‖ < finiteRealSpectralFrequency j := by
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp ‖baseTwoSeparatedCenterBlock‖)
  refine ⟨N,⟨N,by omega⟩,?_⟩
  change ‖baseTwoSeparatedCenterBlock‖ < Real.log ((N+1:ℕ):ℝ)
  have ht : Real.exp ‖baseTwoSeparatedCenterBlock‖ < ((N+1:ℕ):ℝ) := by
    push_cast
    linarith
  have hlog := Real.log_lt_log (Real.exp_pos ‖baseTwoSeparatedCenterBlock‖) ht
  simpa only [Real.log_exp] using hlog

/-- No family of faithful intertwiners to the unchanged separated block can
cover all geometric base-two cutoffs. The missing material diagonal is not
replaced by adding the bounded central adjoint pairs alone. -/
theorem separatedCenterBlock_not_complete_materialClock_realization :
    ¬ (∀ N : ℕ, ∃ U : FiniteSeedGradientCarrier (4*N) →ₗ[ℂ] BaseTwoSeparatedCenterHilbert,
      Function.Injective U ∧ ∀ y,
        U (finiteSeedGradientClock (4*N) y) = baseTwoSeparatedCenterBlock (U y)) := by
  intro h
  obtain ⟨N,j,hj⟩ := separatedCenterBlock_exists_excluded_baseTwo_cutoff
  exact separatedCenterBlock_no_injective_seedGradient_intertwiner j hj (h N)

/-- The genuine completed finite boundary graph is equivalent to seed/gradient
coordinates. Retaining its derived boundary does not remove the frequency obstruction. -/
theorem separatedCenterBlock_not_completedBoundaryClock_realization :
    ¬ (∀ N : ℕ, ∃ U : finiteCompletedBoundaryGraph N →ₗ[ℂ] BaseTwoSeparatedCenterHilbert,
      Function.Injective U ∧ ∀ y,
        U (finiteCompletedBoundaryClock N y) = baseTwoSeparatedCenterBlock (U y)) := by
  intro h
  apply separatedCenterBlock_not_complete_materialClock_realization
  intro N
  obtain ⟨U,hU,hint⟩ := h N
  have he : Function.Injective (finiteCompletedBoundaryGraphEmbed N) := by
    intro x y hxy
    have hh := congrArg (fun z : finiteCompletedBoundaryGraph N =>
      finiteCompletedBoundaryForget N z.val) hxy
    change finiteCompletedBoundaryForget N (finiteCompletedBoundaryEmbed N x) =
      finiteCompletedBoundaryForget N (finiteCompletedBoundaryEmbed N y) at hh
    simpa only [finiteCompletedBoundaryForget_embed] using hh
  refine ⟨U.comp (finiteCompletedBoundaryGraphEmbed N),hU.comp he,?_⟩
  intro x
  change U (finiteCompletedBoundaryGraphEmbed N (finiteSeedGradientClock (4*N) x)) = _
  rw [← finiteCompletedBoundaryClock_intertwining N x]
  exact hint _

end GeometryOfNumbers.Analysis.BaseTwoCompletion
