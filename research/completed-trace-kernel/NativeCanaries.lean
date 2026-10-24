import CrossRadialGeometry

/-! Only this late canary uses the independently proved first native
moment sign. The physical states, trace transport and cross factor do not. -/
namespace CarryCompletedTrace
open CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false

def endpointBalance (k : ℕ) {N : ℕ} (c : Fin N → ℂ) : ℝ :=
  ‖endpointTrace 0 (incidentCore k c 1)‖^2 - ‖endpointTrace 0 (returnedCore k c 1)‖^2

/-- Compatibility with the HISTORICAL signed storage flux, not a new sign law. -/
theorem endpoint_balance_is_native_flux (k : ℕ) {N : ℕ} (c : Fin N → ℂ) :
    endpointBalance k c = (deriv (ChiralReturn.storage k c) 1).re := by
  have hi : endpointTrace 0 (incidentCore k c 1) =
      (Real.sqrt ((k : ℝ)+1) : ℂ)*ChiralReturn.incident c 1 := by
    rw [incident_core_trace]
    simp [ChiralReturn.incident]
  have hr : endpointTrace 0 (returnedCore k c 1) =
      (Real.sqrt ((k : ℝ)+1) : ℂ)*ChiralReturn.returned k c 1 := by
    rw [returned_core_trace]
    simp [ChiralReturn.returned,ChiralReturn.incident]
  rw [endpointBalance,hi,hr,norm_mul,norm_mul,mul_pow,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by positivity),
    (ChiralReturn.hasDerivAt_storage k c 1).deriv]
  simp only [Complex.ofReal_one,mul_one,Complex.normSq_eq_norm_sq]
  norm_cast
  ring

theorem endpoint_balance_opposite_negative :
    ∀ᶠ k : ℕ in atTop, endpointBalance k ![1,-1] < 0 := by
  filter_upwards [ChiralReturn.two_point_storage_nonnegative_but_endpoint_flux_negative] with k hk
  rw [endpoint_balance_is_native_flux]
  exact hk.2

theorem radial_pick_first_re_pos_eventually :
    ∀ᶠ k : ℕ in atTop, 0 < (completedNativeHermiteBiehlerChiralPickKernel
      (canonicalCompletedC3RadialTiltPoint k 0) (canonicalCompletedC3RadialTiltPoint k 0)).re := by
  have ha : Tendsto (fun k : ℕ => (k+1 : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun k => by dsimp; omega) tendsto_id
  have ht : Tendsto (fun k : ℕ => (radialMass k)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,radialMass,Nat.cast_add,Nat.cast_one] using
      tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp ha)
  have hw : Tendsto (fun k : ℕ => (radialMass k)⁻¹) atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun k => by
      simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using
        (inv_ne_zero (by unfold radialMass; positivity : radialMass k ≠ 0)))⟩
  have h := completedNativeHermiteBiehlerChiralPickKernel_central_diagonal_tendsto.comp hw
  have he (k : ℕ) : canonicalCompletedC3RadialTiltPoint k 0 =
      Complex.I * ((radialMass k)⁻¹ : ℝ) := by
    rw [canonicalCompletedC3RadialTiltPoint_eq_I_mul_im,canonicalCompletedC3RadialTiltPoint_im]
    simp [radialMass]
  have hh := (Complex.continuous_re.tendsto _).comp h
  have hp : (0 : ℝ) < 4*canonicalCompletedNativeLogDerivativeMoment 0 :=
    mul_pos (by norm_num) canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hp' := Tendsto.eventually_lt tendsto_const_nhds hh hp
  simpa only [Function.comp_def,← he,Complex.ofReal_re] using hp'

/-- Same scalar spectral parameter does NOT identify the material states.
The raw mixed-radial pairing differs strictly from the canonical Pick kernel. -/
theorem cross_radial_residual_re_negative_eventually :
    ∀ᶠ k : ℕ in atTop,
      (crossRadialDefect k (2*k+1) 0 1 -
        completedNativeHermiteBiehlerChiralPickKernel
          (canonicalCompletedC3RadialTiltPoint k 0) (canonicalCompletedC3RadialTiltPoint k 0)).re < 0 := by
  filter_upwards [radial_pick_first_re_pos_eventually] with k hk
  rw [cross_defect_same_point_residual]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr same_point_factor_lt_one) hk

end
end CarryCompletedTrace
