import PrimeAnalysis
import CarrySelfAdjointOperator.CompletedNativeCentralChiralQuotientCurvature

/-! A necessary test of the literal raw-return identification. The existing
prime analysis has a fixed strict contraction bound. The original native
chiral return approaches equal energy, so two isometric ports cannot make
them the same map, even on one untouched radial Cauchy column. -/
namespace CarrySourcePrime
open CarrySelfAdjointOperator CPFormal.Analytic.Cp Filter Topology
open CarrySelfAdjointOperator.RealFirstNative
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Original complete quotient at every fixed material address. -/
theorem native_return_ratio_limit (j : ℕ) :
    Tendsto (fun k : ℕ => ‖completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k j)‖^2) atTop (nhds 1) := by
  have h := hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero_raw.continuousAt.tendsto.comp
    (canonicalCompletedC3RadialTiltPoint_tendsto_zero j)
  simpa using h.norm.pow 2

theorem native_incident_energy_pos (k j : ℕ) :
    0<‖completedNativeRadialChiralCauchyState k j‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ), inner_completedNativeRadialChiralCauchyState]
  change 0<((k:ℝ)+1)*(((j+j+2:ℕ):ℝ)⁻¹)
  exact mul_pos (by positivity) (inv_pos.mpr (by positivity))

/-- Every fixed margin below one eventually fails on the unchanged source. -/
theorem native_return_exceeds_fixed_fraction (j : ℕ) (ρ : ℝ) (hρ : ρ<1) :
    ∀ᶠ k : ℕ in atTop,
      ρ*‖completedNativeRadialChiralCauchyState k j‖^2 <
        ‖completedNativeRadialChiralMultiplierState k j‖^2 := by
  filter_upwards [(native_return_ratio_limit j).eventually (lt_mem_nhds hρ)] with k hk
  rw [completedNativeRadialChiralMultiplierState,norm_smul,mul_pow]
  exact mul_lt_mul_of_pos_right hk (native_incident_energy_pos k j)

/-- Even different isometric incident/return ports cannot identify the raw
native return with the existing prime contraction. This is a NO-GO only
for this specific norm-preserving intertwining. -/
theorem no_eventual_isometric_prime_return (j : ℕ)
    (L : CanonicalCompletedNativeChiralCauchyCarrier →ₗᵢ[ℝ] NativeGpreTowerHilbert)
    (W : CanonicalCompletedNativeChiralCauchyCarrier →ₗᵢ[ℝ] PrimeCarryDefectGlobalHilbert) :
    ¬ ∀ᶠ k : ℕ in atTop,
      W (completedNativeRadialChiralMultiplierState k j)=
        primeContractionLinear (L (completedNativeRadialChiralCauchyState k j)) := by
  intro he
  have hf : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [he,native_return_exceeds_fixed_fraction j (11/12) (by norm_num)] with k hk hbad
    have hbound := nativeGprePrimeCarryDefectState_norm_sq_le
      (L (completedNativeRadialChiralCauchyState k j))
    have hn := congrArg (fun x : PrimeCarryDefectGlobalHilbert => ‖x‖^2) hk
    rw [W.norm_map] at hn
    rw [L.norm_map] at hbound
    change ‖completedNativeRadialChiralMultiplierState k j‖^2=
      ‖nativeGprePrimeCarryDefectState (L (completedNativeRadialChiralCauchyState k j))‖^2 at hn
    rw [hn] at hbad
    exact (not_lt_of_ge hbound) hbad
  exact hf.exists.elim (fun _ h => h)

/-- Enlarging or changing the finite prime atlas with k cannot cure this
specific mismatch; the SAME strict estimate holds for every atlas. -/
theorem no_eventual_isometric_finite_prime_return (j : ℕ) (S : ℕ → Finset Nat.Primes)
    (L : CanonicalCompletedNativeChiralCauchyCarrier →ₗᵢ[ℝ] NativeGpreTowerHilbert)
    (W : CanonicalCompletedNativeChiralCauchyCarrier →ₗᵢ[ℝ] PrimeCarryDefectGlobalHilbert) :
    ¬ ∀ᶠ k : ℕ in atTop,
      W (completedNativeRadialChiralMultiplierState k j)=
        primeAnalysis (S k) (L (completedNativeRadialChiralCauchyState k j)) := by
  intro he
  have hf : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [he,native_return_exceeds_fixed_fraction j (11/12) (by norm_num)] with k hk hbad
    have hbound := prime_analysis_norm_sq_le (S k)
      (L (completedNativeRadialChiralCauchyState k j))
    have hn := congrArg (fun x : PrimeCarryDefectGlobalHilbert => ‖x‖^2) hk
    rw [W.norm_map] at hn
    rw [L.norm_map] at hbound
    rw [hn] at hbad
    exact (not_lt_of_ge hbound) hbad
  exact hf.exists.elim (fun _ h => h)

end
end CarrySourcePrime
