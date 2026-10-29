import PrincipalBoundaryLimit
namespace CarryBoundaryMargin
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- Existing N=4 coercivity transported to the SAME full physical source. -/
theorem physical_four_boundary_coercive :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ k : ℕ in atTop, ∀ x : ℕ →₀ ℂ,
      x.support ⊆ Finset.range 4 →
      ε*(∑ i : Fin 4, Complex.normSq
        (radialFourScaledBoundary (radialFourSourceStep k) (physicalValues k 4 x) i)) ≤
        2*(canonicalCompletedNativeProjectiveChiralForm
          (physicalCompletedFiniteSource k x) (physicalCompletedFiniteSource k x)).re := by
  obtain ⟨ε,he,hc⟩ := storage_one_fourSample_eventually_boundary_coercive
  refine ⟨ε,he,?_⟩
  filter_upwards [hc,canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk hreg
  intro x hx
  have hp := hk (physicalValues k 4 x)
  rw [physical_values_recover k 4 x (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)] at hp
  change ε*(∑ i : Fin 4, Complex.normSq
    (radialFourScaledBoundary (radialFourSourceStep k) (physicalValues k 4 x) i)) ≤
      (storage k (fun i : Fin 4 => incidentWeight k i*x i) 1).re at hp
  rw [original_source_storage k 4 x hx] at hp
  exact hp

/-- Uniform in a AFTER one common radial threshold: the margin cannot vanish.
It is a consequence of old N=4 source coercivity, not an all-order theorem. -/
theorem principal_uniform_physical_margin (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∃ μ : ℝ, 0<μ ∧ ∀ᶠ k : ℕ in atTop, ∀ a : ℝ,
      μ*(a^2+1) ≤ (crossGreenPair eta h0 h1 k k (principalInput a k) (principalInput a k)).re := by
  obtain ⟨ε,he,hc⟩ := physical_four_boundary_coercive
  refine ⟨ε/8,by positivity,?_⟩
  filter_upwards [hc,principal_boundary_eventually_lower] with k hk hb
  intro a
  have hs := hk (principalInput a k) (principal_support a k)
  change ε*(∑ i : Fin 4, Complex.normSq (principalBoundary a k i)) ≤ _ at hs
  have hm := mul_le_mul_of_nonneg_left (hb a) he.le
  rw [cross_green_eq_original]
  linarith

/-- A positive UNIFORM lower margin is passed to the known full-source limit.
No inference of strictness from eventual positivity is used. -/
theorem canonical_uniform_quadratic_margin :
    ∃ μ : ℝ, 0<μ ∧ ∀ a : ℝ,
      μ*(a^2+1) ≤ h 3-2*a*h 2+a^2*h 1 := by
  obtain ⟨μ,hm,hp⟩ := principal_uniform_physical_margin (1/2) (by norm_num) (by norm_num)
  refine ⟨μ,hm,?_⟩
  intro a
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (principal_physical_tendsto a a (1/2) (by norm_num) (by norm_num))
  have hlim : Tendsto (fun k : ℕ =>
      (crossGreenPair (1/2) (by norm_num) (by norm_num) k k (principalInput a k) (principalInput a k)).re)
      atTop (nhds (h 3-2*a*h 2+a^2*h 1)) := by
    simpa only [Function.comp_def,Complex.ofReal_re,two_mul,pow_two] using ht
  exact ge_of_tendsto hlim (hp.mono fun k hk => hk a)

/-- Concrete canonical consequence, with ONLY the algebraic nonzero denominator. -/
theorem canonical_second_shifted_schur_margin (hh : h 1≠0) :
    ∃ μ : ℝ, 0<μ ∧ μ*(1+(h 2/h 1)^2) ≤ h 3-h 2^2/h 1 := by
  obtain ⟨μ,hm,hp⟩ := canonical_uniform_quadratic_margin
  refine ⟨μ,hm,?_⟩
  have he := hp (h 2/h 1)
  have hid : h 3-2*(h 2/h 1)*h 2+(h 2/h 1)^2*h 1=h 3-h 2^2/h 1 := by
    field_simp [hh]
    ring
  rw [hid] at he
  nlinarith

end
end CarryBoundaryMargin
