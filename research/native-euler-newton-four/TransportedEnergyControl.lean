import CriticalJetTransport
import CriticalCompleteMargin
namespace CarryEulerNewton
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarryCriticalComplete CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Existing all-finite-order error control, now applied by EXPLICIT coefficients
to every original four-address physical source. No positivity premise. -/
theorem four_source_explicit_energy_control (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x : ℕ →₀ ℂ, x.support ⊆ Finset.range 4 →
      |4*(canonicalCompletedNativeProjectiveChiralForm
          (physicalCompletedFiniteSource k x) (physicalCompletedFiniteSource k x)).re-
        nativeSourceFiniteBoundaryEnergy 4 (fourNewtonCoordinates k (fun r : Fin 4 => x r))|≤
          ε*‖fourNewtonCoordinates k (fun r : Fin 4 => x r)‖^2 := by
  filter_upwards [storage_one_chiralJetInput_eventually_energy_control 2 ε he] with k hk
  intro x hx
  have hs := hk (fourNewtonCoordinates k (fun r : Fin 4 => x r))
  rw [four_newton_input_exact,original_source_storage k 4 x hx] at hs
  simpa only [← mul_assoc,show (2:ℝ)*2=4 by norm_num] using hs

/-- The norm is the native Pi norm of the constant jet coefficients. It is
not identified with a new norm on the physical Cauchy carrier. -/
theorem critical_jet_norm_sq_le (a : ℝ) : ‖criticalJet a‖^2≤a^2+1 := by
  have hn : ‖criticalJet a‖≤Real.sqrt (a^2+1) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    fin_cases i <;> norm_num [criticalJet]
    all_goals first | positivity | (apply Real.le_sqrt_of_sq_le; nlinarith [sq_abs a])
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [Real.sq_sqrt (by positivity)] at hp
  exact hp

/-- Weighted uniform convergence for the full critical source, transported
from the native jet theorem. One radial threshold for all real a. -/
theorem critical_uniform_energy_control (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℝ,
      |4*(crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource a k)).re-
        nativeSourceFiniteBoundaryEnergy 4 (criticalJet a)|≤ε*(1+a^2) := by
  filter_upwards [four_source_explicit_energy_control ε he] with k hk
  intro a
  have hs := hk (criticalOddSource a k) (critical_four_support a k)
  rw [critical_newton_coordinates] at hs
  have hb := hs.trans (mul_le_mul_of_nonneg_left (critical_jet_norm_sq_le a) he.le)
  simpa only [cross_green_eq_original,add_comm] using hb

/-- Exact normalization dictionary between the two ORIGINAL limiting
boundary readouts, obtained from their common full physical source. -/
theorem critical_boundary_energy_dictionary (a : ℝ) :
    nativeSourceFiniteBoundaryEnergy 4 (criticalJet a)=
      2*nativeSourceFourBoundaryEnergy (boundaryLimit a) := by
  have hn := nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto 2 (criticalJet a)
  simp only [← nativeSourceProjectiveBoundaryJetSynthesis_energy] at hn
  simp only [← critical_source_fixed_jet a] at hn
  have he := (critical_native_energy_limit a (1/2) (by norm_num) (by norm_num)).const_mul (4:ℝ)
  simp only [cross_green_eq_original] at he
  have hf : Tendsto (fun k : ℕ => 4*(canonicalCompletedNativeProjectiveChiralForm
        (physicalCompletedFiniteSource k (criticalOddSource a k))
        (physicalCompletedFiniteSource k (criticalOddSource a k))).re)
      atTop (nhds (2*nativeSourceFourBoundaryEnergy (boundaryLimit a))) := by
    convert he using 1
    ring
  exact tendsto_nhds_unique hn hf

end
end CarryEulerNewton
