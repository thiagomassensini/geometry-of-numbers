import ExplicitNewtonInput
namespace CarryEulerNewton
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarryCriticalComplete CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Explicit Euler-to-Newton map of the EXISTING four-jet charts. The
coefficients 1,3,2,6,11,6 are the shifted falling-factorial coefficients. -/
def eulerToNewton (t : ℝ) (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun m => (Real.sqrt 2:ℂ) *
    ![v 0,Complex.I*(v 1-(t:ℂ)*v 0),
      v 2-3*(t:ℂ)*v 1+2*(t:ℂ)^2*v 0,
      Complex.I*(v 3-6*(t:ℂ)*v 2+11*(t:ℂ)^2*v 1-6*(t:ℂ)^3*v 0)] m

/-- Explicit reverse map. These coordinates are not asserted isometric. -/
def newtonToEuler (t : ℝ) (y : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun m => ![y 0,(t:ℂ)*y 0-Complex.I*y 1,
      (t:ℂ)^2*y 0-3*Complex.I*(t:ℂ)*y 1+y 2,
      (t:ℂ)^3*y 0-7*Complex.I*(t:ℂ)^2*y 1+6*(t:ℂ)*y 2-Complex.I*y 3] m/(Real.sqrt 2:ℂ)

theorem newton_euler_inverse (t : ℝ) (v : Fin 4 → ℂ) :
    newtonToEuler t (eulerToNewton t v)=v := by
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  funext i
  fin_cases i <;> dsimp [eulerToNewton,newtonToEuler] <;> field_simp [hs] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem euler_newton_inverse (t : ℝ) (y : Fin 4 → ℂ) :
    eulerToNewton t (newtonToEuler t y)=y := by
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  funext i
  fin_cases i <;> dsimp [eulerToNewton,newtonToEuler] <;> field_simp [hs] <;>
    ring_nf <;> norm_num [Complex.I_sq]

/-- Source provenance: applying the explicit map to the old Euler chart
recovers the explicit Newton coefficients of the SAME physical source. -/
theorem source_euler_newton_exact (k : ℕ) (x : ℕ →₀ ℂ)
    (hF : ∀ i : Fin 4, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin 4, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    fourNewtonCoordinates k (fun r : Fin 4 => x r)=
      eulerToNewton (radialFourSourceStep k) (sourceBoundary k x) := by
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  rw [sourceBoundary,physical_values_eq k 4 x hF hP]
  funext i
  fin_cases i <;> norm_num [fourNewtonCoordinates,nativeSourceJetOrderPhase,
    canonicalCompletedC3RadialSecondStep,canonicalGreenJetStep_eq_radialFourSourceStep,
    eulerToNewton,radialFourScaledBoundary,radialEulerBoundaryJet,Fin.sum_univ_succ] <;>
    field_simp [hs] <;> ring_nf <;> norm_num [Complex.I_sq]

theorem euler_newton_eventually_exact :
    ∀ᶠ k : ℕ in atTop, ∀ x : ℕ →₀ ℂ,
      fourNewtonCoordinates k (fun r : Fin 4 => x r)=
        eulerToNewton (radialFourSourceStep k) (sourceBoundary k x) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk
  intro x
  exact source_euler_newton_exact k x (fun i => (hk i).2.1) (fun i => (hk i).2.2)

/-- Moving Euler vectors are transported BEFORE any scalar energy readout. -/
theorem euler_to_newton_path_tendsto (v : ℕ → Fin 4 → ℂ) (w : Fin 4 → ℂ)
    (hv : Tendsto v atTop (nhds w)) :
    Tendsto (fun k => eulerToNewton (radialFourSourceStep k) (v k)) atTop
      (nhds (eulerToNewton 0 w)) := by
  have hc : Continuous (fun p : ℝ × (Fin 4 → ℂ) => eulerToNewton p.1 p.2) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [eulerToNewton] <;> fun_prop
  have ht := hc.continuousAt.tendsto.comp (radialFourSourceStep_tendsto_zero.prodMk_nhds hv)
  simpa only [Function.comp_def] using ht

end
end CarryEulerNewton
