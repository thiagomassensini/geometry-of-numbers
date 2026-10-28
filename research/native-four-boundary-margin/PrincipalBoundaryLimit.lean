import PhysicalBoundaryCoordinates
namespace CarryBoundaryMargin
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- Explicit evaluation of the existing boundary chart; no fitted vectors. -/
def boundaryTemplate (a t : ℝ) : Fin 4 → ℂ :=
  fun i => Complex.I*((![0,a,10*a*t,1+77*a*t^2] i/Real.sqrt 2 : ℝ):ℂ)

/-- Coordinate limit in the existing four-jet chart, not a new physical metric. -/
def boundaryLimit (a : ℝ) : Fin 4 → ℂ := boundaryTemplate a 0

theorem principal_boundary_exact (a : ℝ) (k : ℕ)
    (hF : ∀ i : Fin 4, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin 4, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    principalBoundary a k=boundaryTemplate a (radialFourSourceStep k) := by
  have hk : ((k:ℂ)+1)≠0 := by exact_mod_cast (by positivity : (k:ℝ)+1≠0)
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  rw [principalBoundary,physical_values_eq k 4 (principalInput a k) hF hP]
  funext i
  fin_cases i <;>
    norm_num [radialFourScaledBoundary,radialEulerBoundaryJet,principal_coefficient_formula,
      Fin.sum_univ_succ,radialFourSourceStep,boundaryTemplate] <;>
    field_simp [hk,hs] <;> ring

theorem principal_boundary_eventually_exact :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℝ,
      principalBoundary a k=boundaryTemplate a (radialFourSourceStep k) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk
  intro a
  exact principal_boundary_exact a k (fun i => (hk i).2.1) (fun i => (hk i).2.2)

theorem boundary_template_continuous (a : ℝ) : Continuous (boundaryTemplate a) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [boundaryTemplate] <;> fun_prop

/-- Full boundary vector converges BEFORE any squared norm/readout is taken. -/
theorem principal_boundary_tendsto (a : ℝ) :
    Tendsto (principalBoundary a) atTop (nhds (boundaryLimit a)) := by
  have ht := (boundary_template_continuous a).continuousAt.tendsto.comp radialFourSourceStep_tendsto_zero
  apply ht.congr'
  filter_upwards [principal_boundary_eventually_exact] with k hk
  exact (hk a).symm

/-- Exact Euclidean size in the old coercive boundary coordinates. -/
theorem boundary_template_norm_sq (a t : ℝ) :
    (∑ i : Fin 4, Complex.normSq (boundaryTemplate a t i))=
      (a^2+(10*a*t)^2+(1+77*a*t^2)^2)/2 := by
  have hs : (Real.sqrt 2)⁻¹^2=(1/2:ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  norm_num [boundaryTemplate,Fin.sum_univ_succ,Complex.normSq_apply]
  ring_nf
  simp only [hs]
  ring

theorem boundary_limit_norm_sq (a : ℝ) :
    (∑ i : Fin 4, Complex.normSq (boundaryLimit a i))=(a^2+1)/2 := by
  rw [boundaryLimit,boundary_template_norm_sq]
  ring

theorem boundary_limit_ne_zero (a : ℝ) : boundaryLimit a≠0 := by
  intro hz
  have he := boundary_limit_norm_sq a
  simp [hz] at he
  nlinarith [sq_nonneg a]

/-- Elementary shear estimate. It does not assume a moment or source sign. -/
theorem boundary_shear_lower (a c : ℝ) (hc : c^2≤1/2) :
    (a^2+1)/2 ≤ a^2+(1+c*a)^2 := by
  have hp := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg a)
  nlinarith [sq_nonneg (1+2*c*a)]

/-- ONE radial threshold for ALL real a, using the exact vector formula. -/
theorem principal_boundary_eventually_lower :
    ∀ᶠ k : ℕ in atTop, ∀ a : ℝ,
      (a^2+1)/4 ≤ ∑ i : Fin 4, Complex.normSq (principalBoundary a k i) := by
  have ht : Tendsto (fun k : ℕ => (77*(radialFourSourceStep k)^2)^2) atTop (nhds (0:ℝ)) := by
    simpa using ((radialFourSourceStep_tendsto_zero.pow 2).const_mul 77).pow 2
  have hs := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hs,principal_boundary_eventually_exact] with k hk he
  intro a
  rw [he a,boundary_template_norm_sq]
  have hb := boundary_shear_lower a (77*(radialFourSourceStep k)^2) hk.le
  nlinarith [sq_nonneg (10*a*radialFourSourceStep k)]

end
end CarryBoundaryMargin
