import NativePrincipalFlux
import CarrySelfAdjointOperator.CompletedNativeChiralReturnFiniteTransfer
import CarrySelfAdjointOperator.NativePhysicalFiniteSewing
namespace CarryTailReturn
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000


/-- Only a name for the EXISTING quotient on the same actual radial address. -/
abbrev returnWeight (k j : ℕ) : ℂ := completedNativeHermiteBiehlerChiralQuotient
  (canonicalCompletedC3RadialTiltPoint k j)

/-- Finite coordinates of the same weighted source; the original sqrt(k+1)
amplitude belongs to radialIncidentVector, and is inserted ONCE. -/
def weightedIncident (k N : ℕ) (w : ℕ → ℂ) (x : ℕ →₀ ℂ) : RadialIncidentSpan k N :=
  radialIncidentVector k N (fun i => w i*x i)

theorem window_reconstruct (N : ℕ) (x : ℕ →₀ ℂ) (hx : x.support ⊆ Finset.range N) :
    finRadialCoefficients N (fun i => x i)=x := by
  ext j
  by_cases hj : j<N
  · exact finRadialCoefficients_apply N (fun i => x i) ⟨j,hj⟩
  · rw [finRadialCoefficients_outside _ _ _ (by omega),
      coefficient_outside_prefix x hx j (by omega)]

theorem weighted_window_reconstruct (N : ℕ) (w : ℕ → ℂ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) :
    finRadialCoefficients N (fun i => w i*x i)=coefficientWeight w x := by
  ext j
  by_cases hj : j<N
  · rw [coefficient_weight_apply]
    exact finRadialCoefficients_apply N (fun i => w i*x i) ⟨j,hj⟩
  · rw [finRadialCoefficients_outside _ _ _ (by omega),coefficient_weight_apply,
      coefficient_outside_prefix x hx j (by omega),mul_zero]

theorem finite_weighted_synthesis (N : ℕ) (w : ℕ → ℂ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) :
    physicalCauchySynthesis (coefficientWeight w x)=
      ∑ i : Fin N, (w i*x i) • completedNativeChiralCauchyFeature i := by
  rw [← weighted_window_reconstruct N w x hx,finRadialCoefficients,map_sum]
  simp only [physicalCauchySynthesis,Finsupp.linearCombination_single]

/-- The original finite incident domain contains the WHOLE weighted synthesis. -/
theorem weighted_incident_coe (k N : ℕ) (w : ℕ → ℂ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) :
    (weightedIncident k N w x : CanonicalCompletedNativeChiralCauchyCarrier)=
      (Real.sqrt ((k:ℝ)+1):ℂ) • physicalCauchySynthesis (coefficientWeight w x) := by
  rw [weightedIncident,radialIncidentVector_coe,finite_weighted_synthesis N w x hx]
  simp only [radialIncidentSynthesis,LinearMap.coe_mk,AddHom.coe_mk,
    completedNativeRadialChiralCauchyState,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- No new transfer: this is the prescribed native return on every finite span. -/
theorem weighted_incident_return (k N : ℕ) (w : ℕ → ℂ) (x : ℕ →₀ ℂ) :
    radialReturnTransfer k N (weightedIncident k N w x)=
      (weightedIncident k N (fun j => returnWeight k j*w j) x : CanonicalCompletedNativeChiralCauchyCarrier) := by
  simp only [weightedIncident,radialReturnTransfer_exact,radialIncidentVector_coe,
    radialReturnedSynthesis_eq_incident_multiply]
  congr 1
  funext i
  change (w i*x i)*returnWeight k i=(returnWeight k i*w i)*x i
  ring

theorem weighted_return_synthesis (k N : ℕ) (w : ℕ → ℂ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) :
    radialReturnTransfer k N (weightedIncident k N w x)=
      (Real.sqrt ((k:ℝ)+1):ℂ) • physicalCauchySynthesis
        (coefficientWeight (fun j => returnWeight k j*w j) x) := by
  rw [weighted_incident_return,weighted_incident_coe k N _ x hx]

/-- First-leg domain of the SAME original projectively twisted state. -/
def sourceIncident (k N : ℕ) (x : ℕ →₀ ℂ) : RadialIncidentSpan k N :=
  weightedIncident k N (incidentWeight k) x

theorem original_first_leg (k N : ℕ) (x : ℕ →₀ ℂ) (hx : x.support ⊆ Finset.range N) :
    (sourceIncident k N x : CanonicalCompletedNativeChiralCauchyCarrier)=
      (physicalCompletedFiniteSource k x).1 := by
  rw [sourceIncident,weighted_incident_coe k N _ x hx,completed_source_weighted_identity]

theorem original_return_leg (k N : ℕ) (x : ℕ →₀ ℂ) (hx : x.support ⊆ Finset.range N) :
    radialReturnTransfer k N (sourceIncident k N x)=(physicalCompletedFiniteSource k x).2 := by
  have hw : (fun j => returnWeight k j*incidentWeight k j)=returnedWeight k := by
    funext j
    unfold returnedWeight
    ring
  rw [sourceIncident,weighted_return_synthesis k N _ x hx,hw,completed_source_weighted_identity]

/-- Full vector graph identity, before any quadratic readout. -/
theorem original_source_graph (k N : ℕ) (x : ℕ →₀ ℂ) (hx : x.support ⊆ Finset.range N) :
    physicalCompletedFiniteSource k x=
      ((sourceIncident k N x : CanonicalCompletedNativeChiralCauchyCarrier),
        radialReturnTransfer k N (sourceIncident k N x)) := by
  rw [original_first_leg k N x hx,original_return_leg k N x hx]

end
end CarryTailReturn
