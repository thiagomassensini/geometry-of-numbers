import TailReturnGraph
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEnergyPort
namespace CarryTailReturn
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000


/-- Graph defect of a pair whose first leg is in the EXISTING finite domain. -/
def returnGraphDefect (k N : ℕ) (x : RadialIncidentSpan k N)
    (y : CanonicalCompletedNativeChiralCauchyCarrier) : CanonicalCompletedNativeChiralCauchyCarrier :=
  y-radialReturnTransfer k N x

/-- Entire polarized energy balance for non-graph pairs. The two mixed terms
and the defect-defect term cannot be deleted from head or tail. -/
theorem graph_defect_polarized_balance (k N : ℕ) (x x' : RadialIncidentSpan k N)
    (y y' : CanonicalCompletedNativeChiralCauchyCarrier) :
    2*canonicalCompletedNativeProjectiveChiralForm
      ((x:CanonicalCompletedNativeChiralCauchyCarrier),y) ((x':CanonicalCompletedNativeChiralCauchyCarrier),y')=
      inner ℂ x (radialReturnEnergyDefect k N x')-
        inner ℂ (radialReturnTransfer k N x) (returnGraphDefect k N x' y')-
        inner ℂ (returnGraphDefect k N x y) (radialReturnTransfer k N x')-
        inner ℂ (returnGraphDefect k N x y) (returnGraphDefect k N x' y') := by
  rw [radialReturnEnergyDefect_pairing]
  unfold canonicalCompletedNativeProjectiveChiralForm returnGraphDefect
  simp only [inner_sub_left,inner_sub_right]
  norm_num
  ring

/-- A diagonal two-leg component has zero signed form, but its actual RETURN
energy defect is balanced by all three graph-defect crossings. -/
theorem diagonal_pair_return_energy (k N : ℕ) (x y : RadialIncidentSpan k N) :
    inner ℂ x (radialReturnEnergyDefect k N y)=
      inner ℂ (radialReturnTransfer k N x)
        ((y:CanonicalCompletedNativeChiralCauchyCarrier)-radialReturnTransfer k N y)+
      inner ℂ ((x:CanonicalCompletedNativeChiralCauchyCarrier)-radialReturnTransfer k N x)
        (radialReturnTransfer k N y)+
      inner ℂ ((x:CanonicalCompletedNativeChiralCauchyCarrier)-radialReturnTransfer k N x)
        ((y:CanonicalCompletedNativeChiralCauchyCarrier)-radialReturnTransfer k N y) := by
  rw [radialReturnEnergyDefect_pairing]
  change inner ℂ (x:CanonicalCompletedNativeChiralCauchyCarrier)
    (y:CanonicalCompletedNativeChiralCauchyCarrier)-_=_
  simp only [inner_sub_left,inner_sub_right]
  ring

/-- Exact identification with the source energy defect for ANY finite order.
This is an identity, with no sign of the defect presumed. -/
theorem original_source_energy_pairing (k N : ℕ) (x y : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) (hy : y.support ⊆ Finset.range N) :
    inner ℂ (sourceIncident k N x) (radialReturnEnergyDefect k N (sourceIncident k N y))=
      2*canonicalCompletedNativeProjectiveChiralForm (physicalCompletedFiniteSource k x) (physicalCompletedFiniteSource k y) := by
  rw [radialReturnEnergyDefect_pairing,original_return_leg k N x hx,original_return_leg k N y hy]
  change inner ℂ (sourceIncident k N x : CanonicalCompletedNativeChiralCauchyCarrier)
      (sourceIncident k N y : CanonicalCompletedNativeChiralCauchyCarrier)-_=_
  rw [original_first_leg k N x hx,original_first_leg k N y hy]
  unfold canonicalCompletedNativeProjectiveChiralForm
  ring

/-- CONDITIONAL positive port transport. Contractivity is discharged only in
the separate four-source bridge; it is not an all-order conclusion here. -/
theorem original_source_port_pairing (k N : ℕ) (x y : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) (hy : y.support ⊆ Finset.range N)
    (hcontract : ‖radialReturnTransfer k N‖ ≤ 1) :
    inner ℂ (radialReturnEnergyPort k N (sourceIncident k N x))
      (radialReturnEnergyPort k N (sourceIncident k N y))=
        2*canonicalCompletedNativeProjectiveChiralForm (physicalCompletedFiniteSource k x) (physicalCompletedFiniteSource k y) := by
  rw [radialReturnEnergyPort_inner k N hcontract,← radialReturnEnergyDefect_pairing]
  exact original_source_energy_pairing k N x y hx hy

theorem signed_diagonal_norm (u : CanonicalCompletedNativeProjectiveChiralCarrier) :
    2*(canonicalCompletedNativeProjectiveChiralForm u u).re=‖u.1‖^2-‖u.2‖^2 := by
  rw [← inner_self_eq_norm_sq (𝕜:=ℂ) u.1,← inner_self_eq_norm_sq (𝕜:=ℂ) u.2]
  have hh : (2:ℂ)⁻¹=((1/2:ℝ):ℂ) := by norm_num
  unfold canonicalCompletedNativeProjectiveChiralForm
  rw [hh,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.sub_re]
  ring
  rfl

/-- The original storage certificate and the physical source use the SAME
coefficient vector, including the projective amplitude exactly once. -/
theorem original_source_storage (k N : ℕ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) :
    (storage k (fun i : Fin N => incidentWeight k i*x i) 1).re=
      2*(canonicalCompletedNativeProjectiveChiralForm (physicalCompletedFiniteSource k x)
        (physicalCompletedFiniteSource k x)).re := by
  rw [storage_one_eq_finiteTransfer_energy]
  change ‖sourceIncident k N x‖^2-‖radialReturnTransfer k N (sourceIncident k N x)‖^2=_
  change ‖(sourceIncident k N x : CanonicalCompletedNativeChiralCauchyCarrier)‖^2-_= _
  rw [original_first_leg k N x hx,original_return_leg k N x hx,← signed_diagonal_norm]

/-- The literal tail, now with its domain verified, obeys the full polarized
return-defect cancellation. Isotropy is not zero positive port energy. -/
theorem tail_energy_defect_cancellation (e v q a b : ℝ) (k N : ℕ) :
    inner ℂ (tailIncident e v q a k N)
      (radialReturnEnergyDefect k N (tailIncident e v q b k N))=
      inner ℂ (radialReturnTransfer k N (tailIncident e v q a k N)) (tailReturnDefect e v q b k N)+
      inner ℂ (tailReturnDefect e v q a k N) (radialReturnTransfer k N (tailIncident e v q b k N))+
      inner ℂ (tailReturnDefect e v q a k N) (tailReturnDefect e v q b k N) :=
  diagonal_pair_return_energy k N _ _

end
end CarryTailReturn
