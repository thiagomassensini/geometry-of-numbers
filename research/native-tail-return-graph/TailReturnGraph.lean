import FiniteReturnDomain
namespace CarryTailReturn
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000


/-- First leg of the isotropic tail in the actual finite return domain.
No amplitude or phase is duplicated. -/
def tailIncident (e v q a : ℝ) (k N : ℕ) : RadialIncidentSpan k N :=
  weightedIncident k N (fun j => chiralDifference*responseTail e v q k j) (principalInput a k)

theorem principal_prefix (a : ℝ) (k N : ℕ) (hN : 4 ≤ N) :
    (principalInput a k).support ⊆ Finset.range N :=
  (principal_support a k).trans (Finset.range_mono hN)

theorem tail_first_leg (e v q a : ℝ) (k N : ℕ) (hN : 4 ≤ N) :
    (tailIncident e v q a k N : CanonicalCompletedNativeChiralCauchyCarrier)=
      (tailComponent e v q a k).1 := by
  have hw : coefficientWeight (fun j => chiralDifference*responseTail e v q k j) (principalInput a k)=
      chiralDifference • coefficientWeight (responseTail e v q k) (principalInput a k) := by
    ext j
    simp only [coefficient_weight_apply,Finsupp.smul_apply,smul_eq_mul]
    ring
  rw [tailIncident,weighted_incident_coe k N _ _ (principal_prefix a k N hN),hw,map_smul,smul_smul]
  rfl

/-- First leg of the head is also in the SAME domain. -/
def headIncident (e v q a : ℝ) (k N : ℕ) : RadialIncidentSpan k N :=
  sourceIncident k N (principalInput a k)-tailIncident e v q a k N

theorem head_first_leg (e v q a : ℝ) (k N : ℕ) (hN : 4 ≤ N) :
    (headIncident e v q a k N : CanonicalCompletedNativeChiralCauchyCarrier)=
      (headComponent e v q a k).1 := by
  simp only [headIncident,Submodule.coe_sub,original_first_leg k N _ (principal_prefix a k N hN),
    tail_first_leg e v q a k N hN,headComponent,Prod.fst_sub]

/-- Defect is a vector in the original carrier, not a norm or a new metric. -/
def tailReturnDefect (e v q a : ℝ) (k N : ℕ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  (tailIncident e v q a k N : CanonicalCompletedNativeChiralCauchyCarrier)-
    radialReturnTransfer k N (tailIncident e v q a k N)

theorem weighted_return_defect (k N : ℕ) (w : ℕ → ℂ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range N) :
    (weightedIncident k N w x : CanonicalCompletedNativeChiralCauchyCarrier)-
      radialReturnTransfer k N (weightedIncident k N w x)=
        (Real.sqrt ((k:ℝ)+1):ℂ) • physicalCauchySynthesis
          (coefficientWeight (fun j => (1-returnWeight k j)*w j) x) := by
  have hc : coefficientWeight w x-coefficientWeight (fun j => returnWeight k j*w j) x=
      coefficientWeight (fun j => (1-returnWeight k j)*w j) x := by
    ext j
    simp only [Finsupp.sub_apply,coefficient_weight_apply]
    ring
  rw [weighted_incident_coe k N _ x hx,weighted_return_synthesis k N _ x hx,
    ← smul_sub,← map_sub,hc]

/-- Exact native return defect, all finite N>=4, full original response tail. -/
theorem tail_return_defect_synthesis (e v q a : ℝ) (k N : ℕ) (hN : 4 ≤ N) :
    tailReturnDefect e v q a k N=
      ((Real.sqrt ((k:ℝ)+1):ℂ)*chiralDifference) • physicalCauchySynthesis
        (coefficientWeight (fun j => (1-returnWeight k j)*responseTail e v q k j) (principalInput a k)) := by
  have hc : coefficientWeight (fun j => (1-returnWeight k j)*(chiralDifference*responseTail e v q k j)) (principalInput a k)=
      chiralDifference • coefficientWeight (fun j => (1-returnWeight k j)*responseTail e v q k j) (principalInput a k) := by
    ext j
    simp only [coefficient_weight_apply,Finsupp.smul_apply,smul_eq_mul]
    ring
  rw [tailReturnDefect,tailIncident,weighted_return_defect k N _ _ (principal_prefix a k N hN),hc,map_smul,smul_smul]

theorem tail_graph_defect (e v q a : ℝ) (k N : ℕ) (hN : 4 ≤ N) :
    (tailComponent e v q a k).2-radialReturnTransfer k N (tailIncident e v q a k N)=
      tailReturnDefect e v q a k N := by
  unfold tailReturnDefect
  rw [tail_first_leg e v q a k N hN]
  rfl

/-- The head and tail have OPPOSITE defects; only their sum is the original graph. -/
theorem head_graph_defect (e v q a : ℝ) (k N : ℕ) (hN : 4 ≤ N) :
    (headComponent e v q a k).2-radialReturnTransfer k N (headIncident e v q a k N)=
      -tailReturnDefect e v q a k N := by
  simp only [headComponent,Prod.snd_sub,headIncident,map_sub,
    original_return_leg k N _ (principal_prefix a k N hN)]
  unfold tailReturnDefect
  rw [tail_first_leg e v q a k N hN]
  change ((physicalCompletedFiniteSource k (principalInput a k)).2-(tailComponent e v q a k).1)-
    ((physicalCompletedFiniteSource k (principalInput a k)).2-
      radialReturnTransfer k N (tailIncident e v q a k N))=_
  abel

/-- No sign or contraction premise: regularity alone excludes quotient=1. -/
theorem native_quotient_ne_one (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate z≠0) :
    completedNativeHermiteBiehlerChiralQuotient z≠1 := by
  intro he
  unfold completedNativeHermiteBiehlerChiralQuotient at he
  have hc := congrArg (fun w : ℂ => w*completedNativePositiveHermiteBiehlerCoordinate z) he
  field_simp [hP] at hc
  unfold completedNativeNegativeHermiteBiehlerCoordinate completedNativePositiveHermiteBiehlerCoordinate at hc
  have hi : Complex.I*completedNativeOperatorCharacteristic z=0 := by
    linear_combination -(1/2:ℂ)*hc
  exact hF ((mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero)

/-- The ORIGINAL completed response is the Cayley coordinate of the actual
return quotient. This is before moments, not a fitted spectral operator. -/
theorem native_return_response_relation (k j : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0) :
    1+returnWeight k j=2*responseSamples (radialStep k) j*(1-returnWeight k j) := by
  have hA := incident_amplitude_response (canonicalCompletedC3RadialTiltPoint k j) hF
  change incidentWeight k j=(2*responseWeight k j+Complex.I)/(Real.sqrt 2:ℂ) at hA
  rw [response_radial_readout] at hA
  change incidentWeight k j=(2*(Complex.I*responseSamples (radialStep k) j)+Complex.I)/(Real.sqrt 2:ℂ) at hA
  have hD := radial_weight_difference k j hF hP
  unfold returnedWeight chiralDifference at hD
  have hne : incidentWeight k j≠0 := completedNativeNormalizedPositiveChiralAmplitude_ne_zero hF hP
  have he : incidentWeight k j*((1+returnWeight k j)-2*responseSamples (radialStep k) j*(1-returnWeight k j))=0 := by
    change incidentWeight k j-incidentWeight k j*returnWeight k j=2*Complex.I/(Real.sqrt 2:ℂ) at hD
    linear_combination 2*hA-(1+2*responseSamples (radialStep k) j)*hD
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hne)

theorem native_return_cayley_coordinate (k j : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0) :
    (1+returnWeight k j)/(1-returnWeight k j)=2*responseSamples (radialStep k) j := by
  have hn : 1-returnWeight k j≠0 :=
    sub_ne_zero.mpr (Ne.symm (native_quotient_ne_one _ hF hP))
  exact (div_eq_iff hn).mpr (native_return_response_relation k j hF hP)

/-- Typed vector Cayley relation on every finite original incident domain.
No inverse matrix, metric change or canonical moment is used. -/
theorem weighted_cayley_vector (k N : ℕ) (x : ℕ →₀ ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    (weightedIncident k N (fun _ => 1) x : CanonicalCompletedNativeChiralCauchyCarrier)+
      radialReturnTransfer k N (weightedIncident k N (fun _ => 1) x)=
      (2:ℂ) • (weightedIncident k N (responseSamples (radialStep k))
        (coefficientWeight (fun j => 1-returnWeight k j) x) : CanonicalCompletedNativeChiralCauchyCarrier) := by
  rw [weighted_incident_return]
  simp only [weightedIncident,radialIncidentVector_coe]
  rw [← map_add,← map_smul]
  congr 1
  funext i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,coefficient_weight_apply,one_mul,mul_one]
  have he := native_return_response_relation k i (hF i) (hP i)
  linear_combination (x i)*he

/-- Finite return has no nonzero fixed vector on a regular prefix.
This does NOT imply contractivity in the Cauchy metric. -/
theorem native_return_fixed_iff_zero (k N : ℕ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (x : RadialIncidentSpan k N) :
    radialReturnTransfer k N x=(x : CanonicalCompletedNativeChiralCauchyCarrier) ↔ x=0 := by
  constructor
  · intro hx
    obtain ⟨c,rfl⟩ := (radialIncidentCoordinates k N).symm.surjective x
    change radialReturnTransfer k N (radialIncidentVector k N c)=
      (radialIncidentVector k N c : CanonicalCompletedNativeChiralCauchyCarrier) at hx
    rw [radialReturnTransfer_exact,radialIncidentVector_coe,radialReturnedSynthesis_eq_incident_multiply] at hx
    have he := radialIncidentSynthesis_injective k N hx
    have hc : c=0 := by
      funext i
      have hi := congrFun he i
      have hq := native_quotient_ne_one _ (hF i) (hP i)
      have hp : c i*(completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i)-1)=0 := by
        linear_combination hi
      exact (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hq)
    simp [hc]
  · intro hx
    simp [hx]

/-- E=(z,z) lies in the native return graph only when E is zero.
Its FIRST leg is nevertheless in the return domain. -/
theorem tail_in_graph_iff_zero (e v q a : ℝ) (k N : ℕ) (hN : 4 ≤ N)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    radialReturnTransfer k N (tailIncident e v q a k N)=(tailComponent e v q a k).2 ↔
      tailComponent e v q a k=0 := by
  change radialReturnTransfer k N (tailIncident e v q a k N)=(tailComponent e v q a k).1 ↔ _
  rw [← tail_first_leg e v q a k N hN,native_return_fixed_iff_zero k N hF hP]
  constructor
  · intro hz
    have hc := congrArg (fun x : RadialIncidentSpan k N => (x : CanonicalCompletedNativeChiralCauchyCarrier)) hz
    rw [tail_first_leg e v q a k N hN] at hc
    apply Prod.ext <;> exact hc
  · intro hz
    apply Subtype.ext
    rw [tail_first_leg e v q a k N hN,hz]
    rfl

/-- The graph obstruction holds in EVERY fixed finite order after actual regularity. -/
theorem tail_in_graph_eventually_iff_zero (e v q a : ℝ) (N : ℕ) (hN : 4 ≤ N) :
    ∀ᶠ k : ℕ in atTop,
      (radialReturnTransfer k N (tailIncident e v q a k N)=(tailComponent e v q a k).2 ↔
        tailComponent e v q a k=0) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hk
  exact tail_in_graph_iff_zero e v q a k N hN (fun i => (hk i).2.1) (fun i => (hk i).2.2)

end
end CarryTailReturn
