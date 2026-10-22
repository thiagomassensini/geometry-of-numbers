import ConservativeDefect
import WholeSourceLimit
import CriticalGreen

/-! The original finite jet synthesis is codomain-restricted to the closure
it already belongs to. Coercion is an exact vector equality, before readout. -/
namespace CarryConservativeIntertwiner
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre ChiralReturn
open CarryCriticalRelative CarryForcingResidual NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis
open Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def physicalIncident (n k : ℕ) (x : Fin (2*n) → ℂ) : PhysicalCauchySpace :=
  physicalOriginalIncident k (nativeSourceChiralJetInput n k x) 1

def physicalReturned (n k : ℕ) (x : Fin (2*n) → ℂ) : PhysicalCauchySpace :=
  physicalOriginalReturned k (nativeSourceChiralJetInput n k x) 1

theorem physicalIncident_coe (n k : ℕ) (x : Fin (2*n) → ℂ) :
    (physicalIncident n k x : CanonicalCompletedNativeChiralCauchyCarrier) =
      (nativeSourceProjectiveBoundaryJetSynthesis n k x).1 := by
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource]
  simp only [physicalIncident,physicalOriginalIncident,radialIncidentSynthesis,
    LinearMap.coe_mk,AddHom.coe_mk,Complex.ofReal_one,one_pow,mul_one]

theorem physicalReturned_coe (n k : ℕ) (x : Fin (2*n) → ℂ) :
    (physicalReturned n k x : CanonicalCompletedNativeChiralCauchyCarrier) =
      (nativeSourceProjectiveBoundaryJetSynthesis n k x).2 := by
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource]
  simp only [physicalReturned,physicalOriginalReturned,radialReturnedSynthesis,
    LinearMap.coe_mk,AddHom.coe_mk,Complex.ofReal_one,one_pow,mul_one]

def physicalLeading (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n) : PhysicalCauchySpace :=
  physicalOriginalIncident 0 (leadingCoefficients n m x hm) 1

theorem physicalLeading_coe (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n) :
    (physicalLeading n m x hm : CanonicalCompletedNativeChiralCauchyCarrier)=leadingState n m x hm := by
  simp only [physicalLeading,physicalOriginalIncident,leadingState,radialIncidentSynthesis,
    LinearMap.coe_mk,AddHom.coe_mk,Complex.ofReal_one,one_pow,mul_one]

theorem physicalLeading_ne (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hxm : x ⟨m,hm⟩ ≠ 0) : physicalLeading n m x hm ≠ 0 := by
  intro hz
  have he := congrArg (fun v : PhysicalCauchySpace => (v:CanonicalCompletedNativeChiralCauchyCarrier)) hz
  exact leadingState_ne_zero n m x hm hxm (by simpa only [physicalLeading_coe,Submodule.coe_zero] using he)

theorem physical_scaled_incident_tendsto (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hx : ∀ a : Fin (2*n), m < a.val → x a=0) :
    Tendsto (fun k => observationScale k m • physicalIncident n k x) atTop
      (nhds (physicalLeading n m x hm)) := by
  apply tendsto_subtype_rng.mpr
  simpa only [Submodule.coe_smul,physicalIncident_coe,physicalLeading_coe] using
    scaled_incident_tendsto n m x hm hx

theorem physical_scaled_returned_tendsto (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hx : ∀ a : Fin (2*n), m < a.val → x a=0) :
    Tendsto (fun k => observationScale k m • physicalReturned n k x) atTop
      (nhds (-physicalLeading n m x hm)) := by
  apply tendsto_subtype_rng.mpr
  simpa only [Submodule.coe_smul,physicalReturned_coe,Submodule.coe_neg,physicalLeading_coe] using
    scaled_returned_tendsto n m x hm hx

/-- Same physical source, arbitrary independent boundary inputs. -/
theorem physical_source_defect_pairing (R n k l : ℕ)
    (x : Fin (2*n) → ℂ) {p : ℕ} (y : Fin (2*p) → ℂ) :
    inner ℂ (physicalIncident n k x) (physicalIncident p l y)-
      inner ℂ (physicalReturned n k x) (physicalReturned p l y)=
      inner ℂ (conservativeHead R (physicalIncident n k x)) (conservativeHead R (physicalIncident p l y))-
      inner ℂ (conservativeReturn R (physicalIncident n k x))
        (transportDefect R (physicalIncident p l y) (physicalReturned p l y))-
      inner ℂ (transportDefect R (physicalIncident n k x) (physicalReturned n k x))
        (conservativeReturn R (physicalIncident p l y))-
      inner ℂ (transportDefect R (physicalIncident n k x) (physicalReturned n k x))
        (transportDefect R (physicalIncident p l y) (physicalReturned p l y)) :=
  polarized_defect_ledger R _ _ _ _

theorem physical_signed_energy_tendsto (n : ℕ) (x : Fin (2*n) → ℂ) :
    Tendsto (fun k => 2*(‖physicalIncident n k x‖^2-‖physicalReturned n k x‖^2)) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x)) := by
  simpa only [← physicalIncident_coe,← physicalReturned_coe,Submodule.norm_coe] using
    nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto n x

end
end CarryConservativeIntertwiner
