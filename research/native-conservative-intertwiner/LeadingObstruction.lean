import PhysicalCoordinates

namespace CarryConservativeIntertwiner
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre ChiralReturn
open CarryCriticalRelative Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators lp ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Strong stability of the ORIGINAL shift rules out its nonzero fixed points. -/
theorem physical_shift_fixed_eq_zero (R : ℕ) (w : PhysicalCauchySpace)
    (hw : physicalCauchyShift (R+1) w=w) : w=0 := by
  have hall (j : ℕ) : physicalCauchyShift (j*(R+1)) w=w := by
    induction j with
    | zero => simp [physicalCauchyShift_zero]
    | succ j ih =>
      rw [Nat.succ_mul,physicalCauchyShift_add,ContinuousLinearMap.comp_apply,hw,ih]
  have hn : Tendsto (fun j : ℕ => j*(R+1)) atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp; nlinarith) tendsto_id
  have ht := (physicalCauchyShift_tendsto_zero w).comp hn
  simp only [Function.comp_def,hall] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht

def leadingTransportDefect (R : ℕ) (w : PhysicalCauchySpace) : PhysicalCauchySpace :=
  physicalCauchyShift (R+1) w-w

theorem leadingTransportDefect_ne (R : ℕ) (w : PhysicalCauchySpace) (hw : w≠0) :
    leadingTransportDefect R w≠0 := by
  intro hz
  exact hw (physical_shift_fixed_eq_zero R w (sub_eq_zero.mp hz))

/-- Exact nonzero leading defect of the conservative map on the complete source. -/
theorem scaled_transport_defect_tendsto (R n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m<2*n)
    (hx : ∀ a : Fin (2*n), m<a.val → x a=0) :
    Tendsto (fun k => observationScale k m • transportDefect R
      (physicalIncident n k x) (physicalReturned n k x)) atTop
      (nhds (leadingTransportDefect R (physicalLeading n m x hm))) := by
  have hi := physical_scaled_incident_tendsto n m x hm hx
  have hr := physical_scaled_returned_tendsto n m x hm hx
  have hc := (conservativeReturn R).continuous.continuousAt.tendsto.comp hi
  have ht := hr.sub hc
  convert ht using 1
  · funext k
    simp only [transportDefect,smul_sub,map_smul,Function.comp_def]
  · simp only [leadingTransportDefect,conservativeReturn,neg_apply]
    abel

/-- No exact transport even eventually; no canonical moment sign is used. -/
theorem conservative_return_not_eventually_source (R n m : ℕ) (x : Fin (2*n) → ℂ)
    (hm : m<2*n) (hx : ∀ a : Fin (2*n), m<a.val → x a=0)
    (hxm : x ⟨m,hm⟩ ≠ 0) :
    ∀ᶠ k : ℕ in atTop, physicalReturned n k x ≠ conservativeReturn R (physicalIncident n k x) := by
  have ht := (scaled_transport_defect_tendsto R n m x hm hx).eventually_ne
    (leadingTransportDefect_ne R _ (physicalLeading_ne n m x hm hxm))
  filter_upwards [ht] with k hk he
  apply hk
  rw [transportDefect,he,sub_self,smul_zero]

/-- The candidate's positive complement is cancelled by the full leading
transport error. This is an identity, not a source negativity statement. -/
theorem leading_conservative_cancellation (R : ℕ) (w : PhysicalCauchySpace) :
    ‖conservativeHead R w‖^2-
      2*(inner ℂ (conservativeReturn R w) (leadingTransportDefect R w)).re-
      ‖leadingTransportDefect R w‖^2=0 := by
  have h := energy_defect_ledger R w (-w)
  have he : transportDefect R w (-w)=leadingTransportDefect R w := by
    simp only [transportDefect,conservativeReturn,neg_apply,leadingTransportDefect]
    abel
  rw [he,norm_neg,sub_self] at h
  exact h.symm

end
end CarryConservativeIntertwiner
