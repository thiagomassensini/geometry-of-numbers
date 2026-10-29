import WholeSourceLimit
import CriticalSource

namespace CarryCriticalRelative
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn CarryCriticalSource
open Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000

def criticalOrder (s : Fin 2) (n : ℕ) : ℕ := 2*n+s.val

theorem criticalOrder_lt (s : Fin 2) (n : ℕ) : criticalOrder s n < 2*(n+1) := by
  have hs := s.isLt
  unfold criticalOrder
  omega

theorem criticalCoordinates_above (s : Fin 2) (n : ℕ) (a : Fin (2*(n+1)))
    (ha : criticalOrder s n < a.val) : criticalCoordinates s n a = 0 := by
  fin_cases s
  · have ham : a.val % 2 ≠ 0 := by
      have hlt := a.isLt
      simp only [criticalOrder] at ha
      omega
    change nativeSourceBoundaryFromParity (n+1)
      (fun i => (criticalCoefficients 0 n i : ℂ)) 0 a = 0
    simp [nativeSourceBoundaryFromParity, ham]
  · have hlt := a.isLt
    simp only [criticalOrder] at ha
    omega

theorem parityCoordinates_top (s : Fin 2) (n : ℕ) (v : Fin (n+1) → ℝ) :
    parityCoordinates s v ⟨criticalOrder s n, criticalOrder_lt s n⟩ =
      (((-1:ℝ)^n : ℝ) : ℂ) * (v (Fin.last n) : ℂ) := by
  fin_cases s
  · have hd : (2*n+0)/2 = n := by omega
    have hm : (2*n+0)%2 = 0 := by omega
    simp only [parityCoordinates, if_true,
      nativeSourceBoundaryFromParity, criticalOrder, hd, hm]
    rfl
  · have hd : (2*n+1)/2 = n := by omega
    have hm : (2*n+1)%2 ≠ 0 := by omega
    simp only [parityCoordinates, one_ne_zero, if_false,
      nativeSourceBoundaryFromParity, criticalOrder, hd, hm]
    rfl

theorem criticalCoordinates_top_phase (s : Fin 2) (n : ℕ) :
    nativeSourceJetOrderPhase (criticalOrder s n) *
      criticalCoordinates s n ⟨criticalOrder s n, criticalOrder_lt s n⟩ = 1 := by
  rw [criticalCoordinates, parityCoordinates_top]
  have hc : criticalCoefficients s n (Fin.last n) = 1 := Fin.snoc_last _ _
  rw [hc, Complex.ofReal_one, mul_one]
  have hd : (2*n+s.val)/2 = n := by have hs := s.isLt; omega
  simp only [nativeSourceJetOrderPhase, criticalOrder, hd]
  norm_cast
  rw [← pow_add]
  exact Even.neg_one_pow ⟨n,by omega⟩

theorem criticalCoordinates_top_ne (s : Fin 2) (n : ℕ) :
    criticalCoordinates s n ⟨criticalOrder s n, criticalOrder_lt s n⟩ ≠ 0 := by
  intro hz
  have h := criticalCoordinates_top_phase s n
  rw [hz, mul_zero] at h
  norm_num at h

/-- Universal leading source vector: no old moment coupling enters its
definition. Those couplings are retained in the exact, subleading source. -/
def criticalLeadingState (s : Fin 2) (n : ℕ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis 0 (2*(n+1)) (fun r =>
    amp 0 * ((criticalOrder s n).factorial : ℂ)⁻¹ *
      completedGreenForwardWeight (criticalOrder s n) r)

theorem critical_leading_eq (s : Fin 2) (n : ℕ) :
    leadingState (n+1) (criticalOrder s n) (criticalCoordinates s n) (criticalOrder_lt s n) =
      criticalLeadingState s n := by
  unfold leadingState criticalLeadingState
  congr 1
  funext r
  unfold leadingCoefficients
  have h := criticalCoordinates_top_phase s n
  linear_combination (norm := ring_nf) h *
    (amp 0 * ((criticalOrder s n).factorial : ℂ)⁻¹ *
      completedGreenForwardWeight (criticalOrder s n) r)

theorem criticalLeadingState_ne (s : Fin 2) (n : ℕ) : criticalLeadingState s n ≠ 0 := by
  rw [← critical_leading_eq]
  exact leadingState_ne_zero _ _ _ _ (criticalCoordinates_top_ne s n)

/-- Equality of BOTH original vectors, before reading energies. -/
theorem critical_pair_exact (s : Fin 2) (n k : ℕ) :
    nativeSourceProjectiveBoundaryJetSynthesis (n+1) k (criticalCoordinates s n) =
      ((criticalIncident s n k : CanonicalCompletedNativeChiralCauchyCarrier), criticalReturned s n k) := by
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource]
  simp only [criticalReturned, criticalIncident, criticalInput,
    radialReturnTransfer_exact, radialIncidentVector_coe]

theorem critical_whole_source_tendsto (s : Fin 2) (n : ℕ) :
    Tendsto (fun k => observationScale k (criticalOrder s n) •
      ((criticalIncident s n k : CanonicalCompletedNativeChiralCauchyCarrier), criticalReturned s n k))
      atTop (nhds (criticalLeadingState s n, -criticalLeadingState s n)) := by
  have ht := scaled_whole_source_tendsto (n+1) (criticalOrder s n)
    (criticalCoordinates s n) (criticalOrder_lt s n) (criticalCoordinates_above s n)
  simpa only [critical_pair_exact, critical_leading_eq] using ht

theorem critical_energy_ratio_tendsto_one (s : Fin 2) (n : ℕ) :
    Tendsto (fun k => ‖criticalReturned s n k‖^2 / ‖criticalIncident s n k‖^2)
      atTop (nhds 1) := by
  have ht := returned_incident_energy_ratio_tendsto_one (n+1) (criticalOrder s n)
    (criticalCoordinates s n) (criticalOrder_lt s n)
    (criticalCoordinates_above s n) (criticalCoordinates_top_ne s n)
  simpa only [critical_pair_exact, Submodule.norm_coe] using ht

theorem critical_no_fixed_relative_contraction (s : Fin 2) (n : ℕ)
    (rho : ℝ) (hrho : rho < 1) :
    ¬ (∀ᶠ k : ℕ in atTop, ‖criticalReturned s n k‖^2 ≤ rho * ‖criticalIncident s n k‖^2) := by
  have h := no_fixed_relative_contraction (n+1) (criticalOrder s n)
    (criticalCoordinates s n) (criticalOrder_lt s n)
    (criticalCoordinates_above s n) (criticalCoordinates_top_ne s n) rho hrho
  simpa only [critical_pair_exact, Submodule.norm_coe] using h

end
end CarryCriticalRelative
