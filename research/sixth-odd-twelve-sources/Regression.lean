import OddOrderedCertificate
import OddPhysicalPolarization
import ResidualObstructions

namespace CarrySixthOdd
open CarryThetaPattern CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCorrectedGreenPorts MeasureTheory Filter
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem sixth_odd_literal_theta_gate :
    2208*completedNativeThetaTailMoment 22-completedNativeThetaTailMoment 24 <
      4*(Nat.factorial 24:ℝ)*sourceCeiling 1 5 := by
  have hg := sixth_odd_theta_integral_certificate
  rw [sourceThetaIntegral_moments] at hg
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hg ⊢
  exact hg

theorem sixth_odd_integral_gate :
    (∫ u in Set.Ioi (0:ℝ), (2208*u^22-u^24)*XiThetaCosine.thetaTail u) <
      4*(Nat.factorial 24:ℝ)*sourceCeiling 1 5 := by
  have hg := sixth_odd_theta_integral_certificate
  norm_num only [sourceThetaIntegral,Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hg ⊢
  exact hg

/-- Two 6x6 sectors. This is not a 12x12 real Hankel assertion. -/
theorem both_six_source_sectors_posDef :
    (sourceMomentMatrix h 0 6).PosDef ∧ (sourceMomentMatrix h 1 6).PosDef :=
  ⟨CarrySixthEven.even_source_six_posDef,odd_source_six_posDef⟩

theorem sixth_odd_eventually_above_pivot :
    ∀ᶠ k : ℕ in atTop, sourceMomentSchur h 1 5 < criticalBalance 1 5 k :=
  (tendsto_order.mp (criticalBalance_tendsto 1 5 odd_source_five_posDef)).1 _ (by
    have hp := sixth_odd_pivot_pos
    change sourceMomentSchur h 1 5 < 2*sourceMomentSchur h 1 5
    linarith)

/-- The center, BOTH new diagonals, both old/new same-sector crossings and
the mixed crossing belong to ONE original physical realization. -/
theorem twelve_block_calibration :
    ∃ v : Fin 12 → CanonicalCompletedNativeChiralCauchyCarrier,
      inner ℂ (fullSourceJet v 0) (fullSourceJet v 0) = (h 0:ℂ) ∧
      inner ℂ (fullSourceJet v 10) (fullSourceJet v 10) = (h 10:ℂ) ∧
      inner ℂ (fullSourceJet v 11) (fullSourceJet v 11) = (h 11:ℂ) ∧
      inner ℂ (fullSourceJet v 8) (fullSourceJet v 10) = (h 9:ℂ) ∧
      inner ℂ (fullSourceJet v 9) (fullSourceJet v 11) = (h 10:ℂ) ∧
      inner ℂ (fullSourceJet v 10) (fullSourceJet v 11) = 0 := by
  obtain ⟨v,_,hv⟩ := canonical_twelve_physical_realization
  refine ⟨v,?_,?_,?_,?_,?_,?_⟩
  · rw [hv]
    exact polarizedGreenMomentCoefficient_even_even _ 0 0
  · rw [hv]
    exact polarizedGreenMomentCoefficient_even_even _ 5 5
  · rw [hv]
    exact polarizedGreenMomentCoefficient_odd_odd _ 5 5
  · rw [hv]
    exact polarizedGreenMomentCoefficient_even_even _ 4 5
  · rw [hv]
    exact polarizedGreenMomentCoefficient_odd_odd _ 4 5
  · rw [hv]
    exact polarizedGreenMomentCoefficient_even_odd _ 5 5

end
end CarrySixthOdd
