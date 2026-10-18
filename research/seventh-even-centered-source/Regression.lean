import EvenSeventhCertificate
import OrderedKernelPositivity
import RelativeResidual

namespace CarrySeventhEven
open CarrySelfAdjointOperator CarryCriticalSource CarryThetaPattern
open CarrySelfAdjointOperator.ChiralReturn MeasureTheory Filter
open scoped Topology InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Original raw Hankel ordering, not a centered Green pairing. -/
theorem seventh_ordered_even_pivot_pos :
    0 < GeometryOfNumbers.Analysis.carryPairingPivot (fun i j => h (i+j)) 6 := by
  apply CarryOrderedKernel.ordered_pivot_pos_of_posDef (fun i j => h (i+j))
    (fun i j => by rw [Nat.add_comm i j]) 6
  exact even_source_seven_posDef

theorem seventh_even_literal_theta_gate :
    -4*(Nat.factorial 26:ℝ)*sourceCeiling 0 6 <
      2600*completedNativeThetaTailMoment 24-completedNativeThetaTailMoment 26 := by
  have hg := seventh_even_theta_integral_certificate
  rw [sourceThetaIntegral_moments] at hg
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hg ⊢
  exact hg

theorem seventh_even_integral_gate :
    -4*(Nat.factorial 26:ℝ)*sourceCeiling 0 6 <
      ∫ u in Set.Ioi (0:ℝ), (2600*u^24-u^26)*XiThetaCosine.thetaTail u := by
  have hg := seventh_even_theta_integral_certificate
  norm_num only [sourceThetaIntegral,Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hg ⊢
  exact hg

theorem seventh_even_balance_limit :
    Tendsto (criticalBalance 0 6) atTop (𝓝 (2*sourceMomentSchur h 0 6)) :=
  criticalBalance_tendsto 0 6 CarrySixthEven.even_source_six_posDef

theorem seventh_even_eventually_above_pivot :
    ∀ᶠ k : ℕ in atTop, sourceMomentSchur h 0 6 < criticalBalance 0 6 k :=
  (tendsto_order.mp seventh_even_balance_limit).1 _ (by
    have hp := seventh_even_pivot_pos
    change sourceMomentSchur h 0 6 < 2*sourceMomentSchur h 0 6
    linarith)

/-- Both signed Jordan channels are retained in the critical direction.
This does not assert contraction on the entire fourteen-source face. -/
theorem seventh_even_jordan_margin : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop,
    ‖radialReturnJordanNegativePort k 14 (criticalIncident 0 6 k)‖^2+ε ≤
      ‖radialReturnJordanPositivePort k 14 (criticalIncident 0 6 k)‖^2 :=
  (criticalMargin_iff_jordanGap 0 6).mp seventh_even_criticalMargin

theorem seventh_even_sourceRemainder_pos : 0 < nativeSourceSchurRemainder 0 6 :=
  (criticalMargin_iff_sourceRemainder 0 6 CarrySixthEven.even_source_six_posDef).mp
    seventh_even_criticalMargin

end
end CarrySeventhEven
