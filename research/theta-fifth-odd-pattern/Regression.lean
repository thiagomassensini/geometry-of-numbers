import TenSourceReturn
import AllOrderPattern
import ModeSchedule

namespace CarryThetaPattern
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCorrectedGreenPorts CarryIntegralCertificate
open GeometryOfNumbers.Analysis Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- Recover both literal weights already encountered, without modifying them. -/
theorem theta_weights_regression :
    sourceThetaIntegral 8 =
      1224*completedNativeThetaTailMoment 16-completedNativeThetaTailMoment 18 ∧
    sourceThetaIntegral 9 =
      1520*completedNativeThetaTailMoment 18-completedNativeThetaTailMoment 20 := by
  constructor <;> rw [sourceThetaIntegral_moments] <;> norm_num

theorem fifth_odd_pattern_regression :
    sourceThetaIntegral 9 < 4*(Nat.factorial 20:ℝ)*sourceCeiling 1 4 := by
  rw [sourceCeiling_fifthOdd,sourceThetaIntegral_moments]
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat]
  have hc := fifthOdd_margin_iff_thetaMoments.mp fifth_odd_criticalMargin
  norm_num at hc
  exact hc

/-- Central coefficient, both new diagonals, an old-new cross and the mixed
parity entry all belong to ONE ten-column physical realization. -/
theorem ten_block_calibration :
    ∃ v : Fin 10 → CanonicalCompletedNativeChiralCauchyCarrier,
      inner ℂ (fullSourceJet v 0) (fullSourceJet v 0) = (h 0:ℂ) ∧
      inner ℂ (fullSourceJet v 8) (fullSourceJet v 8) = (h 8:ℂ) ∧
      inner ℂ (fullSourceJet v 9) (fullSourceJet v 9) = (h 9:ℂ) ∧
      inner ℂ (fullSourceJet v 7) (fullSourceJet v 9) = (h 8:ℂ) ∧
      inner ℂ (fullSourceJet v 8) (fullSourceJet v 9) = 0 := by
  obtain ⟨v,_,hv⟩ := canonical_ten_physical_realization
  refine ⟨v,?_,?_,?_,?_,?_⟩
  · rw [hv]
    exact polarizedGreenMomentCoefficient_even_even _ 0 0
  · rw [hv]
    exact polarizedGreenMomentCoefficient_even_even _ 4 4
  · rw [hv]
    exact polarizedGreenMomentCoefficient_odd_odd _ 4 4
  · rw [hv]
    exact polarizedGreenMomentCoefficient_odd_odd _ 3 4
  · rw [hv]
    exact polarizedGreenMomentCoefficient_even_odd _ 4 4

theorem eight_to_ten_residual_crossings :
    ∀ᶠ k : ℕ in atTop, ∀ a b : Fin 8,
      inner ℂ (residualEnergyJet k 9 (Fin.castLE (by decide : 8 ≤ 10) a))
        (residualEnergyJet k 9 (Fin.castLE (by decide : 8 ≤ 10) b)) =
      inner ℂ (residualEnergyJet k 7 a) (residualEnergyJet k 7 b) := by
  filter_upwards [ten_return_eventually_contractive] with k hk
  intro a b
  exact CarryReturnCompatibility.residualJets_prefix_pairing k (by decide : 7 ≤ 9) hk a b


/-- The first even step beyond the certified block, left as an exact gate. -/
theorem next_even_margin_gate :
    HasCriticalMargin 0 5 ↔
      -4*(Nat.factorial 22:ℝ)*sourceCeiling 0 5 < sourceThetaIntegral 10 :=
  evenMargin_iff_lower_theta 5 even_source_five_posDef

theorem next_even_theta_weight : sourceThetaIntegral 10 =
    1848*completedNativeThetaTailMoment 20-completedNativeThetaTailMoment 22 := by
  rw [sourceThetaIntegral_moments]
  norm_num

/-- This is an arbitrary-order tail-accuracy schedule, with no positivity
claim for an unproved source pivot. -/
theorem reciprocal_tolerance_mode_schedule :
    ∃ K : ℕ → ℕ, StrictMono K ∧ ∀ n,
      (∫ u in Set.Ioi 0, weightedOmittedPrefix (K n) (2*n) u) < 1/((n:ℝ)+1) :=
  exists_monotone_mode_schedule (fun n => 1/((n:ℝ)+1)) (fun n => by positivity)

theorem common_prefix_mode_schedule_regression :
    ∃ K : ℕ → ℕ, StrictMono K ∧ ∀ n j, j ≤ n →
      (∫ u in Set.Ioi 0, weightedOmittedPrefix (K n) (2*j) u) < 1/((j:ℝ)+1) :=
  exists_monotone_common_mode_schedule (fun j => 1/((j:ℝ)+1)) (fun j => by positivity)

end
end CarryThetaPattern
