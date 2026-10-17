import EighthPhysical
import LimitTower

namespace CarryReturnCompatibility
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open GeometryOfNumbers.Analysis CarryCorrectedGreenPorts
open CarryMaterialMixedSchurComparison
open Filter
open scoped InnerProductSpace Topology
noncomputable section
set_option autoImplicit false

/-- Seven old columns are INCLUDED, with all their crossings, rather than
being solved anew. The new eighth source also has its canonical calibration. -/
theorem eighth_block_calibration :
    ∃ v : Fin 8 → CanonicalCompletedNativeChiralCauchyCarrier,
      inner ℂ (fullSourceJet v 0) (fullSourceJet v 0) =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) ∧
      inner ℂ (fullSourceJet v 1) (fullSourceJet v 1) =
        (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) ∧
      inner ℂ (fullSourceJet v 7) (fullSourceJet v 7) =
        (canonicalCompletedNativeLogDerivativeMoment 7 : ℂ) ∧
      inner ℂ (fullSourceJet v 5) (fullSourceJet v 7) =
        (canonicalCompletedNativeLogDerivativeMoment 6 : ℂ) := by
  obtain ⟨v,_,hv⟩ := canonical_eight_physical_realization
  refine ⟨v,?_,?_,?_,?_⟩
  · rw [hv]
    exact polarizedGreenMomentCoefficient_even_even _ 0 0
  · rw [hv]
    exact polarizedGreenMomentCoefficient_odd_odd _ 0 0
  · rw [hv]
    exact polarizedGreenMomentCoefficient_odd_odd _ 3 3
  · rw [hv]
    exact polarizedGreenMomentCoefficient_odd_odd _ 2 3

/-- Independent old-new source directions are kept at finite k. -/
theorem seven_to_eight_residual_crossings :
    ∀ᶠ k : ℕ in atTop, ∀ a b : Fin 7,
      inner ℂ (residualEnergyJet k 7 (Fin.castLE (by decide : 7 ≤ 8) a))
        (residualEnergyJet k 7 (Fin.castLE (by decide : 7 ≤ 8) b)) =
          inner ℂ (residualEnergyJet k 6 a) (residualEnergyJet k 6 b) := by
  filter_upwards [eighthReturn_eventually_contractive] with k hk
  intro a b
  exact residualJets_prefix_pairing k (by decide : 6 ≤ 7) hk a b

end
end CarryReturnCompatibility
