import EffectiveOddPair
import EffectiveSixBudget

namespace CarrySummableRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryMaterialVariation
open CarryBoundaryReconstruction NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sixOrders : Finset ℕ := {0,1,2}
def sixCoefficients (u v : ℝ) (r : ℕ) : ℝ := if r=0 then v else if r=1 then u else 1

/-- Literally the jets 1, 3, 5 used by the six-address certificate. -/
theorem six_input_eq_finite_odd (u v : ℝ) (k : ℕ) :
    finiteOddJetSource sixOrders (sixCoefficients u v) k=sixInput u v k := by
  simp [finiteOddJetSource,sixOrders,sixCoefficients,sixInput]
  module

/-- The six-source norm balance equals twice the actual signed energy.
The factor is dictated by the existing chiral form, not normalized away. -/
theorem six_physical_eq_twice_finite_energy (k : ℕ) :
    sixPhysical k = 2*fullEnergy k (finiteOddJetSource sixOrders (sixCoefficients sixU sixV) k) := by
  rw [six_input_eq_finite_odd]
  exact (CarryTailReturn.signed_diagonal_norm _).symm

theorem six_original_absolute_tail_regression (K : ℕ) (hK : budgetIndex ≤ K) :
    Summable (fun j => |2*fullEnergy (K+j) (finiteOddJetSource sixOrders (sixCoefficients sixU sixV) (K+j))-
      2*fullEnergy (K+j+1) (finiteOddJetSource sixOrders (sixCoefficients sixU sixV) (K+j+1))|) ∧
    (∑' j, |2*fullEnergy (K+j) (finiteOddJetSource sixOrders (sixCoefficients sixU sixV) (K+j))-
      2*fullEnergy (K+j+1) (finiteOddJetSource sixOrders (sixCoefficients sixU sixV) (K+j+1))|) ≤
      (radialFourSourceStep K)^2 := by
  simpa only [← six_physical_eq_twice_finite_energy] using
    ⟨(six_effective_absolute_tail K hK).2.1, (six_effective_absolute_tail K hK).2.2⟩

/-- The unchanged sharp six-address reference bound at the original anchor. -/
theorem six_anchor_tail_regression :
    (∑' j, |2*fullEnergy (budgetIndex+j) (finiteOddJetSource sixOrders (sixCoefficients sixU sixV) (budgetIndex+j))-
      2*fullEnergy (budgetIndex+j+1) (finiteOddJetSource sixOrders (sixCoefficients sixU sixV) (budgetIndex+j+1))|) ≤
      1/(10:ℝ)^40 := by
  have hh := (six_original_absolute_tail_regression budgetIndex (le_refl _)).2
  rw [step_at_budget_index] at hh
  convert hh using 1
  norm_num [budgetStep]

end
end CarrySummableRadial
