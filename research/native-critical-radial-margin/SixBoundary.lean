import SixMargin

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- An actual positive source anchor dominates the proven all-cross tail;
this is a sufficient condition, not an assumption about a pivot. -/
theorem finite_odd_boundary_positive_of_anchor (S : Finset ℕ) (c : ℕ → ℝ) (K : ℕ)
    (hK : oddGridCutoff S ≤ K)
    (ha : familyConstant S c*(radialFourSourceStep K)^2 <
      fullEnergy K (finiteOddJetSource S c K)) : 0 < oddCanonicalForm S c := by
  apply positive_boundary_of_increment_budget
    (fun k => fullEnergy k (finiteOddJetSource S c k)) (oddCanonicalForm S c)
    (familyConstant S c) (family_energy_tendsto S c) (family_constant_nonneg S c) K
  · intro j
    exact family_increment_budget S c (K+j) (by omega)
  · exact ha

theorem six_boundary_positive_via_general_tail :
    0 < oddCanonicalForm sixOrders (sixCoefficients sixU sixV) := by
  apply finite_odd_boundary_positive_of_anchor sixOrders (sixCoefficients sixU sixV) budgetIndex
  · have hk : oddGridCutoff sixOrders = 24 := by
      norm_num [oddGridCutoff,oddGridSize,sixOrders,Finset.sup_insert,Finset.sup_empty]
    rw [hk]
    norm_num [budgetIndex]
  · exact six_anchor_beats_general_tail

/-- Normalizations checked: the six-channel norm balance is twice this
canonical odd form. -/
theorem six_canonical_form_eq_half_limit :
    oddCanonicalForm sixOrders (sixCoefficients sixU sixV)=sixLimit sixU sixV/2 := by
  unfold oddCanonicalForm sixLimit
  simp [sixOrders,sixCoefficients,Finset.sum_insert,Finset.sum_singleton]
  ring

/-- The same algebraic residual from PR #41 is positive, derived from the
finite physical source and the absolute tail, not assumed. -/
theorem six_residual_positive_via_general_tail :
    0 < canonicalCompletedNativeLogDerivativeMoment 5+
      sixU*canonicalCompletedNativeLogDerivativeMoment 4+
      sixV*canonicalCompletedNativeLogDerivativeMoment 3 := by
  have hp := six_boundary_positive_via_general_tail
  rw [six_canonical_form_eq_half_limit,six_critical_limit_residual] at hp
  linarith

end
end CarryCriticalRadialMargin
