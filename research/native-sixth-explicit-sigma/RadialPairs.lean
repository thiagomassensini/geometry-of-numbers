import TwelveTrial
import TenDirectAnchor

namespace CarrySixthExplicit
open CarrySelfAdjointOperator CarryDirectAnchor CarrySixthRelative CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial CarryIntegralCertificate NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 72000000
set_option maxRecDepth 65536

/-- The exact budget already includes both orientations of each pair. -/
theorem pair_constant_symmetric (r s : ℕ) : pairConstant r s = pairConstant s r := by
  have hh : spatialCorrection (2*r+1) (2*s+1) = spatialCorrection (2*s+1) (2*r+1) := by
    unfold spatialCorrection
    ring
  unfold pairConstant
  rw [hh,show s+r=r+s by omega]
  ring

theorem sixth_pair_constants_bounded (s : ℕ) (hs : s<6) :
    pairConstant 5 s ≤ (10:ℝ)^12 := by
  interval_cases s <;>
    norm_num [pairConstant,oddFilterBudget,oddFilterCoefficient,nativeOddBeta,
      spatialCorrection,CarrySpatialCorrection.slope,CarrySpatialCorrection.curvature,
      Finset.sum_range_succ,Finset.sum_range_zero,Complex.norm_real,Real.norm_eq_abs,Nat.choose]

/-- A rational upper bound for every ORIGINAL ordered pair of six odd jets. -/
theorem twelve_pair_constants_bounded (r s : ℕ) (hr : r ∈ twelveOrders) (hs : s ∈ twelveOrders) :
    pairConstant r s ≤ (10:ℝ)^12 := by
  have hr' : r<6 := Finset.mem_range.mp hr
  have hs' : s<6 := Finset.mem_range.mp hs
  by_cases hr5 : r<5
  · by_cases hs5 : s<5
    · have h := ten_pair_constants_bounded r s (Finset.mem_range.mpr hr5) (Finset.mem_range.mpr hs5)
      have hm : (10:ℝ)^10 ≤ (10:ℝ)^12 := by norm_num
      exact h.trans hm
    · have he : s=5 := by omega
      subst s
      rw [pair_constant_symmetric]
      exact sixth_pair_constants_bounded r hr'
  · have he : r=5 := by omega
    subst r
    exact sixth_pair_constants_bounded s hs'


end
end CarrySixthExplicit
