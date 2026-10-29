import EightHead

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial CarryIntegralCertificate NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

theorem eight_pair_constants_bounded (r s : ℕ) (hr : r ∈ eightOrders) (hs : s ∈ eightOrders) :
    pairConstant r s ≤ (10:ℝ)^9 := by
  have hr' : r<4 := Finset.mem_range.mp hr
  have hs' : s<4 := Finset.mem_range.mp hs
  interval_cases r <;> interval_cases s <;>
    norm_num [pairConstant,oddFilterBudget,oddFilterCoefficient,nativeOddBeta,
      spatialCorrection,CarrySpatialCorrection.slope,CarrySpatialCorrection.curvature,
      Finset.sum_range_succ,Finset.sum_range_zero,Complex.norm_real,Real.norm_eq_abs,Nat.choose]

theorem eight_coefficient_bounded (r : ℕ) (hr : r ∈ eightOrders) :
    |eightCoefficients r| ≤ 1 := by
  have hr' : r<4 := Finset.mem_range.mp hr
  interval_cases r
  · have h := critical0_box_mem
    norm_num [criticalBox0,Box.Mem,intervalScale] at h
    simp [eightCoefficients]
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  · have h := critical1_box_mem
    norm_num [criticalBox1,Box.Mem,intervalScale] at h
    simp [eightCoefficients]
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  · have h := critical2_box_mem
    norm_num [criticalBox2,Box.Mem,intervalScale] at h
    simp [eightCoefficients]
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  · norm_num [eightCoefficients]

theorem eight_family_constant_bounded : familyConstant eightOrders eightCoefficients ≤ 16*(10:ℝ)^9 := by
  unfold familyConstant
  calc
    _ ≤ ∑ r ∈ eightOrders, ∑ s ∈ eightOrders, (10:ℝ)^9 := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      have hc : |eightCoefficients r*eightCoefficients s| ≤ 1 := by
        rw [abs_mul]
        have hm := mul_le_mul_of_nonneg_right (eight_coefficient_bounded r hr) (abs_nonneg (eightCoefficients s))
        nlinarith [eight_coefficient_bounded s hs]
      calc
        _ ≤ 1*pairConstant r s := mul_le_mul_of_nonneg_right hc (pair_constant_nonneg r s)
        _ ≤ (10:ℝ)^9 := by simpa using eight_pair_constants_bounded r s hr hs
    _ = _ := by norm_num [eightOrders,Finset.sum_range_succ,Finset.sum_range_zero]

/-- The prior all-order estimate controls this same complete source relative
to the explicit interval head. -/
theorem eight_anchor_error :
    |fullEnergy budgetIndex (finiteOddJetSource eightOrders eightCoefficients budgetIndex)-
      oddCanonicalForm eightOrders eightCoefficients| ≤
      familyConstant eightOrders eightCoefficients*(radialFourSourceStep budgetIndex)^2 := by
  apply boundary_error_of_increment_budget
    (fun k => fullEnergy k (finiteOddJetSource eightOrders eightCoefficients k))
    (oddCanonicalForm eightOrders eightCoefficients) (familyConstant eightOrders eightCoefficients)
    (family_energy_tendsto eightOrders eightCoefficients) (family_constant_nonneg eightOrders eightCoefficients) budgetIndex
  intro j
  apply family_increment_budget
  have hcut : oddGridCutoff eightOrders = 32 := by decide +kernel
  rw [hcut]
  unfold budgetIndex
  omega

theorem eight_anchor_beats_general_tail :
    familyConstant eightOrders eightCoefficients*(radialFourSourceStep budgetIndex)^2 <
      fullEnergy budgetIndex (finiteOddJetSource eightOrders eightCoefficients budgetIndex) := by
  have ha := eight_anchor_error
  have hh := eight_head_strict_lower
  have hb := eight_family_constant_bounded
  have hstep : (radialFourSourceStep budgetIndex)^2=1/(10:ℝ)^40 := by
    rw [step_at_budget_index]
    norm_num [budgetStep]
  rw [hstep] at ha ⊢
  have hc := mul_le_mul_of_nonneg_right hb (show (0:ℝ) ≤ 1/(10:ℝ)^40 by positivity)
  have hn : 2*(16*(10:ℝ)^9)*(1/(10:ℝ)^40)<1/(10:ℝ)^23 := by norm_num
  have hneg := (abs_le.mp ha).1
  linarith

end
end CarryCriticalRadialMargin
