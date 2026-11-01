import OddTrialPositivity
import AllOrderPattern

namespace CarrySeventhOddCanonical
open CarrySelfAdjointOperator CarryCriticalSource CarryThetaPattern CarrySixthOdd
open scoped Matrix
noncomputable section
set_option autoImplicit false

/-- Exact specialization of the odd seventh pivot in native coordinates. -/
theorem k7_pivot_formula :
    sourceMomentSchur h 1 6 =
      h 13 - sourceMomentCoupling h 1 6 ⬝ᵥ
        ((sourceMomentMatrix h 1 6)⁻¹ *ᵥ sourceMomentCoupling h 1 6) := by
  rfl

/-- Existing interface: K7 pivot sign is equivalent to odd critical margin at n=6. -/
theorem k7_pos_iff_margin :
    0 < sourceMomentSchur h 1 6 ↔ HasCriticalMargin 1 6 := by
  exact (criticalMargin_iff_pivot 1 6 odd_source_six_posDef).symm

/-- Theta gate form of the same K7 sign condition (no new hypothesis). -/
theorem k7_pos_iff_theta_gate :
    0 < sourceMomentSchur h 1 6 ↔
      sourceThetaIntegral 13 < 4 * (Nat.factorial 28 : ℝ) * sourceCeiling 1 6 := by
  calc
    0 < sourceMomentSchur h 1 6 ↔ HasCriticalMargin 1 6 := k7_pos_iff_margin
    _ ↔ sourceThetaIntegral (2 * 6 + 1) <
        4 * (Nat.factorial (4 * 6 + 4) : ℝ) * sourceCeiling 1 6 :=
      oddMargin_iff_upper_theta 6 odd_source_six_posDef
    _ ↔ sourceThetaIntegral 13 < 4 * (Nat.factorial 28 : ℝ) * sourceCeiling 1 6 := by
      norm_num

/-- Target equivalence at matrix level, reduced to the K7 pivot sign. -/
theorem k7_matrix_posDef_iff_pivot :
    (sourceMomentMatrix h 1 7).PosDef ↔ 0 < sourceMomentSchur h 1 6 := by
  exact sourceMomentMatrix_succ_posDef_iff h 1 6 odd_source_six_posDef

theorem sourceThetaIntegral13_eq_theta26_theta28 :
    sourceThetaIntegral 13 =
      3024 * completedNativeThetaTailMoment 26 - completedNativeThetaTailMoment 28 := by
  rw [sourceThetaIntegral_moments]
  norm_num

theorem k7_pos_iff_theta26_theta28_gate :
    0 < sourceMomentSchur h 1 6 ↔
      3024 * completedNativeThetaTailMoment 26 - completedNativeThetaTailMoment 28 <
        4 * (Nat.factorial 28 : ℝ) * sourceCeiling 1 6 := by
  rw [k7_pos_iff_theta_gate, sourceThetaIntegral13_eq_theta26_theta28]

theorem k7_matrix_posDef_iff_theta26_theta28_gate :
    (sourceMomentMatrix h 1 7).PosDef ↔
      3024 * completedNativeThetaTailMoment 26 - completedNativeThetaTailMoment 28 <
        4 * (Nat.factorial 28 : ℝ) * sourceCeiling 1 6 := by
  rw [k7_matrix_posDef_iff_pivot, k7_pos_iff_theta26_theta28_gate]

end
end CarrySeventhOddCanonical
