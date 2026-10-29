import ReadoutResidual
import VariableTransport

namespace CarryFourLeg
open CarryCameraTail CarryMaterialTheta CarrySelfAdjointOperator CPFormal.Analytic.Cp
open GeometryOfNumbers.Analysis
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false

theorem one_block_value_legs (z w : ℂ) :
    let a := canonicalMixedBoundaryResidualLegs 1 tfvdHaarScale (fun _ => 1) z w
    (a.left (0,0), a.right (0,0), a.left (0,1), a.right (0,1)) =
      (positiveDirichletGradient w 0, positiveDirichletGradient w 1,
       positiveDirichletGradient w 1, positiveDirichletGradient w 2) := by
  rw [original_mixed_legs_addresses 1 tfvdHaarScale_ne_zero (fun _ => 1) (by simp)]
  rfl

theorem one_block_log_legs (z w : ℂ) :
    let a := canonicalMixedBoundaryResidualLegs 1 tfvdHaarScale (fun _ => 1) z w
    (a.jetLeft (0,0), a.jetRight (0,0), a.jetLeft (0,1), a.jetRight (0,1)) =
      (positiveLogDirichletGradient z 0, positiveLogDirichletGradient z 1,
       positiveLogDirichletGradient z 1, positiveLogDirichletGradient z 2) := by
  rw [original_mixed_legs_addresses 1 tfvdHaarScale_ne_zero (fun _ => 1) (by simp)]
  rfl

theorem one_block_right_residual (z w : ℂ) :
    (originalReadoutResiduals 1 z w).2.1 =
      conj (finiteBracketedDirichletChart 3 1 w) -
        (positiveDirichletValue w 3 - positiveDirichletValue w 1) := by
  have hv := (canonicalC3BracketTfvdCompletionState_transport_components 1 w).1
  change (canonicalBoundaryResidualData 1 tfvdHaarScale (fun _ => 1) w).valueReadout = _ at hv
  unfold originalReadoutResiduals mixedBoundaryRightResidual
  dsimp only
  rw [hv, original_mixed_legs_addresses 1 tfvdHaarScale_ne_zero (fun _ => 1) (by simp)]
  simp only [addressedGradientLegs, Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, mul_zero, zero_add, positiveDirichletGradient,
    positiveDirichletValue_eq_natDirichletTerm]
  ring

theorem nat_term_at_real (n : ℕ) (sigma : ℝ) :
    natDirichletTerm (sigma : ℂ) n = (((n : ℝ)^(-sigma) : ℝ) : ℂ) := by
  simpa only [natDirichletTerm, dirichletTerm, Int.cast_natCast,
    Complex.ofReal_neg, Complex.ofReal_natCast] using
    (Complex.ofReal_cpow (x := (n : ℝ)) (by positivity) (-sigma)).symm

theorem one_block_right_residual_at_center (z : ℂ) :
    (originalReadoutResiduals 1 z (1/2 : ℂ)).2.1 =
      ((1 + 2*((2 : ℝ)^(-(1 : ℝ)/2) - (3 : ℝ)^(-(1 : ℝ)/2)) : ℝ) : ℂ) := by
  rw [one_block_right_residual]
  unfold finiteBracketedDirichletChart
  rw [seedSum_three_dirichlet_eq_one]
  simp only [Finset.sum_range_one, realCpSaturatedBracket_three_eq_values,
    positiveDirichletValue_eq_natDirichletTerm]
  norm_num only
  have ht (n : ℕ) : natDirichletTerm (1/2 : ℂ) n =
      (((n : ℝ)^(-(1 : ℝ)/2) : ℝ) : ℂ) := by
    have h := nat_term_at_real n (1/2)
    have hs : ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) := by
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    have he : -(1/2 : ℝ) = -(1 : ℝ)/2 := by ring
    rw [hs, he] at h
    exact h
  simp only [ht, map_add, map_sub, map_mul, map_one, map_ofNat, Complex.conj_ofReal]
  push_cast
  ring

/-- The actual native right residual is already nonzero on the real
critical center. This tests explanations that retain only phase changes. -/
theorem one_block_right_residual_center_gt_one (z : ℂ) :
    1 < ((originalReadoutResiduals 1 z (1/2 : ℂ)).2.1).re := by
  rw [one_block_right_residual_at_center, Complex.ofReal_re]
  have h := Real.rpow_lt_rpow_of_neg (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) < 3) (by norm_num : -(1 : ℝ)/2 < 0)
  linarith

theorem one_block_right_residual_center_ne_zero (z : ℂ) :
    (originalReadoutResiduals 1 z (1/2 : ℂ)).2.1 ≠ 0 := by
  intro hz
  have h := one_block_right_residual_center_gt_one z
  rw [hz, Complex.zero_re] at h
  linarith

theorem zero_time_leg_phase (m k : ℕ) (epsilon : ℝ) :
    - (0 : ℝ)*(c2FiberLogDefect m epsilon (k+1) - c2FiberLogDefect m epsilon k) = 0 := by
  simp

/-- A copied middle gradient belongs to two adjacent C2 centers before
dilation. At the next fixed-radius layer their corresponding edges have
different starting addresses. Closing the same three-edge block is not an
automatic consequence of the point transport identity. -/
theorem dilated_middle_addresses_distinct (m : ℕ) :
    2*(3*m+2) ≠ 2*(3*m+3)-1 := by omega

end
end CarryFourLeg
