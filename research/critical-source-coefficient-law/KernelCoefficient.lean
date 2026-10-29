import StencilCoefficients
import OddCritical

namespace CarrySourceLaw
open CarrySelfAdjointOperator CarryCriticalMixed
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

/-- Original signed binomial weight, in its proved real coordinate. -/
theorem original_weight_re (p r : ℕ) :
    (completedGreenForwardWeight p r).re = (-1:ℝ)^(p-r)*(p.choose r:ℝ) := by
  have he : ((-1:ℂ)^(p-r)).re = (-1:ℝ)^(p-r) := by norm_cast
  simp [completedGreenForwardWeight, he]

/-- Factorization of the COMPLETE ordered crosses of the original shifted
stencils. Lower-degree cancellations use only the old difference identities. -/
theorem greenContraction_eq_shifted_weights (p q d : ℕ) :
    greenContraction p q d =
      ∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
        (completedGreenForwardWeight p r).re*(completedGreenForwardWeight q s).re *
          (∑ a ∈ Finset.range (d+1), (-1:ℝ)^a*(r+1:ℝ)^a*(s+1:ℝ)^(d-a)) := by
  simp only [original_weight_re]
  unfold greenContraction stencilPower
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The odd source power divided by the OLD Cauchy denominator has exactly
this alternating homogeneous kernel; no diagonal crosses are omitted. -/
theorem odd_power_cauchy_quotient (r s j : ℕ) :
    ((r+1:ℝ)^(2*j+1)+(s+1:ℝ)^(2*j+1))/(r+s+2:ℝ) =
      ∑ a ∈ Finset.range (2*j+1), (-1:ℝ)^a*(r+1:ℝ)^a*(s+1:ℝ)^(2*j-a) := by
  have he := Commute.mul_neg_geom_sum₂ (Commute.all (-(r+1:ℝ)) (s+1:ℝ)) (2*j+1)
  have hp : (-(r+1:ℝ))^(2*j+1) = -(r+1:ℝ)^(2*j+1) := by
    rw [neg_pow, Odd.neg_one_pow (show Odd (2*j+1) from ⟨j,by omega⟩)]
    ring
  rw [hp] at he
  have hn : (r+s+2:ℝ) ≠ 0 := by positivity
  apply (div_eq_iff hn).mpr
  have hs : (∑ a ∈ Finset.range (2*j+1), (-(r+1:ℝ))^a*(s+1:ℝ)^(2*j+1-1-a)) =
      ∑ a ∈ Finset.range (2*j+1), (-1:ℝ)^a*(r+1:ℝ)^a*(s+1:ℝ)^(2*j-a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [neg_pow]
    congr 2
  rw [hs] at he
  linear_combination -he

/-- Direct link between the source's odd Taylor powers, its Cauchy metric
and the all-order finite-difference contractions. This is a signed identity. -/
theorem source_power_coefficient_exact (p q j : ℕ) :
    (∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
      (completedGreenForwardWeight p r).re*(completedGreenForwardWeight q s).re *
        (((r+1:ℝ)^(2*j+1)+(s+1:ℝ)^(2*j+1))/(r+s+2:ℝ))) =
      greenContraction p q (2*j) := by
  simp_rw [odd_power_cauchy_quotient]
  exact (greenContraction_eq_shifted_weights p q (2*j)).symm

/-- First even correction coefficient in ANY finite canonical parity
section, read from the source coefficient contractions, without assigning a
sign. Its all-order physical asymptotic rate is a separate obligation. -/
def canonicalCorrection (s N : ℕ) (v : Fin N → ℝ) : ℝ :=
  2*∑ i, ∑ j, correctionWeight (2*i.val+s) (2*j.val+s)*
    canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s+1)*v i*v j

theorem canonicalCorrection_even_two (a : ℝ) :
    canonicalCorrection 0 2 ![a,1] = balanceCorrection a := by
  obtain ⟨h00,h02,h22,_⟩ := correctionWeight_canaries
  have h20 : correctionWeight 2 0 = -20 := by
    calc
      correctionWeight 2 0 = correctionWeight 0 2 := by unfold correctionWeight; ring
      _ = -20 := h02
  norm_num [canonicalCorrection, Fin.sum_univ_two, h00,h02,h20,h22,
    balanceCorrection, sourceCoefficient_eq_canonical]
  ring

theorem canonicalCorrection_odd_two (a : ℝ) :
    canonicalCorrection 1 2 ![a,1] = oddCorrection a := by
  obtain ⟨_,_,_,h11,h13,h33⟩ := correctionWeight_canaries
  have h31 : correctionWeight 3 1 = -42 := by
    calc
      correctionWeight 3 1 = correctionWeight 1 3 := by unfold correctionWeight; ring
      _ = -42 := h13
  norm_num [canonicalCorrection, Fin.sum_univ_two, h11,h13,h31,h33, oddCorrection]
  ring

end
end CarrySourceLaw
