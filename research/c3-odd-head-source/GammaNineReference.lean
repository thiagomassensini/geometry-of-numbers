import GammaNinePolynomial
import GammaValueBoxes

namespace CarryOddHeadSource
open CarryC3Gamma CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

def coefficientReference9 (j : Fin 9) : ℚ :=
  if hj : j.val < 7 then coefficientReference ⟨j.val,hj⟩
  else if j.val = 7 then gammaCoefficientSevenCenter else gammaCoefficientEightCenter

theorem rational_coefficient_boxes9 (j : Fin 9) :
    |rationalCoefficient 512 j.val - coefficientReference9 j| ≤ (1/10^30:ℚ) := by
  by_cases hj : j.val < 7
  · simpa only [coefficientReference9, dif_pos hj] using rational_coefficient_boxes ⟨j.val,hj⟩
  · have he : j.val=7 ∨ j.val=8 := by omega
    rcases he with h7 | h8
    · have hj7 : j = 7 := Fin.ext h7
      subst j
      simpa [coefficientReference9] using gamma_coefficient_seven_box
    · have hj8 : j = 8 := Fin.ext h8
      subst j
      simpa [coefficientReference9] using gamma_coefficient_eight_box

theorem coefficient_reference9_bound (j : Fin 9) :
    |coefficientReference9 j| ≤ (290000:ℚ) := by
  by_cases hj : j.val < 7
  · have h := coefficient_reference_bound ⟨j.val,hj⟩
    simp only [coefficientReference9, dif_pos hj]
    linarith
  · have he : j.val=7 ∨ j.val=8 := by omega
    rcases he with h7 | h8
    · have hj7 : j = 7 := Fin.ext h7
      subst j
      norm_num [coefficientReference9, gammaCoefficientSevenCenter]
    · have hj8 : j = 8 := Fin.ext h8
      subst j
      norm_num [coefficientReference9, gammaCoefficientEightCenter]

def gammaRealReference9 (r : Fin 9) : ℚ :=
  if hr : r.val < 7 then gammaRealReference ⟨r.val,hr⟩
  else if r.val = 7 then -5119986947347628576227176404/10^25
  else 10239994770557442447042746376/10^25

def gammaRationalPolynomial9 (r : Fin 9) : ℚ :=
  3*∑ j ∈ Finset.range (r.val+1),
    (2*logReference)^j/(j.factorial:ℚ)*(-1/2:ℚ)^(r.val-j)*
      coefficientReference9 ⟨r.val-j,by omega⟩

theorem gamma_rational_boxes9 (r : Fin 9) :
    |gammaRationalPolynomial9 r - gammaRealReference9 r| ≤ (1/10^25:ℚ) := by
  fin_cases r <;> decide +kernel

theorem log_three_box_tight :
    |Real.log 3-(logReference:ℝ)| ≤ (2/10^32:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (by norm_num : |(2/3:ℝ)|<1) 256
  have he : Real.log (1-(2/3:ℝ)) = -Real.log 3 := by
    rw [show 1-(2/3:ℝ)=(3:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he] at h
  have hh : |(logApprox:ℝ)-Real.log 3| ≤ (2/3:ℝ)^257/(1-2/3) := by
    simpa [logApprox,sub_eq_add_neg,abs_of_pos (by norm_num : (0:ℝ)<2/3)] using h
  have hr : |(logApprox:ℝ)-(logReference:ℝ)| ≤ (1/10^32:ℝ) := by
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using
      rat_abs_cast_le log_rational_box
  have hb := (abs_sub_le (Real.log 3) (logApprox:ℝ) (logReference:ℝ)).trans
    (add_le_add (by simpa only [abs_sub_comm] using hh) hr)
  exact hb.trans (by norm_num)

#print axioms rational_coefficient_boxes9
#print axioms gamma_rational_boxes9
#print axioms log_three_box_tight
end
end CarryOddHeadSource
