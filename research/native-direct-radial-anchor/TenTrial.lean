import TenSourceInputs

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryIntegralCertificate CarryOddEnergy CarrySummableRadial
open CarryCriticalRadialMargin
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

def tenOrders : Finset ℕ := Finset.range 5
/-- An independently chosen rational probe of the original five jets. It is
NOT asserted to be the exact critical vector. -/
def trialCoefficient (r : ℕ) : ℝ :=
  if r=0 then 3909825757/(10:ℝ)^21 else
  if r=1 then -(940486631/(5*(10:ℝ)^16)) else
  if r=2 then 1101622369/(5*(10:ℝ)^13) else
  if r=3 then -(1085933731/(125*(10:ℝ)^9)) else 1

def trialCoefficientBox (r : ℕ) : Box :=
  if r=0 then Box.rat 3909825757 (10^21) else
  if r=1 then Box.rat (-940486631) (5*10^16) else
  if r=2 then Box.rat 1101622369 (5*10^13) else
  if r=3 then Box.rat (-1085933731) (125*10^9) else Box.point 1

def sourceMomentBox (n : ℕ) : Box :=
  if n=1 then momentBox1 else if n=2 then momentBox2 else if n=3 then momentBox3 else
  if n=4 then momentBox4 else if n=5 then momentBox5 else if n=6 then momentBox6 else
  if n=7 then momentBox7 else if n=8 then momentBox8 else if n=9 then momentBox9 else Box.all

theorem trial_coefficient_box_mem (i : ℕ) (hi : i<5) :
    (trialCoefficientBox i).Mem (trialCoefficient i) := by
  interval_cases i <;> simp [trialCoefficientBox,trialCoefficient]
  · convert (mem_rat 3909825757 (10^21)) using 1 <;> norm_num
  · convert (mem_rat (-940486631) (5*10^16)) using 1 <;> norm_num
  · convert (mem_rat 1101622369 (5*10^13)) using 1 <;> norm_num
  · convert (mem_rat (-1085933731) (125*10^9)) using 1 <;> norm_num
  · simpa only [Int.cast_one] using (mem_point 1)

theorem ten_moment_box_mem (n : ℕ) (hn : 1≤n) (hmn : n≤9) :
    (sourceMomentBox n).Mem (canonicalCompletedNativeLogDerivativeMoment n) := by
  interval_cases n <;> simp [sourceMomentBox]
  · exact moment_box_1_mem
  · exact moment_box_2_mem
  · exact moment_box_3_mem
  · exact moment_box_4_mem
  · exact moment_box_5_mem
  · exact moment_box_6_mem
  · exact moment_box_7_mem
  · exact moment_box_8_mem
  · exact moment_box_9_mem

def trialHeadBox : Box := Box.sum (fun i => Box.sum (fun j =>
  ((trialCoefficientBox i).mul (trialCoefficientBox j)).mul (sourceMomentBox (i+j+1))) 5) 5

theorem trial_head_box_mem : trialHeadBox.Mem (oddCanonicalForm tenOrders trialCoefficient) := by
  have hx := mem_sum (fun i => Box.sum (fun j =>
      ((trialCoefficientBox i).mul (trialCoefficientBox j)).mul (sourceMomentBox (i+j+1))) 5)
    (fun i => ∑ j ∈ Finset.range 5, trialCoefficient i*trialCoefficient j*
      canonicalCompletedNativeLogDerivativeMoment (i+j+1)) 5
    (by
      intro i hi
      apply mem_sum
      intro j hj
      apply mem_mul (mem_mul (trial_coefficient_box_mem i hi) (trial_coefficient_box_mem j hj))
      exact ten_moment_box_mem (i+j+1) (by omega) (by omega))
  simpa [trialHeadBox,oddCanonicalForm,tenOrders] using hx

/-- This is positivity of one RATIONAL trial, NOT the critical pivot. -/
theorem rational_trial_head_lower : (7/(10:ℝ)^30) < oddCanonicalForm tenOrders trialCoefficient := by
  have h := mem_of_contained trial_head_box_mem
    (show trialHeadBox.contained (.finite (75*10^29) (10*10^30))=true by decide +kernel)
  norm_num [Box.Mem,intervalScale] at h
  norm_num at *
  linarith [h.1]

end
end CarryDirectAnchor
