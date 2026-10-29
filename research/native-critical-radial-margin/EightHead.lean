import EightCritical

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryIntegralCertificate CarryOddEnergy
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

def eightOrders : Finset ℕ := Finset.range 4
def eightCoefficients (r : ℕ) : ℝ := if r=0 then critical0 else if r=1 then critical1 else if r=2 then critical2 else 1

def eightCoeffBox (r : ℕ) : Box := if r=0 then criticalBox0 else if r=1 then criticalBox1 else if r=2 then criticalBox2 else Box.point 1
def eightMomentBox (n : ℕ) : Box :=
  if n=1 then momentBox1 else if n=2 then momentBox2 else if n=3 then momentBox3 else
  if n=4 then momentBox4 else if n=5 then momentBox5 else if n=6 then momentBox6 else
  if n=7 then momentBox7 else Box.all

theorem eight_coeff_box_mem (i : ℕ) (hi : i<4) :
    (eightCoeffBox i).Mem (eightCoefficients i) := by
  interval_cases i <;> simp [eightCoeffBox,eightCoefficients]
  · exact critical0_box_mem
  · exact critical1_box_mem
  · exact critical2_box_mem
  · simpa only [Int.cast_one] using (mem_point 1)

theorem eight_moment_box_mem (n : ℕ) (hn : 1≤n) (hmn : n≤7) :
    (eightMomentBox n).Mem (hm n) := by
  interval_cases n <;> simp [eightMomentBox]
  · exact moment_box_1_mem
  · exact moment_box_2_mem
  · exact moment_box_3_mem
  · exact moment_box_4_mem
  · exact moment_box_5_mem
  · exact moment_box_6_mem
  · exact moment_box_7_mem

def eightHeadBox : Box := Box.sum (fun i => Box.sum (fun j =>
  ((eightCoeffBox i).mul (eightCoeffBox j)).mul (eightMomentBox (i+j+1))) 4) 4

theorem eight_head_box_mem : eightHeadBox.Mem (oddCanonicalForm eightOrders eightCoefficients) := by
  have hx := mem_sum (fun i => Box.sum (fun j =>
      ((eightCoeffBox i).mul (eightCoeffBox j)).mul (eightMomentBox (i+j+1))) 4)
    (fun i => ∑ j ∈ Finset.range 4, eightCoefficients i*eightCoefficients j*hm (i+j+1)) 4
    (by
      intro i hi
      apply mem_sum
      intro j hj
      apply mem_mul (mem_mul (eight_coeff_box_mem i hi) (eight_coeff_box_mem j hj))
      exact eight_moment_box_mem (i+j+1) (by omega) (by omega))
  simpa [eightHeadBox,oddCanonicalForm,eightOrders] using hx

/-- A certified strict lower bound for the fully crossed original quadratic
head, from source-integral enclosures only. This also supplies its sign;
it is not a new geometric law of sign. -/
theorem eight_head_strict_lower : (1/(10:ℝ)^23) < oddCanonicalForm eightOrders eightCoefficients := by
  have h := mem_of_contained eight_head_box_mem
    (show eightHeadBox.contained (.finite (2*10^37) (4*10^37))=true by decide +kernel)
  norm_num [Box.Mem, intervalScale] at h
  norm_num at *
  linarith [h.1]

end
end CarryCriticalRadialMargin
