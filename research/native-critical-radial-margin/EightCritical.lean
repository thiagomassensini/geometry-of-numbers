import EightInputs

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryIntegralCertificate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

abbrev hm (n : ℕ) : ℝ := canonicalCompletedNativeLogDerivativeMoment n

def det3 (a b c d e f g h i : ℝ) : ℝ := a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
def det3Box (a b c d e f g h i : Box) : Box :=
  ((a.mul ((e.mul i).add (f.mul h).neg)).add
    (b.mul ((d.mul i).add (f.mul g).neg)).neg).add
      (c.mul ((d.mul h).add (e.mul g).neg))

theorem det3_box_mem {a b c d e f g h i : ℝ} {A B C D E F G H I : Box}
    (ha : A.Mem a) (hb : B.Mem b) (hc : C.Mem c) (hd : D.Mem d)
    (he : E.Mem e) (hf : F.Mem f) (hg : G.Mem g) (hh : H.Mem h) (hi : I.Mem i) :
    (det3Box A B C D E F G H I).Mem (det3 a b c d e f g h i) := by
  simpa only [det3Box,det3,sub_eq_add_neg] using
    mem_add (mem_add (mem_mul ha (mem_add (mem_mul he hi) (mem_neg (mem_mul hf hh))))
      (mem_neg (mem_mul hb (mem_add (mem_mul hd hi) (mem_neg (mem_mul hf hg))))))
      (mem_mul hc (mem_add (mem_mul hd hh) (mem_neg (mem_mul he hg))))

/-- Original three-by-three old odd block and its Cramer coefficients. -/
def oldDet : ℝ := det3 (hm 1) (hm 2) (hm 3) (hm 2) (hm 3) (hm 4) (hm 3) (hm 4) (hm 5)
def num0 : ℝ := det3 (hm 4) (hm 2) (hm 3) (hm 5) (hm 3) (hm 4) (hm 6) (hm 4) (hm 5)
def num1 : ℝ := det3 (hm 1) (hm 4) (hm 3) (hm 2) (hm 5) (hm 4) (hm 3) (hm 6) (hm 5)
def num2 : ℝ := det3 (hm 1) (hm 2) (hm 4) (hm 2) (hm 3) (hm 5) (hm 3) (hm 4) (hm 6)
def critical0 : ℝ := -num0/oldDet
def critical1 : ℝ := -num1/oldDet
def critical2 : ℝ := -num2/oldDet

def oldDetBox : Box := det3Box momentBox1 momentBox2 momentBox3 momentBox2 momentBox3 momentBox4 momentBox3 momentBox4 momentBox5
def num0Box : Box := det3Box momentBox4 momentBox2 momentBox3 momentBox5 momentBox3 momentBox4 momentBox6 momentBox4 momentBox5
def num1Box : Box := det3Box momentBox1 momentBox4 momentBox3 momentBox2 momentBox5 momentBox4 momentBox3 momentBox6 momentBox5
def num2Box : Box := det3Box momentBox1 momentBox2 momentBox4 momentBox2 momentBox3 momentBox5 momentBox3 momentBox4 momentBox6

def criticalBox0 : Box := .finite (-5555575000000000000000000000000000000000000000000000) (-5555425000000000000000000000000000000000000000000000)
def criticalBox1 : Box := .finite 13993900800000000000000000000000000000000000000000000000 13993938300000000000000000000000000000000000000000000000
def criticalBox2 : Box := .finite (-7578390300000000000000000000000000000000000000000000000000) (-7578382200000000000000000000000000000000000000000000000000)

theorem old_det_box_mem : oldDetBox.Mem oldDet := by
  exact det3_box_mem moment_box_1_mem moment_box_2_mem moment_box_3_mem
    moment_box_2_mem moment_box_3_mem moment_box_4_mem moment_box_3_mem moment_box_4_mem moment_box_5_mem

theorem old_det_box_positive : oldDetBox.positive = true := by decide +kernel

theorem old_det_positive : 0 < oldDet := pos_of_mem old_det_box_mem old_det_box_positive

theorem num0_box_mem : num0Box.Mem num0 := by
  exact det3_box_mem moment_box_4_mem moment_box_2_mem moment_box_3_mem
    moment_box_5_mem moment_box_3_mem moment_box_4_mem moment_box_6_mem moment_box_4_mem moment_box_5_mem

theorem num1_box_mem : num1Box.Mem num1 := by
  exact det3_box_mem moment_box_1_mem moment_box_4_mem moment_box_3_mem
    moment_box_2_mem moment_box_5_mem moment_box_4_mem moment_box_3_mem moment_box_6_mem moment_box_5_mem

theorem num2_box_mem : num2Box.Mem num2 := by
  exact det3_box_mem moment_box_1_mem moment_box_2_mem moment_box_4_mem
    moment_box_2_mem moment_box_3_mem moment_box_5_mem moment_box_3_mem moment_box_4_mem moment_box_6_mem

theorem critical0_box_mem : criticalBox0.Mem critical0 := by
  apply mem_of_contained (mem_div (mem_neg num0_box_mem) old_det_box_mem)
  exact (show (num0Box.neg.div oldDetBox).contained criticalBox0 = true by decide +kernel)

theorem critical1_box_mem : criticalBox1.Mem critical1 := by
  apply mem_of_contained (mem_div (mem_neg num1_box_mem) old_det_box_mem)
  exact (show (num1Box.neg.div oldDetBox).contained criticalBox1 = true by decide +kernel)

theorem critical2_box_mem : criticalBox2.Mem critical2 := by
  apply mem_of_contained (mem_div (mem_neg num2_box_mem) old_det_box_mem)
  exact (show (num2Box.neg.div oldDetBox).contained criticalBox2 = true by decide +kernel)

/-- Cramer solves all three old crossings exactly, using only nonzero
old determinant and no sign of the new residual. -/
theorem eight_critical_old_rows :
    hm 1*critical0+hm 2*critical1+hm 3*critical2+hm 4=0 ∧
    hm 2*critical0+hm 3*critical1+hm 4*critical2+hm 5=0 ∧
    hm 3*critical0+hm 4*critical1+hm 5*critical2+hm 6=0 := by
  have hn : oldDet ≠ 0 := old_det_positive.ne'
  unfold critical0 critical1 critical2 num0 num1 num2
  constructor
  · field_simp [hn]; unfold oldDet det3; ring
  constructor <;> field_simp [hn] <;> unfold oldDet det3 <;> ring

end
end CarryCriticalRadialMargin
