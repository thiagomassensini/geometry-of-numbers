import Mathlib
namespace CarryMaterialPivotCertificate
noncomputable section
set_option autoImplicit false

theorem enclose_add {x y a b c d L U : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hl : L ≤ a+c) (hu : b+d ≤ U) : L ≤ x+y ∧ x+y ≤ U := by
  constructor <;> linarith only [hx.1,hx.2,hy.1,hy.2,hl,hu]

theorem enclose_neg {x a b : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    -b ≤ -x ∧ -x ≤ -a := by constructor <;> linarith only [hx.1,hx.2]

theorem enclose_mul {x y a b c d L U : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hll : L ≤ a*c) (hlr : L ≤ a*d) (hrl : L ≤ b*c) (hrr : L ≤ b*d)
    (ull : a*c ≤ U) (ulr : a*d ≤ U) (url : b*c ≤ U) (urr : b*d ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  have hbound (z : ℝ) (hl : L ≤ z*c) (hr : L ≤ z*d)
      (ul : z*c ≤ U) (ur : z*d ≤ U) : L ≤ z*y ∧ z*y ≤ U := by
    rcases le_total 0 z with hz | hz
    · have h1 := mul_le_mul_of_nonneg_left hy.1 hz
      have h2 := mul_le_mul_of_nonneg_left hy.2 hz
      exact ⟨hl.trans h1,h2.trans ur⟩
    · have h1 := mul_le_mul_of_nonpos_left hy.2 hz
      have h2 := mul_le_mul_of_nonpos_left hy.1 hz
      exact ⟨hr.trans h1,h2.trans ul⟩
  have ha := hbound a hll hlr ull ulr
  have hb := hbound b hrl hrr url urr
  rcases le_total 0 y with hy0 | hy0
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_right hx.1 hy0),
      (mul_le_mul_of_nonneg_right hx.2 hy0).trans hb.2⟩
  · exact ⟨hb.1.trans (mul_le_mul_of_nonpos_right hx.2 hy0),
      (mul_le_mul_of_nonpos_right hx.1 hy0).trans ha.2⟩

theorem enclose_inv {x a b L U : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : 0 < a) (hl : L ≤ 1/b) (hu : 1/a ≤ U) :
    L ≤ 1/x ∧ 1/x ≤ U := by
  have hx0 : 0 < x := ha.trans_le hx.1
  exact ⟨hl.trans (one_div_le_one_div_of_le hx0 hx.2),
    (one_div_le_one_div_of_le ha hx.1).trans hu⟩
end
end CarryMaterialPivotCertificate
