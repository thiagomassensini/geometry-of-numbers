import BinomialCoefficient

namespace CarryBinomialGreen
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
open scoped BigOperators

def realWeight (n r : ℕ) : ℝ := (((-1:ℤ)^(n-r)*n.choose r : ℤ):ℝ)

def mixedStencil (p q : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
    realWeight p r*realWeight q s*f (r+1) (s+1)

theorem homogeneous_division (d : ℕ) (x y : ℝ) :
    (x+y)*homogeneous d x y=x^(d+1)-(-y)^(d+1) := by
  have h := Commute.mul_neg_geom_sum₂ (Commute.all (-y) x) (d+1)
  simp only [sub_neg_eq_add, Nat.add_sub_cancel] at h
  rw [← h]
  congr 1
  unfold homogeneous
  apply Finset.sum_congr rfl
  intro k _
  rw [show (-y)^k=(-1:ℝ)^k*y^k from neg_pow y k]
  ring

/-- This is the quotient sampled by the original imaginary radial source. -/
theorem homogeneous_even_quotient (n : ℕ) (x y : ℝ) (hxy : x+y≠0) :
    homogeneous (2*n) x y=(x^(2*n+1)+y^(2*n+1))/(x+y) := by
  have he : (-y)^(2*n+1)= -(y^(2*n+1)) := by
    simp only [pow_succ, pow_mul]
    ring
  have h := homogeneous_division (2*n) x y
  rw [he, sub_neg_eq_add] at h
  apply (eq_div_iff hxy).mpr
  simpa [mul_comm] using h

/-- Polarized product of two independent stencils, with no missing cross. -/
theorem mixed_stencil_homogeneous (p q d : ℕ) :
    mixedStencil p q (homogeneous d)=mixedCoefficient p q d := by
  unfold mixedStencil homogeneous
  simp_rw [Finset.mul_sum]
  calc
    (∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
      ∑ k ∈ Finset.range (d+1),
        realWeight p r*realWeight q s*((-1:ℝ)^k*(r+1)^(d-k)*(s+1)^k)) =
        ∑ r ∈ Finset.range (p+1), ∑ k ∈ Finset.range (d+1), ∑ s ∈ Finset.range (q+1),
          realWeight p r*realWeight q s*((-1:ℝ)^k*(r+1)^(d-k)*(s+1)^k) := by
      apply Finset.sum_congr rfl
      intro r _
      exact Finset.sum_comm
    _ = ∑ k ∈ Finset.range (d+1), ∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
          realWeight p r*realWeight q s*((-1:ℝ)^k*(r+1)^(d-k)*(s+1)^k) := Finset.sum_comm
    _ = mixedCoefficient p q d := by
      unfold mixedCoefficient
      apply Finset.sum_congr rfl
      intro k _
      rw [shifted_power_sum, shifted_power_sum]
      unfold realWeight
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- Arbitrary-index formula applied to the actual two-variable quotient. -/
theorem original_quotient_first_correction (i j : ℕ) :
    mixedStencil (2*i) (2*j) (fun x y =>
      (x^(2*(i+j+1)+1)+y^(2*(i+j+1)+1))/(x+y)) /
      ((2*i).factorial:ℝ) / ((2*j).factorial:ℝ)=firstRadialCoefficient i j := by
  have he : mixedStencil (2*i) (2*j) (fun x y =>
      (x^(2*(i+j+1)+1)+y^(2*(i+j+1)+1))/(x+y))=
      mixedStencil (2*i) (2*j) (homogeneous (2*(i+j+1))) := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [homogeneous_even_quotient _ _ _ (by positivity)]
  rw [he, mixed_stencil_homogeneous, show 2*(i+j+1)=2*i+2*j+2 by omega]
  exact first_radial_coefficient_all_order i j

/-- Both sectors of the original quotient, retaining the parity phase. -/
theorem original_quotient_same_parity (s i j : ℕ) :
    (-1:ℝ)^s*mixedStencil (2*i+s) (2*j+s) (fun x y =>
      (x^(2*(i+j+s+1)+1)+y^(2*(i+j+s+1)+1))/(x+y)) /
      ((2*i+s).factorial:ℝ) / ((2*j+s).factorial:ℝ)=parityRadialCoefficient s i j := by
  have he : mixedStencil (2*i+s) (2*j+s) (fun x y =>
      (x^(2*(i+j+s+1)+1)+y^(2*(i+j+s+1)+1))/(x+y))=
      mixedStencil (2*i+s) (2*j+s) (homogeneous (2*(i+j+s+1))) := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro v _
    rw [homogeneous_even_quotient _ _ _ (by positivity)]
  rw [he,mixed_stencil_homogeneous,
    show 2*(i+j+s+1)=(2*i+s)+(2*j+s)+2 by omega]
  exact same_parity_first_correction s i j

end
end CarryBinomialGreen
