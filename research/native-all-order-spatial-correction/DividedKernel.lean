import DifferencePowers
import Mathlib.Algebra.Ring.GeomSum

namespace CarrySpatialCorrection
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Odd divided powers, before taking real parts or diagonalizing. -/
theorem odd_divided_power (x y : ℂ) (p : ℕ) (hp : Odd p) (hxy : x+y≠0) :
    (x^p+y^p)/(x+y)=
      ∑ l ∈ Finset.range p, (-1:ℂ)^l*x^(p-1-l)*y^l := by
  apply (div_eq_iff hxy).mpr
  have h := geom_sum₂_mul (-y) x p
  rw [hp.neg_pow] at h
  have hh : (∑ l ∈ Finset.range p, (-y)^l*x^(p-1-l)) =
      ∑ l ∈ Finset.range p, (-1:ℂ)^l*x^(p-1-l)*y^l := by
    apply Finset.sum_congr rfl
    intro l _
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  rw [hh, show -y-x= -(x+y) by ring] at h
  linear_combination h

/-- Finite algebraic extraction, with BOTH ordered source pairings retained. -/
def dividedCoefficient (m n p : ℕ) : ℂ :=
  ∑ l ∈ Finset.range p,
    (-1:ℂ)^l*differencePower m (p-1-l)*differencePower n l

theorem divided_below {m n p : ℕ} (hp : p < m+n+1) :
    dividedCoefficient m n p=0 := by
  unfold dividedCoefficient
  apply Finset.sum_eq_zero
  intro l hl
  have hlp := Finset.mem_range.mp hl
  by_cases hn : l<n
  · rw [difference_power_below hn, mul_zero]
  · rw [difference_power_below (show p-1-l < m by omega), mul_zero, zero_mul]

theorem divided_leading (m s : ℕ) : dividedCoefficient m (2*s) (m+2*s+1)=1 := by
  unfold dividedCoefficient
  rw [Finset.sum_eq_single (2*s)]
  · rw [show m+2*s+1-1-2*s=m by omega, difference_power_diagonal,
      difference_power_diagonal]
    simp [pow_mul]
  · intro l hl hne
    have hlp := Finset.mem_range.mp hl
    by_cases hn : l<2*s
    · rw [difference_power_below hn, mul_zero]
    · rw [difference_power_below (show m+2*s+1-1-l < m by omega), mul_zero, zero_mul]
  · intro he
    exact (he (Finset.mem_range.mpr (by omega))).elim

/-- The two-index coefficient in the first excess odd degree. -/
def spatialCorrection (m n : ℕ) : ℂ := curvature m+curvature n-slope m*slope n

/-- All but THREE terms cancel for arbitrary stencil orders. No sign hypothesis. -/
theorem divided_first_correction (m s : ℕ) :
    dividedCoefficient m (2*s) (m+2*s+3)=spatialCorrection m (2*s) := by
  classical
  let f := fun l => (-1:ℂ)^l*differencePower m (m+2*s+3-1-l)*differencePower (2*s) l
  have hs : ({2*s, 2*s+1, 2*s+2} : Finset ℕ) ⊆ Finset.range (m+2*s+3) := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hz : ∀ l ∈ Finset.range (m+2*s+3), l ∉ ({2*s,2*s+1,2*s+2} : Finset ℕ) → f l=0 := by
    intro l hl he
    have hlp := Finset.mem_range.mp hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    unfold f
    by_cases hn : l<2*s
    · rw [difference_power_below hn, mul_zero]
    · rw [difference_power_below (show m+2*s+3-1-l < m by omega), mul_zero, zero_mul]
  have hsum := Finset.sum_subset hs hz
  change (∑ l ∈ Finset.range (m+2*s+3), f l)=_
  rw [← hsum]
  simp only [Finset.sum_insert (show 2*s ∉ ({2*s+1,2*s+2} : Finset ℕ) by simp),
    Finset.sum_insert (show 2*s+1 ∉ ({2*s+2} : Finset ℕ) by simp), Finset.sum_singleton, f]
  simp only [show m+2*s+3-1-2*s=m+2 by omega,
    show m+2*s+3-1-(2*s+1)=m+1 by omega,
    show m+2*s+3-1-(2*s+2)=m by omega,
    difference_power_diagonal, difference_power_one_above, difference_power_two_above]
  norm_num [pow_add, pow_mul, spatialCorrection]
  ring

theorem spatial_correction_diagonal (m : ℕ) :
    spatialCorrection m m=((m:ℂ)+1)*((m:ℂ)+2)*(2*(m:ℂ)+3)/6 := by
  unfold spatialCorrection curvature slope
  ring

end
end CarrySpatialCorrection
