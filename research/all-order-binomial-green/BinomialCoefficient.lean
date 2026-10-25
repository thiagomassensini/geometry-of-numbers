import ShiftedDifferences

/-! Arbitrary-index extraction from the original two-argument stencil.
The coefficient matrix is signed; no positivity is assumed or inferred. -/
namespace CarryBinomialGreen
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

/-- Alternating homogeneous numerator after division by x+y. -/
def homogeneous (d : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d+1), (-1:ℝ)^k*x^(d-k)*y^k

/-- The two original stencils acting on a homogeneous divided power. -/
def mixedCoefficient (p q d : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (d+1), (-1:ℝ)^k*shiftedPower p (d-k)*shiftedPower q k

/-- Every term below the combined stencil order vanishes. -/
theorem mixed_coefficient_zero (p q d : ℕ) (hd : d<p+q) :
    mixedCoefficient p q d=0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hkbound := Finset.mem_range.mp hk
  by_cases hq : k<q
  · rw [shifted_power_zero hq, mul_zero]
  · rw [shifted_power_zero (show d-k<p by omega), mul_zero, zero_mul]

theorem mixed_coefficient_leading (p q : ℕ) :
    mixedCoefficient p q (p+q)=(-1:ℝ)^q*(p.factorial:ℝ)*(q.factorial:ℝ) := by
  unfold mixedCoefficient
  rw [Finset.sum_eq_single q]
  · rw [show p+q-q=p by omega, shifted_power_self, shifted_power_self]
  · intro k hk hkq
    have hkbound := Finset.mem_range.mp hk
    by_cases hq : k<q
    · rw [shifted_power_zero hq, mul_zero]
    · rw [shifted_power_zero (show p+q-k<p by omega), mul_zero, zero_mul]
  · intro hq
    exact (hq (Finset.mem_range.mpr (by omega))).elim

/-- The next coefficient contains exactly three surviving polarized terms. -/
theorem mixed_coefficient_next (p q : ℕ) :
    mixedCoefficient p q (p+q+2)=
      (-1:ℝ)^q*(p.factorial:ℝ)*(q.factorial:ℝ)*
        (secondOffset p+secondOffset q-triangular p*triangular q) := by
  unfold mixedCoefficient
  let f := fun k => (-1:ℝ)^k*shiftedPower p (p+q+2-k)*shiftedPower q k
  change (∑ k ∈ Finset.range (p+q+2+1), f k)=_
  have hlo : (∑ k ∈ Finset.range q, f k)=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    dsimp [f]
    rw [shifted_power_zero (Finset.mem_range.mp hk), mul_zero]
  have hhi : (∑ k ∈ Finset.range p, f (q+3+k))=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    dsimp [f]
    rw [shifted_power_zero (show p+q+2-(q+3+k)<p by have := Finset.mem_range.mp hk; omega),
      mul_zero, zero_mul]
  rw [show p+q+2+1=(q+3)+p by omega, Finset.sum_range_add, hhi, add_zero,
    Finset.sum_range_add, hlo, zero_add]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero, zero_add]
  dsimp [f]
  rw [show p+q+2-q=p+2 by omega, show p+q+2-(q+1)=p+1 by omega,
    show p+q+2-(q+2)=p by omega, shifted_power_self,
    shifted_power_first, shifted_power_first, shifted_power_second, shifted_power_second,
    shifted_power_self]
  simp only [pow_add, pow_one, neg_one_sq]
  ring

/-- The binomial coefficient of the first radial correction in even sectors. -/
def firstRadialCoefficient (i j : ℕ) : ℝ :=
  secondOffset (2*i)+secondOffset (2*j)-triangular (2*i)*triangular (2*j)

theorem first_radial_coefficient_all_order (i j : ℕ) :
    mixedCoefficient (2*i) (2*j) (2*i+2*j+2) /
      ((2*i).factorial:ℝ) / ((2*j).factorial:ℝ)=firstRadialCoefficient i j := by
  rw [mixed_coefficient_next]
  have he : (-1:ℝ)^(2*j)=1 := by rw [pow_mul]; norm_num
  rw [he, one_mul]
  unfold firstRadialCoefficient
  have hp : ((2*i).factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hq : ((2*j).factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [hp,hq]

/-- Both physical parity sectors, with the phase retained explicitly. -/
def parityRadialCoefficient (s i j : ℕ) : ℝ :=
  secondOffset (2*i+s)+secondOffset (2*j+s)-triangular (2*i+s)*triangular (2*j+s)

theorem same_parity_first_correction (s i j : ℕ) :
    (-1:ℝ)^s*mixedCoefficient (2*i+s) (2*j+s) ((2*i+s)+(2*j+s)+2) /
      ((2*i+s).factorial:ℝ) / ((2*j+s).factorial:ℝ)=parityRadialCoefficient s i j := by
  rw [mixed_coefficient_next]
  have he : (-1:ℝ)^s*(-1:ℝ)^(2*j+s)=1 := by
    rw [← pow_add, show s+(2*j+s)=2*(j+s) by omega, pow_mul]
    norm_num
  have hp : ((2*i+s).factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hq : ((2*j+s).factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  calc
    _ = ((-1:ℝ)^s*(-1:ℝ)^(2*j+s))*parityRadialCoefficient s i j := by
      unfold parityRadialCoefficient
      field_simp [hp,hq]
    _ = parityRadialCoefficient s i j := by rw [he, one_mul]

/-- Exact regression of all six independent coefficients from PR88. -/
theorem even_coefficient_regression :
    firstRadialCoefficient 0 0=1 ∧ firstRadialCoefficient 0 1=20 ∧
    firstRadialCoefficient 0 2=126 ∧ firstRadialCoefficient 1 1=14 ∧
    firstRadialCoefficient 1 2=75 ∧ firstRadialCoefficient 2 2=55 := by
  norm_num [firstRadialCoefficient,secondOffset,triangular]

/-- These weights do not define a positive kernel by themselves. -/
theorem coefficient_two_by_two_negative :
    firstRadialCoefficient 0 0*firstRadialCoefficient 1 1-
      firstRadialCoefficient 0 1*firstRadialCoefficient 1 0= -386 := by
  norm_num [firstRadialCoefficient,secondOffset,triangular]

end
end CarryBinomialGreen
