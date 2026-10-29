import SourceTaylor

/-! Exact contractions of the OLD shifted forward-difference weights.
These are coefficient identities of the original divided-power kernel,
not a positive replacement kernel. -/
namespace CarrySourceLaw
open CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- The signed weights on nodes r+1, the same shifted grid as the source. -/
def stencilPower (p d : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (p+1), (-1:ℝ)^(p-r)*(p.choose r:ℝ)*(r+1:ℝ)^d

theorem stencilPower_below {p d : ℕ} (hd : d<p) : stencilPower p d = 0 := by
  have h := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hd) 1
  rw [fwdDiff_iter_eq_sum_shift] at h
  simpa [stencilPower, smul_eq_mul, add_comm] using h

theorem stencilPower_self (p : ℕ) : stencilPower p p = (p.factorial:ℝ) := by
  have h := congrFun (fwdDiff_iter_eq_factorial (R := ℝ) (n := p)) 1
  rw [fwdDiff_iter_eq_sum_shift] at h
  simpa [stencilPower, smul_eq_mul, add_comm] using h

def firstStencilSurplus (p : ℕ) : ℝ := stencilPower p (p+1)/(p.factorial:ℝ)
def secondStencilSurplus (p : ℕ) : ℝ := stencilPower p (p+2)/(p.factorial:ℝ)

/-- Alternating homogeneous coefficient of the transverse Green quotient.
Factorial/phase normalization is kept separate and explicit. -/
def greenContraction (p q d : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (d+1), (-1:ℝ)^a * stencilPower p a * stencilPower q (d-a)

theorem greenContraction_below {p q d : ℕ} (hd : d<p+q) :
    greenContraction p q d = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hap : a<p
  · rw [stencilPower_below hap]; ring
  · have hqa : d-a<q := by have := Finset.mem_range.mp ha; omega
    rw [stencilPower_below hqa]; ring

theorem greenContraction_leading (p q : ℕ) :
    greenContraction p q (p+q) = (-1:ℝ)^p*(p.factorial:ℝ)*(q.factorial:ℝ) := by
  unfold greenContraction
  rw [Finset.sum_eq_single p]
  · rw [stencilPower_self, show p+q-p=q by omega, stencilPower_self]
  · intro a ha hne
    by_cases hap : a<p
    · rw [stencilPower_below hap]; ring
    · have hqa : p+q-a<q := by have := Finset.mem_range.mp ha; omega
      rw [stencilPower_below hqa]; ring
  · intro hp
    exact False.elim (hp (Finset.mem_range.mpr (by omega)))

/-- Every degree except p,p+1,p+2 cancels EXACTLY in the first even
correction. No asymptotic estimate and no sign is used. -/
theorem greenContraction_second (p q : ℕ) :
    greenContraction p q (p+q+2) =
      (-1:ℝ)^p*(p.factorial:ℝ)*(q.factorial:ℝ)*
        (secondStencilSurplus p + secondStencilSurplus q -
          firstStencilSurplus p*firstStencilSurplus q) := by
  classical
  let term : ℕ → ℝ := fun a => (-1:ℝ)^a*stencilPower p a*stencilPower q (p+q+2-a)
  have hs : (∑ a ∈ Finset.range (p+q+2+1), term a) = ∑ a ∈ ({p,p+1,p+2}:Finset ℕ), term a := by
    symm
    apply Finset.sum_subset
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      apply Finset.mem_range.mpr
      omega
    · intro a ha hn
      have ha' := Finset.mem_range.mp ha
      have hn' : a≠p ∧ a≠p+1 ∧ a≠p+2 := by simpa using hn
      dsimp only [term]
      by_cases hap : a<p
      · rw [stencilPower_below hap]; ring
      · have hqa : p+q+2-a<q := by omega
        rw [stencilPower_below hqa]; ring
  unfold greenContraction
  rw [hs]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
  dsimp only [term]
  rw [show p+q+2-p=q+2 by omega, show p+q+2-(p+1)=q+1 by omega,
    show p+q+2-(p+2)=q by omega, stencilPower_self, stencilPower_self]
  unfold firstStencilSurplus secondStencilSurplus
  have hp : (p.factorial:ℝ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
  have hq : (q.factorial:ℝ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  rw [pow_add, pow_add]
  norm_num
  field_simp
  ring

/-- The minus sign is i^2 from the original transverse ray. -/
def correctionWeight (p q : ℕ) : ℝ :=
  firstStencilSurplus p*firstStencilSurplus q - secondStencilSurplus p-secondStencilSurplus q

theorem correctionWeight_eq_contraction (p q : ℕ) :
    -(-1:ℝ)^p/((p.factorial:ℝ)*(q.factorial:ℝ))*greenContraction p q (p+q+2) =
      correctionWeight p q := by
  rw [greenContraction_second]
  unfold correctionWeight
  have hp : (p.factorial:ℝ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
  have hq : (q.factorial:ℝ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  have he : ((-1:ℝ)^p)^2 = 1 := by rw [← pow_mul, Nat.mul_comm p 2, pow_mul]; norm_num
  field_simp
  rw [he]
  ring

/-- Kernel-checked canaries from the original shifted stencil. -/
theorem correctionWeight_canaries :
    correctionWeight 0 0 = -1 ∧ correctionWeight 0 2 = -20 ∧
    correctionWeight 2 2 = -14 ∧ correctionWeight 1 1 = -5 ∧
    correctionWeight 1 3 = -42 ∧ correctionWeight 3 3 = -30 := by
  norm_num [correctionWeight, firstStencilSurplus, secondStencilSurplus,
    stencilPower, Finset.sum_range_succ, Nat.factorial]

end
end CarrySourceLaw
