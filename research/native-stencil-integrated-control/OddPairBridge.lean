import SumReindex

namespace CarryCenteredStirling
open CarrySelfAdjointOperator CarryOddCauchy
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- One source-origin beta term becomes the corresponding upper centered
binomial term, with its original factorial and sign. -/
theorem odd_beta_term_to_centered (r s i d : ℕ) (hi : i≤2*r+1) :
    ((-1:ℂ)^(2*s+1)/((2*r+1).factorial:ℂ))*
      (completedGreenForwardWeight (2*r+1) i * (((i+1:ℕ):ℂ)^d)*
        ((i+1).factorial:ℂ)/((i+(2*s+1)+2).factorial:ℂ)) =
    (((2*r+1)+(2*s+1)+2).factorial:ℂ)⁻¹ *
      ((-1:ℂ)^i*(((2*r+1)+(2*s+1)+2).choose ((2*s+1)+i+2):ℂ)*
        (((i:ℂ)+1)^(d+1))) := by
  have hf := shifted_factorial_binomial (2*r+1) (2*s+1) i hi
  unfold completedGreenForwardWeight
  push_cast
  rw [odd_stencil_sign r i hi]
  have hs : (-1:ℂ)^(2*s+1) = -1 := odd_exponent_sign s
  rw [hs,pow_succ]
  linear_combination ((-1:ℂ)^i)*((i:ℂ)+1)^d*hf


/-- The complete two-leg physical stencil sum equals the negative centered
finite difference for arbitrary odd stencil orders and odd source layer. -/
theorem odd_stencil_pair_eq_centered (r s q : ℕ) :
    stencilPair (2*r+1) (2*s+1) (2*q+1) =
      -centeredDifference ((2*r+1)+(2*s+1)+2) (2*q+2) (((2*s+1:ℕ):ℂ)+1) := by
  let m := 2*r+1
  let n := 2*s+1
  let N := m+n+2
  let d := 2*q+1
  let p := 2*q+2
  have hpow : d+1=p := by dsimp [d,p]
  have hN : Even N := by
    refine ⟨r+s+2,?_⟩
    dsimp [N,m,n]
    omega
  have htop : ((-1:ℂ)^n/(m.factorial:ℂ))*
      (∑ i ∈ Finset.range (m+1), completedGreenForwardWeight m i *
        (((i+1:ℕ):ℂ)^d)*((i+1).factorial:ℂ)/((i+n+2).factorial:ℂ)) =
      (N.factorial:ℂ)⁻¹*(∑ i ∈ Finset.range (m+1),
        (-1:ℂ)^i*(N.choose (n+i+2):ℂ)*((i:ℂ)+1)^p) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hii : i≤2*r+1 := by dsimp [m] at hi; have := Finset.mem_range.mp hi; omega
    have he := odd_beta_term_to_centered r s i d hii
    rw [hpow] at he
    simpa only [m,n,N,Nat.cast_add,Nat.cast_one] using he
  have hbottom : ((-1:ℂ)^m/(n.factorial:ℂ))*
      (∑ j ∈ Finset.range (n+1), completedGreenForwardWeight n j *
        (((j+1:ℕ):ℂ)^d)*((j+1).factorial:ℂ)/((j+m+2).factorial:ℂ)) =
      (N.factorial:ℂ)⁻¹*(∑ j ∈ Finset.range (n+1),
        (-1:ℂ)^j*(N.choose (m+j+2):ℂ)*((j:ℂ)+1)^p) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjj : j≤2*s+1 := by dsimp [n] at hj; have := Finset.mem_range.mp hj; omega
    have he := odd_beta_term_to_centered s r j d hjj
    rw [hpow] at he
    have hcomm : (2*s+1)+(2*r+1)+2=(2*r+1)+(2*s+1)+2 := by omega
    rw [hcomm] at he
    simpa only [m,n,N,Nat.cast_add,Nat.cast_one] using he
  have hsign (k : ℕ) (hk : k≤N) : (-1:ℂ)^(N-k)=(-1:ℂ)^k := by
    apply neg_one_pow_congr
    rw [Nat.even_iff,Nat.even_iff]
    rcases hN with ⟨z,hz⟩
    omega
  have hsum : (∑ k ∈ Finset.range (N+1),
      (((-1:ℤ)^(N-k)*(N.choose k:ℤ):ℤ):ℂ)*((k:ℂ)-((n:ℂ)+1))^p) =
      ∑ k ∈ Finset.range (N+1),
        (-1:ℂ)^k*(N.choose k:ℂ)*((k:ℂ)-((n:ℂ)+1))^p := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k≤N := by have := Finset.mem_range.mp hk; omega
    simp only [Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast]
    rw [hsign k hkN]
  have hsplit : (∑ k ∈ Finset.range (N+1),
      (-1:ℂ)^k*(N.choose k:ℂ)*((k:ℂ)-((n:ℂ)+1))^p) =
      -(∑ i ∈ Finset.range (m+1), (-1:ℂ)^i*(N.choose (n+i+2):ℂ)*((i:ℂ)+1)^p) -
      ∑ j ∈ Finset.range (n+1), (-1:ℂ)^j*(N.choose (m+j+2):ℂ)*((j:ℂ)+1)^p := by
    simpa only [m,n,N,p,Nat.cast_add,Nat.cast_one] using centered_odd_split r s q
  rw [centered_difference_sum]
  change stencilPair m n d = -((N.factorial:ℂ)⁻¹ * _)
  rw [hsum,hsplit]
  rw [stencil_pair_physical_reduction,htop,hbottom]
  ring


/-- The full original two-address Cauchy stencil has the proposed
all-order Lambda coefficient, with no positivity hypothesis. -/
theorem odd_stencil_correction_all_order (r s : ℕ) :
    let m := 2*r+1
    let n := 2*s+1
    stencilPair m n (m+n+3) =
      -(((m:ℂ)+1)*((m:ℂ)+2)*(2*(m:ℂ)+3)/12 +
        ((n:ℂ)+1)*((n:ℂ)+2)*(2*(n:ℂ)+3)/12 +
        ((((m:ℂ)+1)*((m:ℂ)+2)/2)-(((n:ℂ)+1)*((n:ℂ)+2)/2))^2/2) := by
  dsimp only
  have h := odd_stencil_pair_eq_centered r s (r+s+2)
  have hd : 2*(r+s+2)+1=(2*r+1)+(2*s+1)+3 := by omega
  have hp : 2*(r+s+2)+2=(2*r+1)+(2*s+1)+4 := by omega
  rw [hd,hp,centered_correction_eq_lambda] at h
  exact h

end
end CarryCenteredStirling
