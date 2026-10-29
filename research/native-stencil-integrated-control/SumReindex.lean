import ReindexFactor
import OddCauchyRows

namespace CarryCenteredStirling
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Generic exact division of a centered finite sum into lower and upper
address ranges, retaining the central term. -/
theorem centered_sum_split_generic (N c : ℕ) (hc : c≤N) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.range (N+1), f k) =
      (∑ j ∈ Finset.range c, f (c-1-j)) + f c +
      ∑ i ∈ Finset.range (N-c), f (c+1+i) := by
  have hn : N+1=c+((N-c)+1) := by omega
  rw [hn,Finset.sum_range_add]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero]
  rw [← Finset.sum_range_reflect f c]
  have htail : (∑ i ∈ Finset.range (N-c), f (c+(i+1))) =
      ∑ i ∈ Finset.range (N-c), f (c+1+i) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega
  rw [htail]
  ring


/-- Exact sign-aware split of the centered finite difference for two odd
stencil orders. Both source-side sums are retained. -/
theorem centered_odd_split (r s q : ℕ) :
    let m := 2*r+1
    let n := 2*s+1
    let N := m+n+2
    let c := n+1
    let p := 2*q+2
    (∑ k ∈ Finset.range (N+1), (-1:ℂ)^k*(N.choose k:ℂ)*((k:ℂ)-(c:ℂ))^p) =
      -(∑ i ∈ Finset.range (m+1), (-1:ℂ)^i*(N.choose (n+i+2):ℂ)*((i:ℂ)+1)^p) -
      ∑ j ∈ Finset.range (n+1), (-1:ℂ)^j*(N.choose (m+j+2):ℂ)*((j:ℂ)+1)^p := by
  dsimp only
  let m := 2*r+1
  let n := 2*s+1
  let N := m+n+2
  let c := n+1
  let p := 2*q+2
  let f : ℕ → ℂ := fun k => (-1:ℂ)^k*(N.choose k:ℂ)*((k:ℂ)-(c:ℂ))^p
  have hc : c≤N := by dsimp [c,N,m,n]; omega
  have hlen : N-c=m+1 := by dsimp [c,N]; omega
  have hcne : f c=0 := by
    dsimp [f,p]
    simp
  have hlower (j : ℕ) (hj : j<c) :
      f (c-1-j) = -((-1:ℂ)^j*(N.choose (m+j+2):ℂ)*((j:ℂ)+1)^p) := by
    have hjs : j≤n := by dsimp [c] at hj; omega
    have hjN : c-1-j≤N := by omega
    have hcomp : N-(c-1-j)=m+j+2 := by dsimp [c,N]; omega
    have hchoose : N.choose (c-1-j)=N.choose (m+j+2) := by
      rw [← hcomp]
      exact (Nat.choose_symm hjN).symm
    have hsign : (-1:ℂ)^(c-1-j)= -(-1:ℂ)^j := by
      change (-1:ℂ)^(2*s+1-j)= -(-1:ℂ)^j
      exact CarryOddCauchy.odd_stencil_sign s j hjs
    have hsub : (((c-1-j):ℕ):ℂ)-(c:ℂ)=-((j:ℂ)+1) := by
      have hnat : (c-1-j)+(j+1)=c := by omega
      have hh := congrArg (fun z : ℕ => (z:ℂ)) hnat
      push_cast at hh
      linear_combination hh
    have hp : (-((j:ℂ)+1))^p = ((j:ℂ)+1)^p := by
      dsimp [p]
      simp only [pow_add,pow_mul,neg_sq]
    dsimp [f]
    rw [hchoose,hsign,hsub,hp]
    ring
  have hupper (i : ℕ) :
      f (c+1+i) = -((-1:ℂ)^i*(N.choose (n+i+2):ℂ)*((i:ℂ)+1)^p) := by
    have hsign : (-1:ℂ)^(c+1+i)= -(-1:ℂ)^i := by
      have he : (-1:ℂ)^c=1 := by
        dsimp [c,n]
        simp [pow_add,pow_mul]
      rw [show c+1+i=c+(1+i) by omega,pow_add,he,one_mul,pow_add]
      norm_num
    have hsub : (((c+1+i):ℕ):ℂ)-(c:ℂ)=((i:ℂ)+1) := by push_cast; ring
    have hadd : c+1+i=n+i+2 := by dsimp [c]; omega
    dsimp [f]
    rw [hsign,hsub,hadd]
    ring
  have hs := centered_sum_split_generic N c hc f
  rw [hcne,add_zero,hlen] at hs
  have hlow : (∑ j ∈ Finset.range c, f (c-1-j)) =
      -(∑ j ∈ Finset.range (n+1), (-1:ℂ)^j*(N.choose (m+j+2):ℂ)*((j:ℂ)+1)^p) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hlower j (Finset.mem_range.mp hj)
  have hupp : (∑ i ∈ Finset.range (m+1), f (c+1+i)) =
      -(∑ i ∈ Finset.range (m+1), (-1:ℂ)^i*(N.choose (n+i+2):ℂ)*((i:ℂ)+1)^p) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact hupper i
  rw [hlow,hupp] at hs
  change _ = _ at hs
  linear_combination hs

end
end CarryCenteredStirling
