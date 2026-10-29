import DifferencePowers
import StirlingBoundary

namespace CarryCenteredStirling
open CarrySpatialCorrection
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def centeredDifference (N p : ℕ) (c : ℂ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * (fwdDiff (1:ℕ))^[N] (fun j : ℕ => ((j:ℂ)-c)^p) 0

/-- Explicit centered signed-binomial sum. -/
theorem centered_difference_sum (N p : ℕ) (c : ℂ) :
    centeredDifference N p c = (N.factorial:ℂ)⁻¹ *
      ∑ j ∈ Finset.range (N+1),
        (((-1:ℤ)^(N-j)*(N.choose j:ℤ):ℤ):ℂ)*((j:ℂ)-c)^p := by
  unfold centeredDifference
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Nat.cast_id, zero_add]

/-- Centered differences are a finite Stirling sum, obtained from the
existing normalized physical-binomial forward difference theorem. -/
theorem centered_difference_stirling (N p : ℕ) (c : ℂ) :
    centeredDifference N p c =
      ∑ r ∈ Finset.range (p+1),
        (p.choose r:ℂ)*(-(c+1))^(p-r)*(Nat.stirlingSecond (r+1) (N+1):ℂ) := by
  let f : ℕ → ℂ := fun k => ((k:ℂ)-(c+1))^p
  have hf : (fun j : ℕ => ((j:ℂ)-c)^p) = fun j => f (j+1) := by
    funext j
    dsimp [f]
    push_cast
    congr 1
    ring
  have hs := fwdDiff_iter_comp_add (1:ℕ) f 1 N 0
  unfold centeredDifference
  rw [hf, hs]
  simp only [zero_add]
  have he : f = ∑ r ∈ Finset.range (p+1),
      ((p.choose r:ℂ)*(-(c+1))^(p-r)) • (fun k : ℕ => (k:ℂ)^r) := by
    funext k
    dsimp [f]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sub_eq_add_neg,add_pow]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he]
  simp only [fwdDiff_iter_finsetSum, fwdDiff_iter_const_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hd := difference_power_stirling N r
  unfold differencePower at hd
  rw [← hd]
  ring


/-- Only three Stirling layers survive at the first nontrivial correction. -/
theorem centered_difference_two_above (N : ℕ) (c : ℂ) :
    centeredDifference N (N+2) c =
      ((N+2).choose N:ℂ)*(-(c+1))^2 +
      ((N+2).choose (N+1):ℂ)*(-(c+1))*
        (Nat.stirlingSecond (N+2) (N+1):ℂ) +
      (Nat.stirlingSecond (N+3) (N+1):ℂ) := by
  rw [centered_difference_stirling]
  rw [show N+2+1=N+3 by omega, Finset.sum_range_add _ N 3]
  have hz : (∑ r ∈ Finset.range N,
      ((N+2).choose r:ℂ)*(-(c+1))^(N+2-r)*
        (Nat.stirlingSecond (r+1) (N+1):ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hl : r<N := Finset.mem_range.mp hr
    rw [Nat.stirlingSecond_eq_zero_of_lt (show r+1<N+1 by omega)]
    simp
  rw [hz]
  simp only [zero_add,Finset.sum_range_succ,Finset.sum_range_zero]
  simp only [add_zero,Nat.add_sub_cancel_left,
    Nat.stirlingSecond_self,Nat.cast_one,mul_one,Nat.choose_self]
  push_cast
  ring_nf
  simp only [Nat.add_comm 1 N,Nat.add_sub_cancel_left,Nat.sub_self,pow_one,pow_zero]
  ring


/-- Closed form of the two-above centered difference. -/
theorem centered_difference_two_above_closed (N : ℕ) (c : ℂ) :
    centeredDifference N (N+2) c =
      (((N:ℂ)+2)*((N:ℂ)+1)/2)*(c+1)^2 -
        ((N:ℂ)+2)*(c+1)*(((N:ℂ)+2)*((N:ℂ)+1)/2) +
        ((N:ℂ)+1)*((N:ℂ)+2)*((N:ℂ)+3)*(3*(N:ℂ)+4)/24 := by
  rw [centered_difference_two_above]
  have hc : (N+2).choose N=(N+2).choose 2 := by
    have hx : N+2-2=N := by omega
    simpa only [hx] using
      (Nat.choose_symm (n:=N+2) (k:=2) (by omega))
  have hd : (N+2).choose (N+1)=N+2 := by
    simpa only [Nat.add_assoc] using Nat.choose_succ_self_right (N+1)
  rw [hc,hd,Nat.stirlingSecond_succ_self_left,stirling_two_above,
    Nat.cast_choose_two]
  unfold curvature
  push_cast
  ring

/-- The centered all-order difference has exactly the proposed Lambda
coefficient. This still requires the separate Cauchy sum-centering identity
before it can be identified with the original full double stencil. -/
theorem centered_correction_eq_lambda (m n : ℕ) :
    centeredDifference (m+n+2) (m+n+4) ((n:ℂ)+1) =
      ((m:ℂ)+1)*((m:ℂ)+2)*(2*(m:ℂ)+3)/12 +
      ((n:ℂ)+1)*((n:ℂ)+2)*(2*(n:ℂ)+3)/12 +
      ((((m:ℂ)+1)*((m:ℂ)+2)/2)-(((n:ℂ)+1)*((n:ℂ)+2)/2))^2/2 := by
  have he := centered_difference_two_above_closed (m+n+2) ((n:ℂ)+1)
  push_cast at he
  convert he using 1
  ring

end
end CarryCenteredStirling
