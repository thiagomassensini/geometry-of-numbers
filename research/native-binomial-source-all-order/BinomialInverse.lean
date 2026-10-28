import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
import Mathlib.Data.Nat.Choose.Sum

namespace CarryNativeBinomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The signed forward stencil and the unsigned binomial chart are exact
inverses at every finite cutoff. This is coefficient algebra, not a Gram. -/
theorem inverse_binomial_kernel (N r s : ℕ) (_hr : r < N) (hs : s < N) :
    (∑ m ∈ Finset.range N, ((-1:ℂ)^(m-r)*(Nat.choose m r:ℂ))*(Nat.choose s m:ℂ))=
      if r=s then 1 else 0 := by
  by_cases hsr : s < r
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : m < r
    · simp [Nat.choose_eq_zero_of_lt hm]
    · simp [Nat.choose_eq_zero_of_lt (by omega : s < m)]
  · have hrs : r ≤ s := by omega
    have htail : (∑ m ∈ Finset.range (N-(s+1)),
        ((-1:ℂ)^(s+1+m-r)*(Nat.choose (s+1+m) r:ℂ))*(Nat.choose s (s+1+m):ℂ))=0 := by
      apply Finset.sum_eq_zero
      intro m _
      simp [Nat.choose_eq_zero_of_lt (by omega : s < s+1+m)]
    rw [show N=(s+1)+(N-(s+1)) from by omega, Finset.sum_range_add, htail, add_zero]
    have hlo : (∑ m ∈ Finset.range r,
        ((-1:ℂ)^(m-r)*(Nat.choose m r:ℂ))*(Nat.choose s m:ℂ))=0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hm)]
    rw [show s+1=r+(s-r+1) from by omega, Finset.sum_range_add, hlo, zero_add]
    have hterm (j : ℕ) :
        ((-1:ℂ)^(r+j-r)*(Nat.choose (r+j) r:ℂ))*(Nat.choose s (r+j):ℂ)=
          (Nat.choose s r:ℂ)*((-1:ℂ)^j*(Nat.choose (s-r) j:ℂ)) := by
      have hc := Nat.choose_mul (n:=s) (k:=r+j) (s:=r) (by omega)
      have he : (Nat.choose (r+j) r:ℂ)*(Nat.choose s (r+j):ℂ)=
          (Nat.choose s r:ℂ)*(Nat.choose (s-r) j:ℂ) := by
        exact_mod_cast (by simpa [Nat.mul_comm] using hc)
      rw [show r+j-r=j from by omega]
      linear_combination (-1:ℂ)^j*he
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    have ha : (∑ j ∈ Finset.range (s-r+1), (-1:ℂ)^j*(Nat.choose (s-r) j:ℂ))=
        if s-r=0 then 1 else 0 := by
      exact_mod_cast (Int.alternating_sum_range_choose (n:=s-r))
    rw [ha]
    by_cases he : r=s
    · subst s
      simp
    · simp [he,show s-r≠0 from by omega]

/-- Newton's coefficient matrix, fixed by the address binomial coefficients. -/
def binomialMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun m r => (Nat.choose (r:ℕ) (m:ℕ):ℂ)

/-- The ORIGINAL signed forward weights; no metric or normalization change. -/
def signedBinomialMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun r m => CarrySelfAdjointOperator.completedGreenForwardWeight m r

theorem signed_binomial_mul (N : ℕ) :
    signedBinomialMatrix N*binomialMatrix N=1 := by
  ext r s
  simp only [Matrix.mul_apply, signedBinomialMatrix, binomialMatrix,
    CarrySelfAdjointOperator.completedGreenForwardWeight, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast, Matrix.one_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (-1:ℂ)^(j-(r:ℕ))*(Nat.choose j (r:ℕ):ℂ)*(Nat.choose (s:ℕ) j:ℂ))]
  simpa only [Fin.val_inj] using inverse_binomial_kernel N r s r.isLt s.isLt

/-- The explicit square matrices are inverse on both sides. This uses only
finite matrix algebra, never a positivity or native bijectivity theorem. -/
theorem binomial_signed_mul (N : ℕ) :
    binomialMatrix N*signedBinomialMatrix N=1 := by
  exact mul_eq_one_comm.mp (signed_binomial_mul N)

end
end CarryNativeBinomial
