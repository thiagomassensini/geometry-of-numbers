import BinomialInverse

namespace CarryNativeBinomial
open CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The original signed stencil recovers every address, not just its norm. -/
theorem binomial_stencil_exact (N : ℕ) (x : Fin N → ℂ) (r : Fin N) :
    (∑ m : Fin N, completedGreenForwardWeight m r *
      (∑ s : Fin N, (Nat.choose s m:ℂ)*x s))=x r := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have hk (s : Fin N) :
      (∑ m : Fin N, completedGreenForwardWeight m r*(Nat.choose s m:ℂ))=
        if r=s then 1 else 0 := by
    simp only [completedGreenForwardWeight, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      (-1:ℂ)^(j-(r:ℕ))*(Nat.choose j (r:ℕ):ℂ)*(Nat.choose (s:ℕ) j:ℂ))]
    simpa only [Fin.val_inj] using inverse_binomial_kernel N r s r.isLt s.isLt
  simp_rw [hk]
  simp

/-- Explicit Newton coefficients in every existing finite even/odd jet chart.
The phase, factorial and imaginary step are the native ones. -/
def newtonCoordinates (n k : ℕ) (x : Fin (2*n) → ℂ) (m : Fin (2*n)) : ℂ :=
  nativeSourceJetOrderPhase m * ((m:ℕ).factorial:ℂ) *
    canonicalCompletedC3RadialSecondStep k^(m:ℕ) *
      ∑ r : Fin (2*n), (Nat.choose (r:ℕ) (m:ℕ):ℂ)*x r

theorem native_phase_self_inverse (m : ℕ) :
    nativeSourceJetOrderPhase m*nativeSourceJetOrderPhase m=1 := by
  simp only [nativeSourceJetOrderPhase, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one]
  rw [← mul_pow]
  norm_num

/-- Exact cancellation of the existing factorial/step factors at a single
coefficient; the projective amplitude occurs once. -/
theorem newton_input_term (n k : ℕ) (x : Fin (2*n) → ℂ) (r m : Fin (2*n)) :
    nativeSourceChiralJetInputMatrix n k r m*newtonCoordinates n k x m=
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k r)*
        (completedGreenForwardWeight m r *
          ∑ s : Fin (2*n), (Nat.choose (s:ℕ) (m:ℕ):ℂ)*x s) := by
  have hf : ((m:ℕ).factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd := canonicalCompletedC3RadialSecondStep_ne_zero k
  have hp := native_phase_self_inverse m
  unfold nativeSourceChiralJetInputMatrix newtonCoordinates
  field_simp [hf, hd]
  linear_combination
    completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k r)*
      completedGreenForwardWeight m r *
      (∑ s : Fin (2*n), (Nat.choose (s:ℕ) (m:ℕ):ℂ)*x s) *
      hp

/-- All finite orders: the explicit formula recovers the ORIGINAL amplitude-
weighted source. No regularity, moment or sign assumption is used. -/
theorem newton_input_exact (n k : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceChiralJetInput n k (newtonCoordinates n k x)=
      fun r : Fin (2*n) => completedNativeNormalizedPositiveChiralAmplitude
        (canonicalCompletedC3RadialTiltPoint k r)*x r := by
  funext r
  change (∑ m : Fin (2*n), nativeSourceChiralJetInputMatrix n k r m*
    newtonCoordinates n k x m)=_
  simp_rw [newton_input_term]
  rw [← Finset.mul_sum, binomial_stencil_exact]

end
end CarryNativeBinomial
