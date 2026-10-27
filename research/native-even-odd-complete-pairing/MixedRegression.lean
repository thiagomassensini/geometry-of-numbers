import JointEnergy
import Cancellation

namespace CarryMixedParity
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

def firstMixedPair (k : ℕ) : ℂ := signedPair k (radialJetCoefficients k 0) (radialJetCoefficients k 1)

/-- Smallest off-diagonal test in the SAME two original physical sources. -/
theorem first_mixed_exact :
    ∀ᶠ k : ℕ in atTop, firstMixedPair k=Complex.I*((k:ℂ)+1)^2*
      (2*responseReadout (radialStep k)-responseReadout (2*(radialStep k:ℂ)))/3 := by
  have he : nativeEvenProfile 0=triple 1 0 0 := by
    rw [native_profile_zero]
    simp [seedInput, triple]
  have ho : nativeOddProfile 0=triple Complex.I (-Complex.I) 0 := by
    rw [odd_profile_zero]
    simp [triple]
  filter_upwards [mixed_pair_exact {0} {0} (fun _ => 1) (fun _ => 1)] with k hk
  norm_num only [mixedPair, finiteJetSource, finiteOddJetSource, Finset.sum_singleton,
    Nat.mul_zero, zero_add, one_smul] at hk
  rw [radial_even_calibration k 0, radial_odd_calibration k 0] at hk
  norm_num only [Nat.mul_zero, zero_add, pow_zero, pow_one, one_smul] at hk
  norm_num at hk
  rw [he,ho] at hk
  simp only [kernel_smul_left, kernel_smul_right, map_add, map_natCast, map_one] at hk
  unfold kernel at hk
  rw [full_kernel_triple, full_kernel_triple] at hk
  norm_num [responseSamples] at hk
  unfold firstMixedPair
  rw [radial_even_calibration k 0, radial_odd_calibration k 0]
  norm_num only [Nat.mul_zero, zero_add, pow_zero, pow_one, one_smul]
  rw [he,ho]
  linear_combination hk

/-- The original analytic remainder is retained at BOTH sampled addresses. -/
def firstMixedError (z : ℂ) : ℂ :=
  (Complex.I/3)*(2*nativeRemainder 2 z-32*nativeRemainder 2 (2*z))

theorem first_mixed_error_continuous : ContinuousAt firstMixedError 0 := by
  have hR := (native_remainder_analytic 2).continuousAt
  have h2 : ContinuousAt (fun z : ℂ => nativeRemainder 2 (2*z)) 0 := by
    exact hR.comp_of_eq (show ContinuousAt (fun z : ℂ => 2*z) 0 by fun_prop) (by simp)
  unfold firstMixedError
  exact continuousAt_const.mul ((continuousAt_const.mul hR).sub (continuousAt_const.mul h2))

theorem first_mixed_scaled_expansion :
    ∀ᶠ k : ℕ in atTop, ((k:ℂ)+1)*firstMixedPair k=2*Complex.I*(h 1:ℂ)+
      (radialStep k:ℂ)^2*firstMixedError (radialStep k) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have h2t : Tendsto (fun k : ℕ => 2*(radialStep k:ℂ)) atTop (nhds 0) := by
    simpa using ht.const_mul 2
  have hp (z : ℂ) : oddTaylor 2 z=(h 0:ℂ)*z-(h 1:ℂ)*z^3 := by
    norm_num [oddTaylor, Finset.sum_range_succ]
    ring
  filter_upwards [first_mixed_exact, ht.eventually (native_response_expansion 2),
    h2t.eventually (native_response_expansion 2)] with k hk hq1 hq2
  rw [hp] at hq1 hq2
  rw [hk, hq1, hq2]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  have hi3 := congrArg (fun z : ℂ => z^3) hi
  simp only [mul_pow, one_pow] at hi3
  unfold firstMixedError
  norm_num only [show 2*2+1=5 by decide]
  linear_combination (2*Complex.I*(h 1:ℂ)+(radialStep k:ℂ)^2*
    ((Complex.I/3)*(2*nativeRemainder 2 (radialStep k)-
      32*nativeRemainder 2 (2*(radialStep k:ℂ)))))*hi3

/-- The imaginary information has a nontrivial first radial coefficient;
no finite positivity certificate is used to compute it. -/
theorem first_mixed_scaled_tendsto :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*firstMixedPair k) atTop (nhds (2*Complex.I*(h 1:ℂ))) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have he := first_mixed_error_continuous.tendsto.comp ht
  have hl := (tendsto_const_nhds (x := 2*Complex.I*(h 1:ℂ))).add ((ht.pow 2).mul he)
  simp only [zero_pow (by decide : 2≠0), zero_mul, add_zero] at hl
  apply hl.congr'
  filter_upwards [first_mixed_scaled_expansion] with k hk
  exact hk.symm

/-- Conditional separation control: complete complex orthogonality would
force the ORIGINAL first shifted moment to vanish. It is not assumed. -/
theorem complex_orthogonality_would_force_h1_zero
    (hz : ∀ᶠ k : ℕ in atTop, firstMixedPair k=0) : h 1=0 := by
  have hzero : Tendsto (fun k : ℕ => ((k:ℂ)+1)*firstMixedPair k) atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hz] with k hk
    simp [hk]
  have he := tendsto_nhds_unique first_mixed_scaled_tendsto hzero
  have hh : (h 1:ℂ)=0 := by
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  exact_mod_cast hh

end
end CarryMixedParity
