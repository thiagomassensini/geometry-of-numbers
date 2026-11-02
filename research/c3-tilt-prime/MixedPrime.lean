import MixedTail

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem center_log_eq_prime_depth (k : ℕ) :
    Real.log (canonicalRealCpCenter k) = primeDepthLogLedger (3*(k+1)) := by
  have hn : 3*(k+1) ≠ 0 := by omega
  rw [primeDepthLogLedger_eq_log hn]
  congr 1
  simp [canonicalRealCpCenter,Nat.cast_mul]

def primeDepthMixedTiltTerm (n k : ℕ) : ℝ :=
  (canonicalRealCpCenter k ^ (-(1/2:ℝ)) *
    carryTiltThreeFirstSensitivity (canonicalRealCpCenter k)) *
      (primeDepthLogLedger (3*(k+1)))^(2*n)

theorem mixedTiltTerm_eq_primeDepth (n k : ℕ) :
    mixedTiltTerm n k = primeDepthMixedTiltTerm n k := by
  unfold mixedTiltTerm primeDepthMixedTiltTerm
  rw [center_log_eq_prime_depth]

theorem primeDepthMixedTiltTerm_summable (n : ℕ) : Summable (primeDepthMixedTiltTerm n) := by
  have h : mixedTiltTerm n = primeDepthMixedTiltTerm n := by
    funext k
    exact mixedTiltTerm_eq_primeDepth n k
  rw [← h]
  exact mixedTiltTerm_summable n

theorem primeDepthMixedTiltTerm_tsum_pos (n : ℕ) : 0 < ∑' k : ℕ, primeDepthMixedTiltTerm n k := by
  have h : mixedTiltTerm n = primeDepthMixedTiltTerm n := by
    funext k
    exact mixedTiltTerm_eq_primeDepth n k
  rw [← h]
  exact mixedTiltTerm_tsum_pos n

theorem finite_mixed_prime_depth_tendsto_positive (n : ℕ) :
    Tendsto (fun M : ℕ => ((-1:ℂ)^n * iteratedDeriv (2*n) (fun t : ℝ =>
      deriv (fun d : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t)) 0) 0).re)
      atTop (nhds (∑' k : ℕ, primeDepthMixedTiltTerm n k)) := by
  have h : mixedTiltTerm n = primeDepthMixedTiltTerm n := by
    funext k
    exact mixedTiltTerm_eq_primeDepth n k
  rw [← h]
  exact finite_mixed_tilt_tendsto_positive n

#print axioms center_log_eq_prime_depth
#print axioms primeDepthMixedTiltTerm_summable
#print axioms primeDepthMixedTiltTerm_tsum_pos
#print axioms finite_mixed_prime_depth_tendsto_positive
end
end CarryTiltSlice
