import TransverseSwap

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem infinite_tilt_mixed_prime_identity (n : ℕ) :
    ((-1:ℂ)^n * iteratedDeriv (2*n)
      (fun t : ℝ => deriv (infiniteTransverseTilt t) 0) 0).re =
        ∑' k : ℕ, primeDepthMixedTiltTerm n k := by
  have hf : (fun t : ℝ => deriv (infiniteTransverseTilt t) 0) =
      (fun t : ℝ => infiniteMixedTiltResponse (t:ℂ)) := by
    funext t
    exact (hasDerivAt_infiniteTransverseTilt t).deriv
  rw [hf]
  exact infinite_mixed_prime_depth_identity n

theorem infinite_tilt_mixed_positive (n : ℕ) :
    0 < ((-1:ℂ)^n * iteratedDeriv (2*n)
      (fun t : ℝ => deriv (infiniteTransverseTilt t) 0) 0).re := by
  rw [infinite_tilt_mixed_prime_identity]
  exact primeDepthMixedTiltTerm_tsum_pos n

theorem finite_jets_tendsto_infinite_mixed (n : ℕ) :
    Tendsto (fun M : ℕ => ((-1:ℂ)^n * iteratedDeriv (2*n) (fun t : ℝ =>
      deriv (fun d : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t)) 0) 0).re)
      atTop (𝓝 (((-1:ℂ)^n * iteratedDeriv (2*n)
        (fun t : ℝ => deriv (infiniteTransverseTilt t) 0) 0).re)) := by
  rw [infinite_tilt_mixed_prime_identity]
  exact finite_mixed_prime_depth_tendsto_positive n

#print axioms infinite_tilt_mixed_prime_identity
#print axioms infinite_tilt_mixed_positive
#print axioms finite_jets_tendsto_infinite_mixed
end
end CarryTiltSlice
