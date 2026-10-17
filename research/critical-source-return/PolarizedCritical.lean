import CriticalSource

/-! Full complex polarization of the same physical tests. The mixed parity
limit is zero; no finite-regularization crossing is discarded. -/
namespace CarryCriticalSource
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn Filter
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 250000

theorem criticalPairing_eq_projective (s t : Fin 2) (n k : ℕ) :
    criticalPairing s t n k = 2*canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis (n+1) k (criticalCoordinates s n))
      (nativeSourceProjectiveBoundaryJetSynthesis (n+1) k (criticalCoordinates t n)) := by
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,
    nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource]
  simp only [criticalPairing, criticalIncident, criticalReturned,
    radialIncidentVector_coe, radialReturnTransfer_exact,
    canonicalCompletedNativeProjectiveChiralForm, criticalInput]
  rw [← mul_assoc, mul_inv_cancel₀ (by norm_num : (2:ℂ) ≠ 0), one_mul]

theorem criticalPairing_conj (s t : Fin 2) (n k : ℕ) :
    conj (criticalPairing s t n k) = criticalPairing t s n k := by
  simp only [criticalPairing, map_sub, inner_conj_symm]

/-- The full complex self-pairing converges to the real source pivot. -/
theorem criticalPairing_self_tendsto (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) :
    Tendsto (fun k => criticalPairing s s n k) atTop
      (nhds ((2*sourceMomentSchur h s.val n : ℝ) : ℂ)) := by
  simpa only [criticalPairing_self, Function.comp_def] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp (criticalBalance_tendsto s n hA)

/-- Cross parity is retained in finite k and vanishes only by the original
polarized jet limit. No positivity assumption is needed. -/
theorem criticalPairing_even_odd_tendsto (n : ℕ) :
    Tendsto (fun k => criticalPairing 0 1 n k) atTop (nhds 0) := by
  have he : nativeSourceEvenBoundaryPhase (n+1) (criticalCoordinates 0 n) =
      fun i => (criticalCoefficients 0 n i : ℂ) := by
    change nativeSourceEvenBoundaryPhase (n+1)
      (nativeSourceBoundaryFromParity (n+1) (fun i => (criticalCoefficients 0 n i : ℂ)) 0) = _
    exact nativeSourceEvenBoundaryPhase_fromParity (n+1) _ 0
  have ho : nativeSourceOddBoundaryPhase (n+1) (criticalCoordinates 0 n) = 0 := by
    change nativeSourceOddBoundaryPhase (n+1)
      (nativeSourceBoundaryFromParity (n+1) (fun i => (criticalCoefficients 0 n i : ℂ)) 0) = _
    exact nativeSourceOddBoundaryPhase_fromParity (n+1) _ 0
  have he' : nativeSourceEvenBoundaryPhase (n+1) (criticalCoordinates 1 n) = 0 := by
    change nativeSourceEvenBoundaryPhase (n+1)
      (nativeSourceBoundaryFromParity (n+1) 0 (fun i => (criticalCoefficients 1 n i : ℂ))) = _
    exact nativeSourceEvenBoundaryPhase_fromParity (n+1) 0 _
  have ho' : nativeSourceOddBoundaryPhase (n+1) (criticalCoordinates 1 n) =
      fun i => (criticalCoefficients 1 n i : ℂ) := by
    change nativeSourceOddBoundaryPhase (n+1)
      (nativeSourceBoundaryFromParity (n+1) 0 (fun i => (criticalCoefficients 1 n i : ℂ))) = _
    exact nativeSourceOddBoundaryPhase_fromParity (n+1) 0 _
  have ht := (nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto (n+1)
    (criticalCoordinates 0 n) (criticalCoordinates 1 n)).const_mul (2 : ℂ)
  rw [he, ho, he', ho'] at ht
  simpa only [← criticalPairing_eq_projective, Pi.zero_apply, map_zero,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero] using ht

theorem criticalPairing_odd_even_tendsto (n : ℕ) :
    Tendsto (fun k => criticalPairing 1 0 n k) atTop (nhds 0) := by
  simpa only [Function.comp_def, Complex.star_def, criticalPairing_conj, map_zero] using
    continuous_star.continuousAt.tendsto.comp (criticalPairing_even_odd_tendsto n)

end
end CarryCriticalSource
