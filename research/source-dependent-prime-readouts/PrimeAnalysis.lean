import PrimeProjection
import CarrySelfAdjointOperator.NativeRealComplementTransport

/-! The finite prime analysis is a restriction of the EXISTING native G_pre
prime-carry map. The input-dependent profile readouts are not fitted moments.
Its positive complementary form remains distinct from the completed Green form. -/
namespace CarrySourcePrime
open CPFormal.Analytic.Cp
open CarrySelfAdjointOperator CarrySelfAdjointOperator.RealFirstNative
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Existing native transport followed by the original finite prime projection. -/
def primeAnalysis (S : Finset Nat.Primes) :
    NativeGpreTowerHilbert →ₗ[ℝ] PrimeCarryDefectGlobalHilbert :=
  (primeProjection S).comp primeContractionLinear

/-- The original native profile is the actual readout, for every input. -/
theorem prime_contraction_readout_original (X : NativeGpreTowerHilbert) (p : Nat.Primes) :
    primeReadout p (primeContractionLinear X)=
      inner ℝ (nativeGpreTowerProfileVector (p:ℕ) 1) X :=
  inner_globalCarryAxis_nativeGprePrimeCarryDefectState X p

theorem prime_analysis_zero (S : Finset Nat.Primes) : primeAnalysis S 0=0 :=
  (primeAnalysis S).map_zero

theorem prime_analysis_apply (S : Finset Nat.Primes)
    (X : NativeGpreTowerHilbert) (p : Nat.Primes) :
    primeAnalysis S X p=if p∈S then
      inner ℝ (nativeGpreTowerProfileVector (p:ℕ) 1) X •
        primeCriticalCenteredCarryDualAxis p else 0 := by
  classical
  change primeProjection S (primeContractionLinear X) p=_
  rw [prime_projection_apply,prime_contraction_readout_original]

theorem prime_analysis_readout (S : Finset Nat.Primes)
    (X : NativeGpreTowerHilbert) (p : Nat.Primes) :
    primeReadout p (primeAnalysis S X)=if p∈S then
      inner ℝ (nativeGpreTowerProfileVector (p:ℕ) 1) X else 0 := by
  classical
  change primeReadout p (primeProjection S (primeContractionLinear X))=_
  rw [prime_readout_projection,prime_contraction_readout_original]

/-- This is coordinate restriction of the existing map, not a new source. -/
theorem prime_analysis_coordinate_mask (S : Finset Nat.Primes)
    (X : NativeGpreTowerHilbert) (p : Nat.Primes) :
    primeAnalysis S X p=if p∈S then primeContractionLinear X p else 0 := by
  classical
  rw [prime_analysis_apply]
  rfl

/-- Exact polarized ledger for source-dependent readouts in a finite atlas. -/
theorem prime_analysis_pairing (S : Finset Nat.Primes)
    (X Y : NativeGpreTowerHilbert) :
    inner ℝ (primeAnalysis S X) (primeAnalysis S Y)=
      ∑ p∈S, ((p:ℝ)/((p:ℝ)-1))*
        inner ℝ (nativeGpreTowerProfileVector (p:ℕ) 1) X*
        inner ℝ (nativeGpreTowerProfileVector (p:ℕ) 1) Y := by
  change inner ℝ (primeProjection S (primeContractionLinear X))
    (primeProjection S (primeContractionLinear Y))=_
  rw [prime_projection_projected_pairing]
  simp only [prime_contraction_readout_original]

/-- Every finite restriction retains the same uniform contraction bound. -/
theorem prime_analysis_norm_sq_le (S : Finset Nat.Primes) (X : NativeGpreTowerHilbert) :
    ‖primeAnalysis S X‖^2≤(11/12:ℝ)*‖X‖^2 := by
  exact (prime_projection_norm_sq_le S (primeContractionLinear X)).trans
    (nativeGprePrimeCarryDefectState_norm_sq_le X)

theorem prime_analysis_nested (S T : Finset Nat.Primes) (hST : S⊆T)
    (X : NativeGpreTowerHilbert) :
    primeProjection S (primeAnalysis T X)=primeAnalysis S X :=
  prime_projection_nested S T hST (primeContractionLinear X)

/-- Independent finite source coefficients, before any diagonal energy. -/
theorem prime_analysis_synthesis {N : ℕ} (S : Finset Nat.Primes)
    (U : Fin N → NativeGpreTowerHilbert) (c : Fin N → ℝ) :
    primeAnalysis S (∑ i, c i • U i)=∑ i, c i • primeAnalysis S (U i) := by
  simp only [map_sum,map_smul]

theorem prime_analysis_all_crosses {N M : ℕ} (S : Finset Nat.Primes)
    (U : Fin N → NativeGpreTowerHilbert) (V : Fin M → NativeGpreTowerHilbert)
    (c : Fin N → ℝ) (d : Fin M → ℝ) :
    inner ℝ (primeAnalysis S (∑ i,c i • U i)) (primeAnalysis S (∑ j,d j • V j))=
      ∑ i, ∑ j, c i*d j*inner ℝ (primeAnalysis S (U i)) (primeAnalysis S (V j)) := by
  rw [prime_analysis_synthesis,prime_analysis_synthesis,sum_inner]
  simp_rw [inner_sum,real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Complete native transport balance with the finite atlas tail retained. -/
theorem prime_analysis_three_term_polarization (S : Finset Nat.Primes)
    (X Y : NativeGpreTowerHilbert) :
    inner ℝ X Y=SourceKernelCalibration.complementKernel X Y+
      inner ℝ (primeAnalysis S X) (primeAnalysis S Y)+
      inner ℝ (primeContractionLinear X-primeAnalysis S X)
        (primeContractionLinear Y-primeAnalysis S Y) := by
  have h := prime_projection_polarized_pythagoras S
    (primeContractionLinear X) (primeContractionLinear Y)
  change inner ℝ X Y=(inner ℝ X Y-inner ℝ (primeContractionLinear X)
    (primeContractionLinear Y))+inner ℝ (primeProjection S (primeContractionLinear X))
    (primeProjection S (primeContractionLinear Y))+
    inner ℝ (primeContractionLinear X-primeProjection S (primeContractionLinear X))
      (primeContractionLinear Y-primeProjection S (primeContractionLinear Y))
  linarith

/-- The previous fixed-readout theorem is recovered on its legitimate affine
fiber; no affine premise is needed for the construction of primeProjection. -/
theorem prime_projection_recovers_fixed_realization
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (X : PrimeCarryDefectGlobalHilbert)
    (hX : IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn M s S X) :
    primeProjection S X=canonicalEnrichedPrimeCarryDefectProvenanceState M s S := by
  classical
  apply lp.ext
  funext p
  rw [prime_projection_apply,canonicalEnrichedPrimeCarryDefectProvenanceState_apply]
  split_ifs with hp
  · exact congrArg (fun a : ℝ => a • primeCriticalCenteredCarryDualAxis p) (hX p hp)
  · rfl

end
end CarrySourcePrime
