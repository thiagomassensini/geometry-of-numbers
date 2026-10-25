import PrimeAnalysis

/-! Exact native G_pre inputs, not vectors reconstructed from canonical
moments. The blind zero level and the mixed first/second levels are retained. -/
namespace CarrySourcePrime
open CPFormal.Analytic.Cp CarrySelfAdjointOperator CarrySelfAdjointOperator.RealFirstNative
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false

def towerBasis (j : ℕ) : NativeGpreTowerHilbert := lp.single 2 j (1:ℝ)
def primeTwo : Nat.Primes := ⟨2,Nat.prime_two⟩

theorem tower_basis_profile (p τ j : ℕ) :
    inner ℝ (nativeGpreTowerProfileVector p τ) (towerBasis j)=nativeUnitMassTowerProfile p τ j := by
  unfold towerBasis
  rw [lp.inner_single_right]
  simp

theorem tower_basis_ne_zero (j : ℕ) : towerBasis j≠0 := by
  intro h
  have he := congrArg (fun X : NativeGpreTowerHilbert => X j) h
  simp [towerBasis,lp.single_apply] at he

/-- A genuine source direction invisible to EVERY first-time prime readout. -/
theorem prime_contraction_zero_level : primeContractionLinear (towerBasis 0)=0 := by
  apply lp.ext
  funext p
  change inner ℝ (nativeGpreTowerProfileVector (p:ℕ) 1) (towerBasis 0) •
    primeCriticalCenteredCarryDualAxis p=0
  rw [tower_basis_profile,nativeUnitMassTowerProfile_zero_level,zero_smul]

theorem prime_analysis_zero_level (S : Finset Nat.Primes) :
    primeAnalysis S (towerBasis 0)=0 := by
  change primeProjection S (primeContractionLinear (towerBasis 0))=0
  rw [prime_contraction_zero_level,prime_projection_zero]

/-- This observation map alone does not preserve all source information. -/
theorem prime_contraction_not_injective : ¬ Function.Injective primeContractionLinear := by
  intro h
  have he : towerBasis 0=0 := h (by rw [prime_contraction_zero_level,map_zero])
  exact tower_basis_ne_zero 0 he

/-- The complete existing complement keeps the otherwise invisible unit. -/
theorem zero_level_complement_energy :
    SourceKernelCalibration.complementKernel (towerBasis 0) (towerBasis 0)=1 := by
  rw [SourceKernelCalibration.complementKernel_self]
  change ‖towerBasis 0‖^2-‖primeContractionLinear (towerBasis 0)‖^2=1
  rw [prime_contraction_zero_level]
  norm_num [towerBasis]

/-- First two nonzero tower levels, same camera, including the mixed cross. -/
theorem two_level_active_gram :
    inner ℝ (primeAnalysis {primeTwo} (towerBasis 1)) (primeAnalysis {primeTwo} (towerBasis 1))=1/2 ∧
    inner ℝ (primeAnalysis {primeTwo} (towerBasis 1)) (primeAnalysis {primeTwo} (towerBasis 2))=1/8 ∧
    inner ℝ (primeAnalysis {primeTwo} (towerBasis 2)) (primeAnalysis {primeTwo} (towerBasis 2))=1/32 := by
  simp only [prime_analysis_pairing]
  norm_num [tower_basis_profile,primeTwo,nativeUnitMassTowerProfile]

end
end CarrySourcePrime
