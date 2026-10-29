import PrimeCanaries
import CarrySelfAdjointOperator.CompletedNativeRadialChiralMultiplier

/-! Compare the SAME finite input coefficients in the original Cauchy carrier
and the native prime readout. The discrepancy is retained entrywise, then
transported through the original complete chiral multiplier. -/
namespace CarrySourcePrime
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

def primeColumnKernel (S : Finset Nat.Primes) (i j : ℕ) : ℝ :=
  inner ℝ (primeAnalysis S (towerBasis i)) (primeAnalysis S (towerBasis j))

/-- Difference of two independently specified physical/readout pairings. -/
def cauchyPrimeDefect (S : Finset Nat.Primes) (i j : ℕ) : ℝ :=
  (((i+j+2:ℕ):ℝ)⁻¹)-primeColumnKernel S i j

theorem prime_column_kernel_formula (S : Finset Nat.Primes) (i j : ℕ) :
    primeColumnKernel S i j=∑ p∈S, ((p:ℝ)/((p:ℝ)-1))*
      nativeUnitMassTowerProfile (p:ℕ) 1 i*nativeUnitMassTowerProfile (p:ℕ) 1 j := by
  simp only [primeColumnKernel,prime_analysis_pairing,tower_basis_profile]

theorem cauchy_prime_pairing_split (S : Finset Nat.Primes) (i j : ℕ) :
    inner ℂ (completedNativeChiralCauchyFeature i) (completedNativeChiralCauchyFeature j)=
      (primeColumnKernel S i j:ℂ)+(cauchyPrimeDefect S i j:ℂ) := by
  rw [inner_completedNativeChiralCauchyFeature]
  unfold cauchyPrimeDefect
  push_cast
  ring

/-- All addresses and all ordered crosses; the ORIGINAL quotient, including
completion, multiplies both the prime part and its exact signed defect. -/
theorem complete_chiral_kernel_prime_split (S : Finset Nat.Primes) (k N : ℕ)
    (i j : Fin N) :
    canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N i j=
      (((k:ℝ)+1)*primeColumnKernel S i.val j.val:ℝ)*
        (1-conj (completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k i))*
          completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j))+
      (((k:ℝ)+1)*cauchyPrimeDefect S i.val j.val:ℝ)*
        (1-conj (completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k i))*
          completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)) := by
  rw [canonicalCompletedNativeRadialChiralMultiplierDefectMatrix_apply]
  unfold cauchyPrimeDefect
  push_cast
  ring

theorem prime_column_zero_row (S : Finset Nat.Primes) (j : ℕ) :
    primeColumnKernel S 0 j=0 := by
  simp only [primeColumnKernel,prime_analysis_zero_level,inner_zero_left]

theorem cauchy_prime_defect_center (S : Finset Nat.Primes) :
    cauchyPrimeDefect S 0 0=1/2 := by
  norm_num [cauchyPrimeDefect,prime_column_zero_row]

/-- This literal finite Mellin/prime port is not contractive for the original
Cauchy metric. The coefficient-space contraction bound uses another domain. -/
theorem cauchy_prime_defect_negative : cauchyPrimeDefect {primeTwo} 1 1= -1/4 := by
  unfold cauchyPrimeDefect primeColumnKernel
  rw [two_level_active_gram.1]
  norm_num

/-- There is no positive orthogonal-loss channel with these exact readouts
and these two fixed metrics, even on the first nonconstant source column. -/
theorem no_cauchy_prime_positive_loss (E : Type*) [NormedAddCommGroup E]
    (D : E) :
    ¬ (1/4:ℝ)=primeColumnKernel {primeTwo} 1 1+‖D‖^2 := by
  have hg : primeColumnKernel {primeTwo} 1 1=1/2 := two_level_active_gram.1
  rw [hg]
  nlinarith [sq_nonneg ‖D‖]

/-- The preceding no-go expressed in the actual original physical norm. -/
theorem no_original_cauchy_positive_loss (E : Type*) [NormedAddCommGroup E]
    (D : E) :
    ¬ ‖completedNativeChiralCauchyFeature 1‖^2=
      primeColumnKernel {primeTwo} 1 1+‖D‖^2 := by
  have hn : ‖completedNativeChiralCauchyFeature 1‖^2=(1/4:ℝ) := by
    rw [norm_sq_eq_re_inner (𝕜:=ℂ),inner_completedNativeChiralCauchyFeature]
    norm_num
  rw [hn]
  exact no_cauchy_prime_positive_loss E D

/-- The first native radial source is entirely in the retained defect of
this particular readout. No finite/infinite prime atlas can recover it alone. -/
theorem complete_chiral_first_source_defect (S : Finset Nat.Primes) (k : ℕ) :
    canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k 1 0 0=
      (((k:ℝ)+1)*cauchyPrimeDefect S 0 0:ℝ)*
        (1-conj (completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k 0))*
          completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k 0)) := by
  rw [complete_chiral_kernel_prime_split S]
  norm_num [prime_column_zero_row]

end
end CarrySourcePrime
