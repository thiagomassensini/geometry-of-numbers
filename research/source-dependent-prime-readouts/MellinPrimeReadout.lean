import PrimeCanaries
import CarrySelfAdjointOperator.CompletedNativeRadialChiralMultiplier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Finite Mellin readout of the ORIGINAL half-density monomials.
The zero-level trace is kept separately. No bounded map on the full physical
L2 carrier, isometry, or equality with the signed Green form is asserted. -/
namespace CarrySourcePrime
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

/-- The literal finite half-density source, before either real quadrature is read. -/
def originalContinuousSynthesis {N : ℕ} (c : Fin (N+1) → ℝ) : C(unitInterval,ℂ) :=
  ∑ j, (c j:ℂ) • completedNativeChiralCauchyContinuousFeature j.val

/-- Only the positive levels enter the Mellin integrand; c0 remains a trace. -/
def mellinTailPolynomial {N : ℕ} (c : Fin (N+1) → ℝ) (u : ℝ) : ℝ :=
  ∑ j : Fin N, c j.succ*u^j.val

/-- Coordinate bookkeeping in the existing native tower; not an isometry. -/
def finiteTowerSynthesis {N : ℕ} (c : Fin (N+1) → ℝ) : NativeGpreTowerHilbert :=
  ∑ j, c j • towerBasis j.val

theorem finite_polynomial_with_trace {N : ℕ} (c : Fin (N+1) → ℝ) (u : ℝ) :
    (∑ j : Fin (N+1), c j*u^j.val)=c 0+u*mellinTailPolynomial c u := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,mellinTailPolynomial,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

/-- The SAME continuous state reconstructs with its boundary trace present. -/
theorem original_continuous_with_trace {N : ℕ} (c : Fin (N+1) → ℝ) (u : unitInterval) :
    originalContinuousSynthesis c u=
      ((Real.sqrt (u:ℝ)*(c 0+(u:ℝ)*mellinTailPolynomial c u):ℝ):ℂ) := by
  rw [← finite_polynomial_with_trace]
  simp only [originalContinuousSynthesis,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    completedNativeChiralCauchyContinuousFeature,ContinuousMap.coe_mk,smul_eq_mul]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The raw half-density value at the boundary is zero; c0 is its separately
retained desingularized trace, not this raw value. -/
theorem original_continuous_zero {N : ℕ} (c : Fin (N+1) → ℝ) :
    originalContinuousSynthesis c 0=0 := by
  rw [original_continuous_with_trace]
  norm_num

/-- On the positive interval the readout is recovered from the completed
finite vector synthesis, with its boundary trace explicitly subtracted. -/
theorem mellin_tail_from_original_source {N : ℕ} (c : Fin (N+1) → ℝ)
    (u : unitInterval) (hu : 0<(u:ℝ)) :
    (mellinTailPolynomial c u:ℂ)=
      (originalContinuousSynthesis c u/(Real.sqrt (u:ℝ):ℂ)-(c 0:ℂ))/(u:ℂ) := by
  rw [original_continuous_with_trace]
  push_cast
  have hu0 : (u:ℂ)≠0 := by exact_mod_cast (ne_of_gt hu)
  have hs0 : (Real.sqrt (u:ℝ):ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hu))
  field_simp [hu0,hs0]
  ring

/-- Passage to L2 is applied AFTER the original finite vector synthesis. -/
theorem original_continuous_toLp {N : ℕ} (c : Fin (N+1) → ℝ) :
    ContinuousMap.toLp 2 MeasureTheory.volume ℂ (originalContinuousSynthesis c)=
      ∑ j, (c j:ℂ) • completedNativeChiralCauchyFeature j.val := by
  simp only [originalContinuousSynthesis,map_sum,map_smul,completedNativeChiralCauchyFeature]

/-- Exact integral of the positive-level polynomial, with no source estimates. -/
theorem mellin_tail_integral {N : ℕ} (c : Fin (N+1) → ℝ) (p : ℕ) :
    (∫ u in (0:ℝ)..(p:ℝ)⁻¹, mellinTailPolynomial c u)=
      ∑ j : Fin (N+1), c j*nativeUnitMassTowerProfile p 1 j.val := by
  unfold mellinTailPolynomial
  rw [intervalIntegral.integral_finsetSum]
  · rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,nativeUnitMassTowerProfile_zero_level,mul_zero,zero_add]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul,integral_pow]
    simp only [Fin.val_succ,nativeUnitMassTowerProfile,Nat.succ_ne_zero,if_false,Nat.mul_one,
      Nat.cast_add,Nat.cast_one,zero_pow (show j.val+1≠0 by omega),sub_zero,inv_pow]
  · intro j _
    exact (Continuous.const_mul (continuous_pow j.val) (c j.succ)).intervalIntegrable _ _

/-- This integral is the EXISTING input-dependent profile readout. -/
theorem mellin_integral_native_profile {N : ℕ} (c : Fin (N+1) → ℝ) (p : ℕ) :
    (∫ u in (0:ℝ)..(p:ℝ)⁻¹, mellinTailPolynomial c u)=
      inner ℝ (nativeGpreTowerProfileVector p 1) (finiteTowerSynthesis c) := by
  rw [mellin_tail_integral]
  simp only [finiteTowerSynthesis,inner_sum,real_inner_smul_right,tower_basis_profile]

/-- The same finite integral gives an active prime observation after T. -/
theorem mellin_integral_prime_readout {N : ℕ} (c : Fin (N+1) → ℝ) (p : Nat.Primes) :
    (∫ u in (0:ℝ)..(p:ℝ)⁻¹, mellinTailPolynomial c u)=
      primeReadout p (RealFirstNative.primeContractionLinear (finiteTowerSynthesis c)) := by
  rw [prime_contraction_readout_original,mellin_integral_native_profile]

/-- Complex coefficients remain in the original continuous carrier. -/
def originalComplexContinuousSynthesis {N : ℕ} (c : Fin (N+1) → ℂ) : C(unitInterval,ℂ) :=
  ∑ j, c j • completedNativeChiralCauchyContinuousFeature j.val

/-- Both real quadratures reconstruct the complex vector, before readout. -/
theorem original_complex_two_quadratures {N : ℕ} (c : Fin (N+1) → ℂ) :
    originalComplexContinuousSynthesis c=
      originalContinuousSynthesis (fun j => (c j).re)+
      Complex.I • originalContinuousSynthesis (fun j => (c j).im) := by
  ext u
  simp only [originalComplexContinuousSynthesis,originalContinuousSynthesis,
    ContinuousMap.sum_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hc : ((c j).re:ℂ)+Complex.I*((c j).im:ℂ)=c j := by
    simpa only [mul_comm] using Complex.re_add_im (c j)
  linear_combination -(completedNativeChiralCauchyContinuousFeature j.val u)*hc

theorem original_complex_with_trace {N : ℕ} (c : Fin (N+1) → ℂ) (u : unitInterval) :
    originalComplexContinuousSynthesis c u=
      (Real.sqrt (u:ℝ):ℂ)*(c 0+(u:ℂ)*
        ((mellinTailPolynomial (fun j => (c j).re) u:ℂ)+
          Complex.I*(mellinTailPolynomial (fun j => (c j).im) u:ℂ))) := by
  rw [original_complex_two_quadratures]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,
    original_continuous_with_trace]
  push_cast
  have hc : ((c 0).re:ℂ)+Complex.I*((c 0).im:ℂ)=c 0 := by
    simpa only [mul_comm] using Complex.re_add_im (c 0)
  linear_combination (Real.sqrt (u:ℝ):ℂ)*hc

theorem original_complex_toLp {N : ℕ} (c : Fin (N+1) → ℂ) :
    ContinuousMap.toLp 2 MeasureTheory.volume ℂ (originalComplexContinuousSynthesis c)=
      ∑ j, c j • completedNativeChiralCauchyFeature j.val := by
  simp only [originalComplexContinuousSynthesis,map_sum,map_smul,completedNativeChiralCauchyFeature]

end
end CarrySourcePrime
