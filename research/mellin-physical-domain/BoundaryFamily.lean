import MellinPrimeReadout

/-! A finite-source family in the ORIGINAL Cauchy carrier. No moment, zero,
height or target Gram is an input. The desingularized boundary trace is zero. -/
namespace CarryMellinDomain
open CarrySourcePrime CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Coefficients of u(1-u)^n in the original half-density source. -/
def boundaryCoefficients (n : ℕ) : Fin (n+2) → ℝ :=
  Fin.cases 0 (fun j : Fin (n+1) => (-1:ℝ)^j.val*(n.choose j.val:ℝ))

def boundaryContinuous (n : ℕ) : C(unitInterval,ℂ) :=
  originalContinuousSynthesis (boundaryCoefficients n)

def concentratingCoefficients (n : ℕ) (j : Fin (n+2)) : ℝ :=
  ((n:ℝ)+1)*boundaryCoefficients n j

def concentratingContinuous (n : ℕ) : C(unitInterval,ℂ) :=
  originalContinuousSynthesis (concentratingCoefficients n)

def physicalConcentration (n : ℕ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  ContinuousMap.toLp 2 MeasureTheory.volume ℂ (concentratingContinuous n)

theorem boundary_trace_zero (n : ℕ) : boundaryCoefficients n 0=0 := rfl

theorem concentrating_trace_zero (n : ℕ) : concentratingCoefficients n 0=0 := by
  simp [concentratingCoefficients,boundary_trace_zero]

/-- All original stencil terms are synthesized before the scalar polynomial. -/
theorem boundary_tail_polynomial (n : ℕ) (u : ℝ) :
    mellinTailPolynomial (boundaryCoefficients n) u=(1-u)^n := by
  unfold mellinTailPolynomial boundaryCoefficients
  simp only [Fin.cases_succ]
  rw [show 1-u=(-u)+1 by ring,add_pow]
  change (∑ j : Fin (n+1), (fun r : ℕ => (-1:ℝ)^r*(n.choose r:ℝ)*u^r) j.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => (-1:ℝ)^r*(n.choose r:ℝ)*u^r) (n+1)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_pow,mul_one]
  rw [show -u=(-1:ℝ)*u by ring,mul_pow]
  ring

theorem boundary_source_original (n : ℕ) (u : unitInterval) :
    boundaryContinuous n u=((Real.sqrt (u:ℝ)*(u:ℝ)*(1-(u:ℝ))^n:ℝ):ℂ) := by
  rw [boundaryContinuous,original_continuous_with_trace,boundary_trace_zero,boundary_tail_polynomial]
  push_cast
  ring

theorem concentrating_source_original (n : ℕ) (u : unitInterval) :
    concentratingContinuous n u=
      ((((n:ℝ)+1)*Real.sqrt (u:ℝ)*(u:ℝ)*(1-(u:ℝ))^n:ℝ):ℂ) := by
  have hs : concentratingContinuous n=(((n:ℝ)+1):ℂ) • boundaryContinuous n := by
    simp only [concentratingContinuous,concentratingCoefficients,boundaryContinuous,
      originalContinuousSynthesis,Finset.smul_sum,smul_smul,Complex.ofReal_mul]
    push_cast
    rfl
  rw [hs,ContinuousMap.smul_apply,boundary_source_original]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- The actual physical L2 vector is still a finite sum of original columns. -/
theorem physical_concentration_original (n : ℕ) :
    physicalConcentration n=∑ j : Fin (n+2),
      (concentratingCoefficients n j:ℂ) • completedNativeChiralCauchyFeature j.val := by
  exact original_continuous_toLp (concentratingCoefficients n)

theorem concentrating_tail_polynomial (n : ℕ) (u : ℝ) :
    mellinTailPolynomial (concentratingCoefficients n) u=((n:ℝ)+1)*(1-u)^n := by
  unfold mellinTailPolynomial concentratingCoefficients
  have h := boundary_tail_polynomial n u
  unfold mellinTailPolynomial at h
  rw [← h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end CarryMellinDomain
