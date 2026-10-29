import ComplementRows

namespace CarryOddCauchy
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- REAL coefficients extracted from the original odd stencil, not new inputs. -/
def nativeOddBeta (r j : ℕ) : ℝ :=
  (-1:ℝ)^(r+j)*(Nat.choose (2*r+1) j:ℝ)/((2*r+1).factorial:ℝ)

theorem odd_exponent_sign (r : ℕ) : (-1:ℂ)^(2*r+1)= -1 := by
  rw [pow_succ,pow_mul]
  norm_num

theorem odd_stencil_sign (r j : ℕ) (hj : j≤2*r+1) :
    (-1:ℂ)^(2*r+1-j)= -(-1:ℂ)^j := by
  have hp : (-1:ℂ)^(2*r+1-j)=(-1:ℂ)^(j+1) :=
    neg_one_pow_congr (by rw [Nat.even_iff,Nat.even_iff]; omega)
  rw [hp,pow_succ]
  ring

/-- Literal coefficient equality: includes the original factorial and phase. -/
theorem native_odd_coefficient (r j : ℕ) :
    nativeOddProfile r j=Complex.I*(nativeOddBeta r j:ℂ) := by
  by_cases hj : j≤2*r+1
  · simp only [nativeOddProfile,staticStencil,Finsupp.smul_apply,smul_eq_mul,raw_stencil_apply,
      completedGreenForwardWeight,nativeOddBeta]
    push_cast
    rw [odd_stencil_sign r j hj,pow_add]
    ring
  · have hc := Nat.choose_eq_zero_of_lt (by omega : 2*r+1<j)
    simp [nativeOddProfile,staticStencil,raw_stencil_apply,
      completedGreenForwardWeight,nativeOddBeta,hc]

/-- The WHOLE original odd source is synthesized before any pairing. -/
theorem native_odd_vector (r : ℕ) :
    physicalCauchySynthesis (nativeOddProfile r)=
      (Complex.I*(-1:ℂ)^r*((2*r+1).factorial:ℂ)⁻¹) •
        ((physicalComplement^(2*r+1)) (completedNativeChiralCauchyFeature 0)) := by
  simp only [nativeOddProfile,staticStencil,map_smul,raw_stencil_complement,smul_smul]
  rw [odd_exponent_sign]
  congr 1
  ring

/-- Requested all-order physical Cauchy formula, with BOTH indices arbitrary. -/
theorem native_odd_cauchy_row (r j : ℕ) :
    inner ℂ (completedNativeChiralCauchyFeature j) (physicalCauchySynthesis (nativeOddProfile r))=
      Complex.I*(-1:ℂ)^r*((j+1).factorial:ℂ)/((j+2*r+3).factorial:ℂ) := by
  rw [native_odd_vector,inner_smul_right]
  change (Complex.I*(-1:ℂ)^r*((2*r+1).factorial:ℂ)⁻¹)*complementRow (2*r+1) j=_
  rw [complement_row_factorial]
  have hf : ((2*r+1).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*r+1)
  rw [show j+(2*r+1)+2=j+2*r+3 by omega]
  field_simp

/-- All material coefficients, with the original finite support derived. -/
theorem native_odd_atoms (r : ℕ) :
    nativeOddProfile r=∑ j ∈ Finset.range (2*r+2), Finsupp.single j (Complex.I*(nativeOddBeta r j:ℂ)) := by
  classical
  ext n
  simp only [Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.single_apply]
  by_cases hn : n<2*r+2
  · simpa [Finset.mem_range,hn] using native_odd_coefficient r n
  · have hc : nativeOddProfile r n=0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hmem
      exact hn (Finset.mem_range.mp (odd_profile_support r hmem))
    simp [Finset.mem_range,hn,hc]

/-- Reversal is by the ORIGINAL complex conjugate inner product. -/
theorem native_odd_cauchy_reverse (r j : ℕ) :
    inner ℂ (physicalCauchySynthesis (nativeOddProfile r)) (completedNativeChiralCauchyFeature j)=
      -Complex.I*(-1:ℂ)^r*((j+1).factorial:ℂ)/((j+2*r+3).factorial:ℂ) := by
  rw [← inner_conj_symm, native_odd_cauchy_row]
  simp only [map_div₀,map_mul,map_pow,map_neg,map_one,map_natCast,Complex.conj_I]

end
end CarryOddCauchy
