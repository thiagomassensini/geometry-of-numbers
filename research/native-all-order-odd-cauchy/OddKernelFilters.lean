import OddCauchyRows

namespace CarryOddCauchy
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- Positive magnitude extracted from the original TWO-input Cauchy kernel. -/
def oddFilterMagnitude (r s j : ℕ) : ℝ :=
  (Nat.choose (2*s+1) j:ℝ)*((j+1).factorial:ℝ)/
    (((2*s+1).factorial:ℝ)*((j+2*r+3).factorial:ℝ))

/-- Signed coefficient; r is the LEFT profile and s the RIGHT profile. -/
def oddFilterCoefficient (r s j : ℕ) : ℝ :=
  (-1:ℝ)^r*nativeOddBeta s j*((j+1).factorial:ℝ)/((j+2*r+3).factorial:ℝ)

def oddFilter (r s : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (2*s+2), (oddFilterCoefficient r s j:ℂ)*w j

/-- Whole weighted vector, with all original coefficients and their phase. -/
theorem weighted_native_odd_vector (s : ℕ) (w : ℕ → ℂ) :
    physicalCauchySynthesis (coefficientWeight w (nativeOddProfile s))=
      ∑ j ∈ Finset.range (2*s+2), (w j*Complex.I*(nativeOddBeta s j:ℂ)) •
        completedNativeChiralCauchyFeature j := by
  rw [native_odd_atoms,weight_sum_input,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hw : coefficientWeight w (Finsupp.single j (Complex.I*(nativeOddBeta s j:ℂ)))=
      Finsupp.single j (w j*Complex.I*(nativeOddBeta s j:ℂ)) := by
    ext n
    by_cases hn : n=j
    · simp [coefficient_weight_apply,hn,mul_assoc]
    · simp [coefficient_weight_apply,Finsupp.single_eq_of_ne hn]
  rw [hw]
  simp only [physicalCauchySynthesis,Finsupp.linearCombination_single]

/-- The exact all-order SINGLE-sum filter, derived from the physical vectors.
The two input orders remain separate; no Hankel or canonical sign is assumed. -/
theorem native_odd_kernel_filter (r s : ℕ) (w : ℕ → ℂ) :
    kernel w (nativeOddProfile r) (nativeOddProfile s)=oddFilter r s w := by
  change inner ℂ (physicalCauchySynthesis (nativeOddProfile r))
    (physicalCauchySynthesis (coefficientWeight w (nativeOddProfile s)))=_
  rw [weighted_native_odd_vector]
  simp only [inner_sum,inner_smul_right,native_odd_cauchy_reverse]
  unfold oddFilter
  apply Finset.sum_congr rfl
  intro j _
  unfold oddFilterCoefficient
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- Explicit alternating sign, with the ORIGINAL factorials. -/
theorem odd_filter_coefficient_factorization (r s j : ℕ) :
    oddFilterCoefficient r s j=(-1:ℝ)^(r+s+j)*oddFilterMagnitude r s j := by
  unfold oddFilterCoefficient oddFilterMagnitude nativeOddBeta
  rw [show r+s+j=r+(s+j) by omega,pow_add]
  ring

theorem odd_filter_magnitude_pos (r s j : ℕ) (hj : j≤2*s+1) :
    0<oddFilterMagnitude r s j := by
  unfold oddFilterMagnitude
  have hc : 0<(Nat.choose (2*s+1) j:ℝ) := by exact_mod_cast Nat.choose_pos hj
  positivity

theorem odd_filter_even_pos (r s j : ℕ) (hj : j≤2*s+1) (he : Even (r+s+j)) :
    0<oddFilterCoefficient r s j := by
  rw [odd_filter_coefficient_factorization,he.neg_one_pow,one_mul]
  exact odd_filter_magnitude_pos r s j hj

theorem odd_filter_odd_neg (r s j : ℕ) (hj : j≤2*s+1) (ho : Odd (r+s+j)) :
    oddFilterCoefficient r s j<0 := by
  rw [odd_filter_coefficient_factorization,ho.neg_one_pow,neg_one_mul]
  exact neg_neg_of_pos (odd_filter_magnitude_pos r s j hj)

theorem odd_filter_outside_support (r s j : ℕ) (hj : 2*s+1<j) :
    oddFilterCoefficient r s j=0 := by
  simp [oddFilterCoefficient,nativeOddBeta,Nat.choose_eq_zero_of_lt hj]

/-- Exact forward-difference form of the SAME physical kernel.
The difference index is MATERIAL ADDRESS, not vertical Carry depth or k. -/
theorem native_odd_kernel_forward_difference (r s : ℕ) (w : ℕ → ℂ) :
    kernel w (nativeOddProfile r) (nativeOddProfile s)=
      ((-1:ℂ)^(r+s+1)/((2*s+1).factorial:ℂ))*
        ((fwdDiff (1:ℕ))^[2*s+1]
          (fun j => ((j+1).factorial:ℂ)/((j+2*r+3).factorial:ℂ)*w j)) 0 := by
  rw [native_odd_kernel_filter]
  unfold oddFilter
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [zsmul_eq_mul,nsmul_eq_mul,mul_one,zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j≤2*s+1 := by have := Finset.mem_range.mp hj; omega
  unfold oddFilterCoefficient nativeOddBeta
  push_cast
  rw [odd_stencil_sign s j hj']
  simp only [pow_add,pow_one]
  ring

/-- The two ordered filters of the ORIGINAL symmetrized pair. -/
theorem native_odd_ordered_filters (r s : ℕ) (w : ℕ → ℂ) :
    oddPairKernel w r s=oddFilter r s w+oddFilter s r w := by
  unfold oddPairKernel
  rw [native_odd_kernel_filter,native_odd_kernel_filter]

end
end CarryOddCauchy
