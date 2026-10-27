import OddAddressLowering
namespace CarryAddressSplit
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- Boundary cancellation makes this split orthogonal for the SIGNED ordered sum.
It is not a Hilbert norm identity and does not assume a moment sign. -/

theorem address_even_odd_orthogonal (w : ℕ → ℂ) (v : ℕ →₀ ℂ)
    (h0 : sourceEndpoint v=0) (h1 : sourceEndpoint (addressPower 1 v)=0)
    (A B C : ℝ) :
    symKernel w ((A:ℂ) • v+(B:ℂ) • addressPower 2 v)
      ((C:ℂ) • addressPower 1 v)=0 := by
  have hz := sym_address_self_zero w v h0
  have ht := sym_second_first_zero w v h1
  simp only [symKernel,kernel_source_add_left,kernel_source_add_right,
    kernel_smul_left,kernel_smul_right,Complex.conj_ofReal] at hz ht ⊢
  linear_combination (A:ℂ)*(C:ℂ)*hz+(B:ℂ)*(C:ℂ)*ht

/-- This Green cancellation is available at EVERY odd stencil order above the first. -/

theorem native_odd_address_orthogonal (r : ℕ) (w : ℕ → ℂ) (A B C : ℝ) :
    symKernel w ((A:ℂ) • nativeOddProfile (r+1)+
      (B:ℂ) • addressPower 2 (nativeOddProfile (r+1)))
      ((C:ℂ) • addressPower 1 (nativeOddProfile (r+1)))=0 := by
  apply address_even_odd_orthogonal
  · have he := endpoint_odd_power_zero (r+1) 0 (by omega)
    simpa only [address_power_zero] using he
  · exact endpoint_odd_power_zero (r+1) 1 (by omega)

/-- Literal component of the ORIGINAL critical input; no fitted source or metric. -/

def principalInput (a : ℝ) (k : ℕ) : ℕ →₀ ℂ :=
  ((((k:ℝ)+1)^3+12*a*((k:ℝ)+1):ℝ):ℂ) • nativeOddProfile 1+
    ((a*((k:ℝ)+1):ℝ):ℂ) • addressPower 2 (nativeOddProfile 1)

/-- The retained correction component. Its factor 7 comes from (D-3)(D-4). -/

def defectInput (a : ℝ) (k : ℕ) : ℕ →₀ ℂ :=
  ((7*a*((k:ℝ)+1):ℝ):ℂ) • addressPower 1 (nativeOddProfile 1)

theorem critical_input_split (a : ℝ) (k : ℕ) :
    criticalOddSource a k=principalInput a k-defectInput a k := by
  have he := odd_address_lowering 0
  simp only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat,show (3:ℂ)*4=12 by norm_num] at he
  rw [critical_source_profiles]
  ext j
  have hj := DFunLike.congr_fun he j
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.neg_apply,Finsupp.smul_apply,
    smul_eq_mul] at hj
  simp only [principalInput,defectInput,Finsupp.add_apply,Finsupp.sub_apply,
    Finsupp.smul_apply,smul_eq_mul]
  push_cast
  linear_combination -(a:ℂ)*((k:ℂ)+1)*hj

theorem principal_defect_kernel_orthogonal (a b : ℝ) (k : ℕ) (w : ℕ → ℂ) :
    symKernel w (principalInput a k) (defectInput b k)=0 := by
  simpa only [principalInput,defectInput] using
    native_odd_address_orthogonal 0 w
      (((k:ℝ)+1)^3+12*a*((k:ℝ)+1)) (a*((k:ℝ)+1)) (7*b*((k:ℝ)+1))

theorem defect_principal_kernel_orthogonal (a b : ℝ) (k : ℕ) (w : ℕ → ℂ) :
    symKernel w (defectInput a k) (principalInput b k)=0 := by
  rw [sym_kernel_swap]
  exact principal_defect_kernel_orthogonal b a k w

/-- Both legs of EVERY original bulk/boundary/commutator field split first. -/

theorem completed_parts_split (a : ℝ) (k : ℕ)
    (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (j : Fin 3) :
    completedSourceParts eta h0 h1 k (criticalOddSource a k) j=
      completedSourceParts eta h0 h1 k (principalInput a k) j-
      completedSourceParts eta h0 h1 k (defectInput a k) j := by
  have he := completed_part_add_input eta h0 h1 k (criticalOddSource a k) (defectInput a k) j
  have hc : criticalOddSource a k+defectInput a k=principalInput a k := by
    rw [critical_input_split,sub_add_cancel]
  rw [hc] at he
  exact eq_sub_of_add_eq he.symm

/-- No physical source is replaced: the full original two-leg state splits linearly. -/

theorem complete_physical_source_split (a : ℝ) (k : ℕ) :
    physicalCompletedFiniteSource k (criticalOddSource a k)=
      physicalCompletedFiniteSource k (principalInput a k)-
      physicalCompletedFiniteSource k (defectInput a k) := by
  simp only [critical_input_split,physicalCompletedFiniteSource_original,map_sub]

theorem weighted_odd_support (p : ℕ) :
    (addressPower p (nativeOddProfile 1)).support ⊆ Finset.range 4 := by
  rw [address_power_support]
  exact odd_profile_support 1

theorem principal_support (a : ℝ) (k : ℕ) :
    (principalInput a k).support ⊆ Finset.range 4 := by
  exact (Finsupp.support_add).trans (Finset.union_subset
    ((Finsupp.support_smul).trans (odd_profile_support 1))
    ((Finsupp.support_smul).trans (weighted_odd_support 2)))

theorem defect_support (a : ℝ) (k : ℕ) :
    (defectInput a k).support ⊆ Finset.range 4 :=
  (Finsupp.support_smul).trans (weighted_odd_support 1)

theorem weighted_odd_imaginary (p j : ℕ) :
    conj (addressPower p (nativeOddProfile 1) j)= -addressPower p (nativeOddProfile 1) j := by
  simp only [address_power_apply,native_odd_coefficient,map_mul,map_pow,map_add,
    map_natCast,map_one,Complex.conj_I,Complex.conj_ofReal]
  ring

theorem principal_imaginary (a : ℝ) (k j : ℕ) :
    conj (principalInput a k j)= -principalInput a k j := by
  have hzero := weighted_odd_imaginary 0 j
  rw [address_power_zero] at hzero
  simp only [principalInput,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,
    map_add,map_mul,Complex.conj_ofReal,hzero,weighted_odd_imaginary]
  ring

theorem defect_imaginary (a : ℝ) (k j : ℕ) :
    conj (defectInput a k j)= -defectInput a k j := by
  simp only [defectInput,Finsupp.smul_apply,smul_eq_mul,map_mul,
    Complex.conj_ofReal,weighted_odd_imaginary]
  ring

end
end CarryAddressSplit
