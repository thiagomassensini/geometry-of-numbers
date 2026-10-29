import GridSignObstruction

namespace CarryAddressSplit
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000

/-- The EXISTING source address weight. Not the material logarithmic clock. -/
abbrev addressPower (p : ℕ) (c : ℕ →₀ ℂ) : ℕ →₀ ℂ := coefficientWeight (monomialWeight p) c

/-- Endpoint of the literal finite half-density synthesis, not a new metric. -/
def sourceEndpoint : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ (fun _ => 1)

theorem source_endpoint_sum (c : ℕ →₀ ℂ) : sourceEndpoint c=∑ j ∈ c.support, c j := by
  simp [sourceEndpoint,Finsupp.linearCombination_apply,Finsupp.sum]

theorem source_endpoint_single (j : ℕ) (z : ℂ) : sourceEndpoint (Finsupp.single j z)=z := by
  simp [sourceEndpoint]

theorem source_endpoint_physical (c : ℕ →₀ ℂ) :
    sourceEndpoint c=(∑ j ∈ c.support, c j • completedNativeChiralCauchyContinuousFeature j) 1 := by
  simp [source_endpoint_sum,completedNativeChiralCauchyContinuousFeature]

theorem address_power_apply (p : ℕ) (c : ℕ →₀ ℂ) (j : ℕ) :
    addressPower p c j=((j:ℂ)+1)^p*c j := by
  simp [addressPower,coefficient_weight_apply,monomialWeight]

theorem address_power_zero (c : ℕ →₀ ℂ) : addressPower 0 c=c := by
  ext j
  simp only [address_power_apply,pow_zero,one_mul]

theorem address_power_support (p : ℕ) (c : ℕ →₀ ℂ) : (addressPower p c).support=c.support := by
  classical
  ext j
  have hj : (j:ℂ)+1≠0 := by exact_mod_cast (by omega : j+1≠0)
  simp [Finsupp.mem_support_iff,address_power_apply,pow_ne_zero p hj]

theorem address_power_comp (p q : ℕ) (c : ℕ →₀ ℂ) :
    addressPower p (addressPower q c)=addressPower (p+q) c := by
  ext j
  simp only [address_power_apply,pow_add]
  ring

theorem address_power_add (p : ℕ) (c d : ℕ →₀ ℂ) :
    addressPower p (c+d)=addressPower p c+addressPower p d := by
  ext j
  simp only [address_power_apply,Finsupp.add_apply,mul_add]

theorem address_power_scale (p : ℕ) (z : ℂ) (c : ℕ →₀ ℂ) :
    addressPower p (z • c)=z • addressPower p c := by
  ext j
  simp only [address_power_apply,Finsupp.smul_apply,smul_eq_mul]
  ring

theorem address_power_single (p j : ℕ) (z : ℂ) :
    addressPower p (Finsupp.single j z)=Finsupp.single j (((j:ℂ)+1)^p*z) := by
  ext n
  by_cases hn : n=j
  · simp [address_power_apply,hn]
  · simp [address_power_apply,Finsupp.single_eq_of_ne hn]

theorem address_power_sum (p : ℕ) (S : Finset ℕ) (f : ℕ → ℕ →₀ ℂ) :
    addressPower p (∑ j ∈ S, f j)=∑ j ∈ S, addressPower p (f j) :=
  weight_sum_input (monomialWeight p) S f

/-- Exact finite-source Green identity: the endpoint term is KEPT.
It is the source-weight version of the existing radial Euler Green mechanism. -/
theorem kernel_address_green (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    kernel w (addressPower 1 c) d+kernel w c (addressPower 1 d)=
      conj (sourceEndpoint c)*(∑ j ∈ d.support, w j*d j) := by
  rw [kernel_double_sum,kernel_double_sum,source_endpoint_sum]
  simp only [address_power_support,address_power_apply,pow_one,map_mul,map_add,map_natCast,map_one,map_sum]
  rw [← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : (i:ℂ)+(j:ℂ)+2≠0 := by exact_mod_cast (by omega : i+j+2≠0)
  field_simp
  ring

/-- BOTH ordered kernels, as in the original pure-odd chiral readout. -/
def symKernel (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) : ℂ := kernel w c d+kernel w d c

theorem sym_kernel_swap (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) : symKernel w c d=symKernel w d c := by
  unfold symKernel
  ring

theorem sym_address_self_zero (w : ℕ → ℂ) (c : ℕ →₀ ℂ) (hc : sourceEndpoint c=0) :
    symKernel w c (addressPower 1 c)=0 := by
  have he := kernel_address_green w c c
  rw [hc] at he
  simp only [map_zero,zero_mul] at he
  unfold symKernel
  linear_combination he

theorem sym_second_first_zero (w : ℕ → ℂ) (c : ℕ →₀ ℂ)
    (hc : sourceEndpoint (addressPower 1 c)=0) :
    symKernel w (addressPower 2 c) (addressPower 1 c)=0 := by
  have he := sym_address_self_zero w (addressPower 1 c) hc
  rw [address_power_comp] at he
  simpa only [show 1+1=2 by decide,sym_kernel_swap] using he

theorem kernel_source_add_left (w : ℕ → ℂ) (c d v : ℕ →₀ ℂ) :
    kernel w (c+d) v=kernel w c v+kernel w d v := by
  change inner ℂ (physicalCauchySynthesis (c+d))
    (physicalCauchySynthesis (coefficientWeight w v))=_
  rw [map_add,inner_add_left]
  rfl

theorem kernel_source_add_right (w : ℕ → ℂ) (c d v : ℕ →₀ ℂ) :
    kernel w v (c+d)=kernel w v c+kernel w v d := by
  have hw : coefficientWeight w (c+d)=coefficientWeight w c+coefficientWeight w d := by
    ext j
    simp only [coefficient_weight_apply,Finsupp.add_apply,mul_add]
  change inner ℂ (physicalCauchySynthesis v) (physicalCauchySynthesis (coefficientWeight w (c+d)))=_
  rw [hw,map_add,inner_add_right]
  rfl

theorem kernel_source_neg_left (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    kernel w (-c) d= -kernel w c d := by
  change inner ℂ (physicalCauchySynthesis (-c)) _=_
  rw [map_neg,inner_neg_left]
  rfl

theorem kernel_source_neg_right (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    kernel w c (-d)= -kernel w c d := by
  have hw : coefficientWeight w (-d)= -coefficientWeight w d := by
    ext j
    simp only [coefficient_weight_apply,Finsupp.neg_apply,mul_neg]
  change inner ℂ _ (physicalCauchySynthesis (coefficientWeight w (-d)))=_
  rw [hw,map_neg,inner_neg_right]
  rfl

theorem sym_sub_sub (w : ℕ → ℂ) (c d v z : ℕ →₀ ℂ) :
    symKernel w (c-d) (v-z)=
      symKernel w c v-symKernel w c z-symKernel w d v+symKernel w d z := by
  simp only [symKernel,sub_eq_add_neg,kernel_source_add_left,kernel_source_add_right,
    kernel_source_neg_left,kernel_source_neg_right]
  ring

/-- Move the SAME real address weight through the right weighted source. -/
theorem kernel_address_right (p : ℕ) (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    kernel w c (addressPower p d)=kernel (fun j => ((j:ℂ)+1)^p*w j) c d := by
  have he : coefficientWeight w (addressPower p d)=
      coefficientWeight (fun j => ((j:ℂ)+1)^p*w j) d := by
    ext j
    simp only [addressPower,coefficient_weight_apply,monomialWeight]
    push_cast
    ring
  change inner ℂ _ (physicalCauchySynthesis (coefficientWeight w (addressPower p d)))=_
  rw [he]
  rfl

end
end CarryAddressSplit
