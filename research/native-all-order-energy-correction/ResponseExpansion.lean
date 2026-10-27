import Regression
import PhysicalKernels

namespace CarryEnergyCorrection
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The original response Taylor polynomial, without any sign hypothesis. -/
def oddTaylor (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, (-1:ℂ)^j*(h j:ℂ)*z^(2*j+1)

theorem response_taylor_polynomial (N : ℕ) (z : ℂ) :
    (∑ n ∈ Finset.range (2*N+1), responseCoefficient n*z^n)=oddTaylor N z := by
  induction N with
  | zero => simp [oddTaylor, response_coefficient_even 0]
  | succ N ih =>
    rw [show 2*(N+1)+1=(2*N+1)+1+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      show 2*N+1+1=2*(N+1) by omega, response_coefficient_even]
    simp only [zero_mul, add_zero, response_coefficient_odd, oddTaylor,
      Finset.sum_range_succ]

/-- ONE remainder of the same native germ for each truncation order. -/
theorem response_odd_remainder (N : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ z : ℂ in nhds 0,
      responseReadout z=oddTaylor N z+z^(2*N+1)*R z := by
  obtain ⟨R,hR,he⟩ := response_readout_analytic.exists_eventuallyEq_sum_add_pow_mul (2*N+1)
  refine ⟨R,hR,?_⟩
  filter_upwards [he] with z hz
  rw [hz]
  have hp : (∑ n ∈ Finset.range (2*N+1),
      (z^n/(n.factorial:ℂ)) • iteratedDeriv n responseReadout 0)=
      ∑ n ∈ Finset.range (2*N+1), responseCoefficient n*z^n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [← response_coefficient_derivative]
    simp only [smul_eq_mul]
    ring
  rw [hp, response_taylor_polynomial]
  rfl

def nativeRemainder (N : ℕ) : ℂ → ℂ := Classical.choose (response_odd_remainder N)

theorem native_remainder_analytic (N : ℕ) : AnalyticAt ℂ (nativeRemainder N) 0 :=
  (Classical.choose_spec (response_odd_remainder N)).1

theorem native_response_expansion (N : ℕ) :
    ∀ᶠ z : ℂ in nhds 0,
      responseReadout z=oddTaylor N z+z^(2*N+1)*nativeRemainder N z :=
  (Classical.choose_spec (response_odd_remainder N)).2

/-- Literal complex address samples, before any real/imaginary readout. -/
def responseSamples (z : ℂ) (j : ℕ) : ℂ := responseReadout (((j+1:ℕ):ℂ)*z)
def taylorSamples (N : ℕ) (z : ℂ) (j : ℕ) : ℂ :=
  ∑ l ∈ Finset.range N, ((-1:ℂ)^l*(h l:ℂ)*z^(2*l+1))*monomialWeight (2*l+1) j

def remainderSamples (N : ℕ) (z : ℂ) (j : ℕ) : ℂ :=
  monomialWeight (2*N+1) j*nativeRemainder N (((j+1:ℕ):ℂ)*z)

/-- The same remainder is retained at every address of a finite prefix. -/
theorem response_samples_prefix (N M : ℕ) :
    ∀ᶠ z : ℂ in nhds 0, ∀ j : Fin M,
      responseSamples z j=taylorSamples N z j+z^(2*N+1)*remainderSamples N z j := by
  have ht (j : Fin M) : Tendsto (fun z : ℂ => ((j.val+1:ℕ):ℂ)*z) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun z : ℂ => ((j.val+1:ℕ):ℂ)*z) 0 := by fun_prop
    simpa using hc.tendsto
  have he : ∀ᶠ z : ℂ in nhds 0, ∀ j : Fin M,
      responseReadout (((j.val+1:ℕ):ℂ)*z)=
        oddTaylor N (((j.val+1:ℕ):ℂ)*z)+
          (((j.val+1:ℕ):ℂ)*z)^(2*N+1)*nativeRemainder N (((j.val+1:ℕ):ℂ)*z) := by
    rw [eventually_all]
    exact fun j => (ht j).eventually (native_response_expansion N)
  filter_upwards [he] with z hz
  intro j
  rw [responseSamples, hz j]
  unfold oddTaylor taylorSamples remainderSamples monomialWeight
  rw [mul_pow]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    rw [mul_pow]
    ring
  · ring

/-- This is only an abbreviation for the existing full-sector Cauchy pairing.
The auxiliary eta of sectorKernel false does not occur in its value. -/
abbrev kernel (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) : ℂ :=
  sectorKernel false (1/2) (by norm_num) (by norm_num) w c d

abbrev pairKernel (w : ℕ → ℂ) (r s : ℕ) : ℂ :=
  kernel w (nativeEvenProfile r) (nativeEvenProfile s)+
    kernel w (nativeEvenProfile s) (nativeEvenProfile r)

theorem kernel_add (w v : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    kernel (fun j => w j+v j) c d=kernel w c d+kernel v c d :=
  kernel_add_weight false (1/2) (by norm_num) (by norm_num) w v c d

theorem kernel_scale (a : ℂ) (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    kernel (fun j => a*w j) c d=a*kernel w c d :=
  kernel_scale_weight false (1/2) (by norm_num) (by norm_num) a w c d

theorem kernel_sum_weight (S : Finset ℕ) (w : ℕ → ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    kernel (fun j => ∑ l ∈ S, w l j) c d=∑ l ∈ S, kernel (w l) c d := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hz : coefficientWeight (fun _ => 0) d=0 := by
      ext j
      simp [coefficient_weight_apply]
    change inner ℂ (physicalCauchySynthesis c)
      (physicalCauchySynthesis (coefficientWeight (fun _ => 0) d))=0
    rw [hz, map_zero, inner_zero_right]
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [kernel_add, ih]

theorem native_profile_support (r : ℕ) :
    (nativeEvenProfile r).support ⊆ Finset.range (2*r+1) := by
  intro j hj
  apply Finset.mem_range.mpr
  by_contra hn
  have hz : nativeEvenProfile r j=0 := by
    simp only [nativeEvenProfile, staticStencil, Finsupp.smul_apply, smul_eq_mul,
      raw_stencil_apply, completedGreenForwardWeight]
    rw [Nat.choose_eq_zero_of_lt (by omega : 2*r < j)]
    simp
  exact (Finsupp.mem_support_iff.mp hj) hz

/-- Equality of the whole weighted synthesis, before pairing an independent input. -/
theorem response_synthesis_expansion (N : ℕ) (c : ℕ →₀ ℂ) :
    ∀ᶠ z : ℂ in nhds 0,
      physicalCauchySynthesis (coefficientWeight (responseSamples z) c)=
        physicalCauchySynthesis (coefficientWeight (taylorSamples N z) c)+
          z^(2*N+1) • physicalCauchySynthesis (coefficientWeight (remainderSamples N z) c) := by
  classical
  obtain ⟨M,hM⟩ := Finset.exists_nat_subset_range c.support
  filter_upwards [response_samples_prefix N M] with z hz
  have hc : coefficientWeight (responseSamples z) c=
      coefficientWeight (fun j => taylorSamples N z j+z^(2*N+1)*remainderSamples N z j) c := by
    ext j
    simp only [coefficient_weight_apply]
    by_cases hj : j∈c.support
    · rw [hz ⟨j,Finset.mem_range.mp (hM hj)⟩]
    · rw [Finsupp.notMem_support_iff.mp hj]; ring
  rw [hc]
  have hs := stencil_add_weight false (1/2) (taylorSamples N z)
    (fun j => z^(2*N+1)*remainderSamples N z j) c
  have ht := stencil_scale_weight false (1/2) (z^(2*N+1)) (remainderSamples N z) c
  simp only [coefficientStencil, Bool.false_eq_true, ite_false] at hs ht
  rw [hs, ht, map_add, map_smul]

end
end CarryEnergyCorrection
