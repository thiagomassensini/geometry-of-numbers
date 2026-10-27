import Stencil
import PhysicalKernels
import DividedKernel

namespace CarrySpatialCorrection
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- The SAME static stencil with its original even imaginary-step phase. -/
def nativeEvenProfile (r : ℕ) : ℕ →₀ ℂ := (-1:ℂ)^r • staticStencil (2*r)

theorem weight_finite_stencil (w : ℕ → ℂ) (s : Finset ℕ) (a : ℕ → ℂ) :
    coefficientWeight w (∑ j ∈ s, a j • Finsupp.single j 1)=
      ∑ j ∈ s, (w j*a j) • Finsupp.single j 1 := by
  classical
  ext i
  simp only [coefficient_weight_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=i
  · subst j; simp
  · simp [Finsupp.single_eq_of_ne (Ne.symm hj)]

/-- Literal two-input Cauchy pairing, retaining its original denominators. -/
theorem raw_kernel_sum (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (w : ℕ → ℂ) (m n : ℕ) :
    sectorKernel false eta h0 h1 w (rawStencil m) (rawStencil n)=
      ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
        (completedGreenForwardWeight m i : ℂ)*(completedGreenForwardWeight n j : ℂ)*
          w j / ((i:ℂ)+(j:ℂ)+2) := by
  simp only [sectorKernel, sectorField, coefficientStencil, Bool.false_eq_true, ite_false,
    rawStencil, weight_finite_stencil, map_sum, map_smul, physicalCauchySynthesis,
    Finsupp.linearCombination_single, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, inner_completedNativeChiralCauchyFeature]
  simp only [one_mul, map_one, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [completedGreenForwardWeight, map_intCast]
  push_cast
  ring

/-- Factorial-normalized kernels of arbitrary orders, not only even orders. -/
theorem static_kernel_sum (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (w : ℕ → ℂ) (m n : ℕ) :
    sectorKernel false eta h0 h1 w (staticStencil m) (staticStencil n)=
      (m.factorial:ℂ)⁻¹*(n.factorial:ℂ)⁻¹*
        ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
          (completedGreenForwardWeight m i : ℂ)*(completedGreenForwardWeight n j : ℂ)*
            w j / ((i:ℂ)+(j:ℂ)+2) := by
  simp only [staticStencil, sectorKernel, map_smul, field_scale_input,
    inner_smul_left, inner_smul_right, map_inv₀, map_natCast]
  rw [← sectorKernel, raw_kernel_sum]
  ring

/-- The ordered sum is reduced only AFTER both whole source vectors are paired.
No Hermitian symmetry is assumed for the weighted kernel. -/
theorem static_odd_divided (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (m n p : ℕ) (hp : Odd p) :
    sectorKernel false eta h0 h1 (monomialWeight p) (staticStencil m) (staticStencil n)+
    sectorKernel false eta h0 h1 (monomialWeight p) (staticStencil n) (staticStencil m)=
      dividedCoefficient m n p := by
  rw [static_kernel_sum, static_kernel_sum]
  rw [Finset.sum_comm (s:=Finset.range (n+1)) (t:=Finset.range (m+1))]
  have hpair :
      (∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
        (completedGreenForwardWeight m i:ℂ)*(completedGreenForwardWeight n j:ℂ)*
          monomialWeight p j/((i:ℂ)+(j:ℂ)+2)) +
      (∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
        (completedGreenForwardWeight n j:ℂ)*(completedGreenForwardWeight m i:ℂ)*
          monomialWeight p i/((j:ℂ)+(i:ℂ)+2)) =
      ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
        (completedGreenForwardWeight m i:ℂ)*(completedGreenForwardWeight n j:ℂ)*
          (∑ l ∈ Finset.range p, (-1:ℂ)^l*((i+1:ℕ):ℂ)^(p-1-l)*((j+1:ℕ):ℂ)^l) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hn : (((i+1:ℕ):ℂ)+((j+1:ℕ):ℂ))≠0 := by
      have he : ((i+1:ℕ):ℂ)+((j+1:ℕ):ℂ)=((i+j+2:ℕ):ℂ) := by push_cast; ring
      rw [he]
      exact_mod_cast (show i+j+2≠0 by omega)
    rw [← odd_divided_power _ _ p hp hn]
    unfold monomialWeight
    push_cast
    ring
  calc
    _ = (m.factorial:ℂ)⁻¹*(n.factorial:ℂ)⁻¹*
        ((∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
          (completedGreenForwardWeight m i:ℂ)*(completedGreenForwardWeight n j:ℂ)*
            monomialWeight p j/((i:ℂ)+(j:ℂ)+2))+
        (∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
          (completedGreenForwardWeight n j:ℂ)*(completedGreenForwardWeight m i:ℂ)*
            monomialWeight p i/((j:ℂ)+(i:ℂ)+2))) := by ring
    _ = _ := by
      rw [hpair]
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s:=Finset.range (n+1)) (t:=Finset.range p)]
      rw [Finset.sum_comm]
      unfold dividedCoefficient
      apply Finset.sum_congr rfl
      intro l _
      rw [difference_power_sum, difference_power_sum]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm (s:=Finset.range (n+1)) (t:=Finset.range (m+1))]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold completedGreenForwardWeight
      ring

/-- The original phase of the even radial jet is retained in BOTH arguments. -/
theorem native_odd_divided (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (r s p : ℕ) (hp : Odd p) :
    sectorKernel false eta h0 h1 (monomialWeight p) (nativeEvenProfile r) (nativeEvenProfile s)+
    sectorKernel false eta h0 h1 (monomialWeight p) (nativeEvenProfile s) (nativeEvenProfile r)=
      (-1:ℂ)^(r+s)*dividedCoefficient (2*r) (2*s) p := by
  simp only [nativeEvenProfile, sectorKernel, map_smul, field_scale_input,
    inner_smul_left, inner_smul_right, map_pow, map_neg, map_one]
  have h := static_odd_divided eta h0 h1 (2*r) (2*s) p hp
  unfold sectorKernel at h
  rw [← h, pow_add]
  ring

/-- Exact finite Stirling extraction for EVERY odd address-power degree. -/
theorem native_odd_stirling (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (r s p : ℕ) (hp : Odd p) :
    sectorKernel false eta h0 h1 (monomialWeight p) (nativeEvenProfile r) (nativeEvenProfile s)+
    sectorKernel false eta h0 h1 (monomialWeight p) (nativeEvenProfile s) (nativeEvenProfile r)=
      (-1:ℂ)^(r+s)*∑ l ∈ Finset.range p,
        (-1:ℂ)^l*(Nat.stirlingSecond (p-l) (2*r+1):ℂ)*
          (Nat.stirlingSecond (l+1) (2*s+1):ℂ) := by
  rw [native_odd_divided eta h0 h1 r s p hp]
  unfold dividedCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  simp only [difference_power_stirling]
  rw [show p-1-l+1=p-l by have := Finset.mem_range.mp hl; omega]

/-- All lower odd powers cancel in the TWO ordered physical pairings. -/
theorem native_below (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (r s p : ℕ) (hp : Odd p) (hb : p < 2*r+2*s+1) :
    sectorKernel false eta h0 h1 (monomialWeight p) (nativeEvenProfile r) (nativeEvenProfile s)+
    sectorKernel false eta h0 h1 (monomialWeight p) (nativeEvenProfile s) (nativeEvenProfile r)=0 := by
  rw [native_odd_divided eta h0 h1 r s p hp, divided_below hb, mul_zero]

/-- Main all-order spatial law in TWO independent indices. Complex equality. -/
theorem native_first_correction (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (r s : ℕ) :
    sectorKernel false eta h0 h1 (monomialWeight (2*r+2*s+3))
      (nativeEvenProfile r) (nativeEvenProfile s)+
    sectorKernel false eta h0 h1 (monomialWeight (2*r+2*s+3))
      (nativeEvenProfile s) (nativeEvenProfile r)=
      (-1:ℂ)^(r+s)*spatialCorrection (2*r) (2*s) := by
  rw [native_odd_divided eta h0 h1 r s _ ⟨r+s+1, by omega⟩,
    divided_first_correction]

/-- The same all-order cancellation at the leading odd degree. -/
theorem native_leading (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (r s : ℕ) :
    sectorKernel false eta h0 h1 (monomialWeight (2*r+2*s+1))
      (nativeEvenProfile r) (nativeEvenProfile s)+
    sectorKernel false eta h0 h1 (monomialWeight (2*r+2*s+1))
      (nativeEvenProfile s) (nativeEvenProfile r)=(-1:ℂ)^(r+s) := by
  rw [native_odd_divided eta h0 h1 r s _ ⟨r+s, by omega⟩, divided_leading, mul_one]

end
end CarrySpatialCorrection
