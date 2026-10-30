import EffectiveResponse

namespace CarrySummableRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Effective tail sampled at the original arithmetic addresses. -/
def effectiveRemainderSamples (M : ℕ) (z : ℂ) (j : ℕ) : ℂ :=
  monomialWeight (2*M+1) j * effectiveResponseRemainder M (((j+1:ℕ):ℂ)*z)

theorem effective_response_samples (M j : ℕ) (z : ℂ)
    (hz : ‖((j+1:ℕ):ℂ)*z‖ < 1/4)
    (hF : completedNativeOperatorCharacteristic
      (Complex.I*(((j+1:ℕ):ℂ)*z)) ≠ 0) :
    responseSamples z j = taylorSamples M z j +
      z^(2*M+1)*effectiveRemainderSamples M z j := by
  rw [responseSamples, effective_response_expansion M _ hz hF]
  unfold oddTaylor taylorSamples effectiveRemainderSamples monomialWeight
  rw [mul_pow]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    rw [mul_pow]
    ring
  · ring

theorem odd_filter_affine (r s : ℕ) (a : ℂ) (w v : ℕ → ℂ) :
    oddFilter r s (fun j => w j+a*v j)=oddFilter r s w+a*oddFilter r s v := by
  unfold oddFilter
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact two-order transport after the complete original Cauchy synthesis.
The independent order indices and both ordered filters remain present. -/
theorem odd_pair_effective_expansion (r s : ℕ) (z : ℂ)
    (hz : ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*z‖ < 1/4)
    (hF : ∀ j < 2*max r s+2, completedNativeOperatorCharacteristic
      (Complex.I*(((j+1:ℕ):ℂ)*z)) ≠ 0) :
    oddPairKernel (responseSamples z) r s =
      z^(2*(r+s+1)+1) * ((h (r+s+1):ℂ) - z^2 *
        spatialCorrection (2*r+1) (2*s+1)*(h (r+s+2):ℂ) +
        z^4*oddPairKernel (effectiveRemainderSamples (r+s+3) z) r s) := by
  let M := r+s+3
  have hf (u v : ℕ) (hu : u ≤ max r s) (hv : v ≤ max r s) :
      oddFilter u v (responseSamples z) =
        oddFilter u v (fun j => taylorSamples M z j+
          z^(2*M+1)*effectiveRemainderSamples M z j) := by
    unfold oddFilter
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < 2*max r s+2 := by
      have := Finset.mem_range.mp hj
      omega
    rw [effective_response_samples M j z (hz j hj') (hF j hj')]
  have he : oddPairKernel (responseSamples z) r s =
      oddPairKernel (taylorSamples M z) r s +
        z^(2*M+1)*oddPairKernel (effectiveRemainderSamples M z) r s := by
    rw [native_odd_ordered_filters, hf r s (le_max_left _ _) (le_max_right _ _),
      hf s r (le_max_right _ _) (le_max_left _ _),
      odd_filter_affine, odd_filter_affine, native_odd_ordered_filters,
      native_odd_ordered_filters]
    ring
  rw [he, odd_pair_taylor_cancellation]
  dsimp only [M]
  rw [show 2*(r+s+3)+1=(2*(r+s+1)+1)+4 by omega, pow_add]
  ring

/-- The physical normalized pair has the effective expansion at every
explicitly regular source step, with no eventual or sign hypothesis. -/
theorem normalized_odd_pair_effective_at_regular (S : Finset ℕ) (r s k : ℕ)
    (hr : r ∈ S) (hs : s ∈ S)
    (hk : (oddGridSize S : ℝ)*|radialFourSourceStep k| < 1/4) :
    normalizedOddPair r s k = (h (r+s+1):ℂ) - (radialStep k:ℂ)^2*
      spatialCorrection (2*r+1) (2*s+1)*(h (r+s+2):ℂ) + (radialStep k:ℂ)^4*
      oddPairKernel (effectiveRemainderSamples (r+s+3) (radialStep k)) r s := by
  let N := oddGridSize S
  have hr' : r ≤ S.sup id := Finset.le_sup (f:=id) hr
  have hs' : s ≤ S.sup id := Finset.le_sup (f:=id) hs
  have hm : 2*max r s+2 ≤ N := by
    dsimp [N, oddGridSize]
    omega
  have hz (j : ℕ) (hj : j < 2*max r s+2) :
      ‖((j+1:ℕ):ℂ)*(radialStep k:ℂ)‖ < 1/4 := by
    have hh := finite_grid_radius N (radialFourSourceStep k) hk ⟨j,by omega⟩
    simpa [CarryMovingRadial.point, radialStep, radialFourSourceStep, norm_mul,
      mul_assoc] using hh
  have hF (j : ℕ) (hj : j < 2*max r s+2) :
      completedNativeOperatorCharacteristic
        (Complex.I*(((j+1:ℕ):ℂ)*(radialStep k:ℂ))) ≠ 0 := by
    have hh := (finite_radial_regular N (radialFourSourceStep k) hk ⟨j,by omega⟩).1
    simpa [CarryMovingRadial.point, radialStep, radialFourSourceStep,
      mul_assoc] using hh
  have he := odd_pair_effective_expansion r s (radialStep k:ℂ) hz hF
  unfold normalizedOddPair
  rw [he]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  rw [← mul_assoc, ← mul_pow, hi, one_pow, one_mul]

end
end CarrySummableRadial
