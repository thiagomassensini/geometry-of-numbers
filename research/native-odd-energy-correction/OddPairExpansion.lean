import OddProfiles

namespace CarryOddEnergy
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem odd_pair_taylor_sum (N r s : ℕ) (z : ℂ) :
    oddPairKernel (taylorSamples N z) r s=
      ∑ l ∈ Finset.range N, ((-1:ℂ)^l*(h l:ℂ)*z^(2*l+1))*
        oddPairKernel (monomialWeight (2*l+1)) r s := by
  unfold taylorSamples oddPairKernel
  rw [kernel_sum_weight, kernel_sum_weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [kernel_scale, kernel_scale]
  ring

/-- The TWO surviving Taylor contributions, before scalar readout. -/
theorem odd_pair_taylor_cancellation (r s : ℕ) (z : ℂ) :
    oddPairKernel (taylorSamples (r+s+3) z) r s=
      z^(2*(r+s+1)+1)*((h (r+s+1):ℂ)-z^2*
        spatialCorrection (2*r+1) (2*s+1)*(h (r+s+2):ℂ)) := by
  rw [odd_pair_taylor_sum, Finset.sum_range_succ, Finset.sum_range_succ]
  have hz : (∑ l ∈ Finset.range (r+s+1), ((-1:ℂ)^l*(h l:ℂ)*z^(2*l+1))*
      oddPairKernel (monomialWeight (2*l+1)) r s)=0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [odd_pair_below r s l (Finset.mem_range.mp hl), mul_zero]
  rw [hz, zero_add, odd_pair_leading, odd_pair_correction]
  have hs : (-1:ℂ)^(r+s+1)*(-1:ℂ)^(r+s+1)=1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [pow_succ (-1:ℂ) (r+s+1)]
  have he : z^(2*(r+s+2)+1)=z^(2*(r+s+1)+1)*z^2 := by rw [← pow_add]; congr 1
  rw [he]
  linear_combination ((h (r+s+1):ℂ)*z^(2*(r+s+1)+1)-
    z^(2*(r+s+1)+1)*z^2*spatialCorrection (2*r+1) (2*s+1)*(h (r+s+2):ℂ))*hs

/-- Expansion of the SAME complete complex synthesis in each argument. -/
theorem odd_pair_response_expansion (r s : ℕ) :
    ∀ᶠ z : ℂ in nhds 0,
      oddPairKernel (responseSamples z) r s=
        z^(2*(r+s+1)+1)*((h (r+s+1):ℂ)-z^2*spatialCorrection (2*r+1) (2*s+1)*
          (h (r+s+2):ℂ)+z^4*oddPairKernel (remainderSamples (r+s+3) z) r s) := by
  filter_upwards [response_synthesis_expansion (r+s+3) (nativeOddProfile r),
    response_synthesis_expansion (r+s+3) (nativeOddProfile s)] with z hr hs
  have he : oddPairKernel (responseSamples z) r s=
      oddPairKernel (taylorSamples (r+s+3) z) r s+
        z^(2*(r+s+3)+1)*oddPairKernel (remainderSamples (r+s+3) z) r s := by
    change (inner ℂ _ (physicalCauchySynthesis (coefficientWeight (responseSamples z) _)))+
      (inner ℂ _ (physicalCauchySynthesis (coefficientWeight (responseSamples z) _)))=_
    rw [hr, hs]
    simp only [inner_add_right, inner_smul_right]
    unfold oddPairKernel kernel sectorKernel sectorField coefficientStencil
    simp only [Bool.false_eq_true, ite_false]
    ring
  rw [he, odd_pair_taylor_cancellation,
    show 2*(r+s+3)+1=(2*(r+s+1)+1)+4 by omega, pow_add]
  ring

theorem odd_pair_remainder_continuous (r s : ℕ) :
    ContinuousAt (fun z : ℂ => oddPairKernel (remainderSamples (r+s+3) z) r s) 0 := by
  have hw (j : ℕ) : ContinuousAt (fun z : ℂ => remainderSamples (r+s+3) z j) 0 := by
    have ht : Tendsto (fun z : ℂ => ((j+1:ℕ):ℂ)*z) (nhds 0) (nhds 0) := by
      have hc : ContinuousAt (fun z : ℂ => ((j+1:ℕ):ℂ)*z) 0 := by fun_prop
      simpa using hc.tendsto
    have hR := ((native_remainder_analytic (r+s+3)).continuousAt.tendsto.comp ht)
    simp only [remainderSamples]
    have hc : ContinuousAt (fun z : ℂ => nativeRemainder (r+s+3) (((j+1:ℕ):ℂ)*z)) 0 := by
      simpa only [ContinuousAt, Function.comp_def, mul_zero] using hR
    exact continuousAt_const.mul hc
  have hr := weighted_synthesis_continuous (fun z => remainderSamples (r+s+3) z) (nativeOddProfile r) hw
  have hs := weighted_synthesis_continuous (fun z => remainderSamples (r+s+3) z) (nativeOddProfile s) hw
  change ContinuousAt (fun z : ℂ => inner ℂ _
    (physicalCauchySynthesis (coefficientWeight (remainderSamples (r+s+3) z) _))+
    inner ℂ _ (physicalCauchySynthesis (coefficientWeight (remainderSamples (r+s+3) z) _))) 0
  exact (continuousAt_const.inner hs).add (continuousAt_const.inner hr)

/-- Normalized original two-input flux, before its final real readout. -/
def normalizedOddPair (r s k : ℕ) : ℂ :=
  ((k:ℂ)+1)^(2*(r+s+1)+1)*oddPairKernel (responseSamples (radialStep k)) r s

theorem normalized_odd_pair_expansion (r s : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      normalizedOddPair r s k=(h (r+s+1):ℂ)-(radialStep k:ℂ)^2*
        spatialCorrection (2*r+1) (2*s+1)*(h (r+s+2):ℂ)+(radialStep k:ℂ)^4*
          oddPairKernel (remainderSamples (r+s+3) (radialStep k)) r s := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  filter_upwards [ht.eventually (odd_pair_response_expansion r s)] with k hk
  unfold normalizedOddPair
  rw [hk]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  rw [← mul_assoc, ← mul_pow, hi, one_pow, one_mul]

theorem normalized_odd_pair_correction_tendsto (r s : ℕ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)^2*(normalizedOddPair r s k-(h (r+s+1):ℂ)))
      atTop (nhds (-spatialCorrection (2*r+1) (2*s+1)*(h (r+s+2):ℂ))) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hR := (odd_pair_remainder_continuous r s).tendsto.comp ht
  have hlim := (tendsto_const_nhds (x := -spatialCorrection (2*r+1) (2*s+1)*(h (r+s+2):ℂ))).add
    ((ht.pow 2).mul hR)
  simp only [zero_pow (by decide : 2≠0), zero_mul, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [normalized_odd_pair_expansion r s] with k hk
  rw [hk]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  have hi2 := congrArg (fun z : ℂ => z^2) hi
  simp only [mul_pow, one_pow] at hi2
  simp only [Function.comp_def]
  linear_combination (spatialCorrection (2*r+1) (2*s+1)*(h (r+s+2):ℂ))*hi2-
    (radialStep k:ℂ)^2*oddPairKernel (remainderSamples (r+s+3) (radialStep k)) r s*hi2

end
end CarryOddEnergy
