import MixedSpatialLeading

namespace CarryMixedImaginary
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem mixed_taylor_sum (N r s : ℕ) (z : ℂ) :
    mixedStaticPair (taylorSamples N z) r s=
      ∑ l ∈ Finset.range N, ((-1:ℂ)^l*(h l:ℂ)*z^(2*l+1))*
        mixedStaticPair (monomialWeight (2*l+1)) r s := by
  unfold taylorSamples mixedStaticPair
  rw [kernel_sum_weight, kernel_sum_weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [kernel_scale, kernel_scale]
  ring

theorem mixed_taylor_cancellation (r s : ℕ) (z : ℂ) :
    mixedStaticPair (taylorSamples (r+s+2) z) r s=
      z^(2*(r+s+1)+1)*((-1:ℂ)^(r+s+1)*(h (r+s+1):ℂ)*mixedSlope r s) := by
  rw [show r+s+2=(r+s+1)+1 by omega, mixed_taylor_sum, Finset.sum_range_succ]
  have hz : (∑ l ∈ Finset.range (r+s+1), ((-1:ℂ)^l*(h l:ℂ)*z^(2*l+1))*
      mixedStaticPair (monomialWeight (2*l+1)) r s)=0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [mixed_static_below r s l (Finset.mem_range.mp hl), mul_zero]
  rw [hz, zero_add, mixed_static_leading]
  ring

/-- Both weighted complete vectors are expanded using the SAME native remainder. -/
theorem mixed_response_expansion (r s : ℕ) :
    ∀ᶠ z : ℂ in nhds 0, mixedStaticPair (responseSamples z) r s=
      z^(2*(r+s+1)+1)*((-1:ℂ)^(r+s+1)*(h (r+s+1):ℂ)*mixedSlope r s+
        z^2*mixedStaticPair (remainderSamples (r+s+2) z) r s) := by
  filter_upwards [response_synthesis_expansion (r+s+2) (staticStencil (2*r)),
    response_synthesis_expansion (r+s+2) (staticStencil (2*s+1))] with z hr hs
  have he : mixedStaticPair (responseSamples z) r s=
      mixedStaticPair (taylorSamples (r+s+2) z) r s+
        z^(2*(r+s+2)+1)*mixedStaticPair (remainderSamples (r+s+2) z) r s := by
    change (inner ℂ _ (physicalCauchySynthesis (coefficientWeight (responseSamples z) _)))+
      (inner ℂ _ (physicalCauchySynthesis (coefficientWeight (responseSamples z) _)))=_
    rw [hr, hs]
    simp only [inner_add_right, inner_smul_right]
    unfold mixedStaticPair kernel sectorKernel sectorField coefficientStencil
    simp only [Bool.false_eq_true, ite_false]
    ring
  rw [he, mixed_taylor_cancellation,
    show 2*(r+s+2)+1=2*(r+s+1)+1+2 by omega, pow_add]
  ring

theorem remainder_samples_continuous (N j : ℕ) :
    ContinuousAt (fun z : ℂ => remainderSamples N z j) 0 := by
  have ht : Tendsto (fun z : ℂ => ((j+1:ℕ):ℂ)*z) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun z : ℂ => ((j+1:ℕ):ℂ)*z) 0 := by fun_prop
    simpa using hc.tendsto
  have hR := ((native_remainder_analytic N).continuousAt.tendsto.comp ht)
  simp only [remainderSamples]
  have hc : ContinuousAt (fun z : ℂ => nativeRemainder N (((j+1:ℕ):ℂ)*z)) 0 := by
    simpa only [ContinuousAt, Function.comp_def, mul_zero] using hR
  exact continuousAt_const.mul hc

theorem mixed_remainder_continuous (r s : ℕ) :
    ContinuousAt (fun z : ℂ => mixedStaticPair (remainderSamples (r+s+2) z) r s) 0 := by
  have hr := weighted_synthesis_continuous (fun z => remainderSamples (r+s+2) z)
    (staticStencil (2*r)) (remainder_samples_continuous (r+s+2))
  have hs := weighted_synthesis_continuous (fun z => remainderSamples (r+s+2) z)
    (staticStencil (2*s+1)) (remainder_samples_continuous (r+s+2))
  change ContinuousAt (fun z : ℂ => inner ℂ _
    (physicalCauchySynthesis (coefficientWeight (remainderSamples (r+s+2) z) _))+
    inner ℂ _ (physicalCauchySynthesis (coefficientWeight (remainderSamples (r+s+2) z) _))) 0
  exact (continuousAt_const.inner hs).add (continuousAt_const.inner hr)

/-- Normalized observation of the original ordered pair, not a modified source. -/
def normalizedMixedRay (r s k : ℕ) : ℂ :=
  (-Complex.I)*(-1:ℂ)^(r+s)*((k:ℂ)+1)^(2*(r+s+1)+1)*
    mixedStaticPair (responseSamples (radialStep k)) r s

theorem mixed_phase_leading (r s : ℕ) :
    (-Complex.I)*(-1:ℂ)^(r+s)*(-1:ℂ)^(r+s+1)=Complex.I := by
  have he : (-1:ℂ)^(r+s)*(-1:ℂ)^(r+s)=1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [pow_succ]
  linear_combination Complex.I*he

/-- Exact eventual expansion, with the complete native analytic remainder. -/
theorem normalized_mixed_expansion (r s : ℕ) :
    ∀ᶠ k : ℕ in atTop, normalizedMixedRay r s k=
      Complex.I*mixedSlope r s*(h (r+s+1):ℂ)+(radialStep k:ℂ)^2*
        ((-Complex.I)*(-1:ℂ)^(r+s)*mixedStaticPair (remainderSamples (r+s+2) (radialStep k)) r s) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  filter_upwards [ht.eventually (mixed_response_expansion r s)] with k hk
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  unfold normalizedMixedRay
  rw [hk]
  have hp := congrArg (fun z : ℂ => z^(2*(r+s+1)+1)) hi
  rw [mul_pow, one_pow] at hp
  calc
    _ = (-Complex.I)*(-1:ℂ)^(r+s)*
        (((k:ℂ)+1)^(2*(r+s+1)+1)*(radialStep k:ℂ)^(2*(r+s+1)+1))*
        ((-1:ℂ)^(r+s+1)*(h (r+s+1):ℂ)*mixedSlope r s+
          (radialStep k:ℂ)^2*mixedStaticPair (remainderSamples (r+s+2) (radialStep k)) r s) := by ring
    _ = _ := by
      rw [hp]
      linear_combination ((h (r+s+1):ℂ)*mixedSlope r s)*mixed_phase_leading r s

/-- Arbitrary independent even/odd orders, without any positivity hypothesis. -/
theorem normalized_mixed_tendsto (r s : ℕ) :
    Tendsto (normalizedMixedRay r s) atTop
      (nhds (Complex.I*mixedSlope r s*(h (r+s+1):ℂ))) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hR := (mixed_remainder_continuous r s).tendsto.comp ht
  have hlim := (tendsto_const_nhds (x:=Complex.I*mixedSlope r s*(h (r+s+1):ℂ))).add
    ((ht.pow 2).mul ((tendsto_const_nhds (x:=(-Complex.I)*(-1:ℂ)^(r+s))).mul hR))
  simp only [zero_pow (by decide : 2≠0), zero_mul, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [normalized_mixed_expansion r s] with k hk
  exact hk.symm

end
end CarryMixedImaginary
