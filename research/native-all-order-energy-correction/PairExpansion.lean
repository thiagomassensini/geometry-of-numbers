import ResponseExpansion

namespace CarryEnergyCorrection
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem pair_taylor_sum (N r s : ℕ) (z : ℂ) :
    pairKernel (taylorSamples N z) r s=
      ∑ l ∈ Finset.range N, ((-1:ℂ)^l*(h l:ℂ)*z^(2*l+1))*
        pairKernel (monomialWeight (2*l+1)) r s := by
  unfold taylorSamples pairKernel
  rw [kernel_sum_weight, kernel_sum_weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [kernel_scale, kernel_scale]
  ring

theorem pair_below (r s l : ℕ) (hl : l < r+s) :
    pairKernel (monomialWeight (2*l+1)) r s=0 :=
  native_below (1/2) (by norm_num) (by norm_num) r s (2*l+1) ⟨l,rfl⟩ (by omega)

theorem pair_leading (r s : ℕ) :
    pairKernel (monomialWeight (2*(r+s)+1)) r s=(-1:ℂ)^(r+s) := by
  rw [show 2*(r+s)+1=2*r+2*s+1 by omega]
  exact native_leading (1/2) (by norm_num) (by norm_num) r s

theorem pair_correction (r s : ℕ) :
    pairKernel (monomialWeight (2*(r+s+1)+1)) r s=
      (-1:ℂ)^(r+s)*spatialCorrection (2*r) (2*s) := by
  rw [show 2*(r+s+1)+1=2*r+2*s+3 by omega]
  exact native_first_correction (1/2) (by norm_num) (by norm_num) r s

/-- The TWO surviving Taylor contributions, before scalar readout. -/
theorem pair_taylor_cancellation (r s : ℕ) (z : ℂ) :
    pairKernel (taylorSamples (r+s+2) z) r s=
      z^(2*(r+s)+1)*((h (r+s):ℂ)-z^2*
        spatialCorrection (2*r) (2*s)*(h (r+s+1):ℂ)) := by
  rw [pair_taylor_sum, Finset.sum_range_succ, Finset.sum_range_succ]
  have hz : (∑ l ∈ Finset.range (r+s), ((-1:ℂ)^l*(h l:ℂ)*z^(2*l+1))*
      pairKernel (monomialWeight (2*l+1)) r s)=0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [pair_below r s l (Finset.mem_range.mp hl), mul_zero]
  rw [hz, zero_add, pair_leading, pair_correction]
  have hs : (-1:ℂ)^(r+s)*(-1:ℂ)^(r+s)=1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [pow_succ (-1:ℂ) (r+s)]
  have he : z^(2*(r+s+1)+1)=z^(2*(r+s)+1)*z^2 := by rw [← pow_add]; congr 1
  rw [he]
  linear_combination ((h (r+s):ℂ)*z^(2*(r+s)+1)-
    z^(2*(r+s)+1)*z^2*spatialCorrection (2*r) (2*s)*(h (r+s+1):ℂ))*hs

/-- Expansion of the SAME complete complex synthesis in each argument. -/
theorem pair_response_expansion (r s : ℕ) :
    ∀ᶠ z : ℂ in nhds 0,
      pairKernel (responseSamples z) r s=
        z^(2*(r+s)+1)*((h (r+s):ℂ)-z^2*spatialCorrection (2*r) (2*s)*
          (h (r+s+1):ℂ)+z^4*pairKernel (remainderSamples (r+s+2) z) r s) := by
  filter_upwards [response_synthesis_expansion (r+s+2) (nativeEvenProfile r),
    response_synthesis_expansion (r+s+2) (nativeEvenProfile s)] with z hr hs
  have he : pairKernel (responseSamples z) r s=
      pairKernel (taylorSamples (r+s+2) z) r s+
        z^(2*(r+s+2)+1)*pairKernel (remainderSamples (r+s+2) z) r s := by
    change (inner ℂ _ (physicalCauchySynthesis (coefficientWeight (responseSamples z) _)))+
      (inner ℂ _ (physicalCauchySynthesis (coefficientWeight (responseSamples z) _)))=_
    rw [hr, hs]
    simp only [inner_add_right, inner_smul_right]
    unfold pairKernel kernel sectorKernel sectorField coefficientStencil
    simp only [Bool.false_eq_true, ite_false]
    ring
  rw [he, pair_taylor_cancellation,
    show 2*(r+s+2)+1=(2*(r+s)+1)+4 by omega, pow_add]
  ring

theorem weighted_synthesis_sum (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    physicalCauchySynthesis (coefficientWeight w c)=
      ∑ j ∈ c.support, (w j*c j) • completedNativeChiralCauchyFeature j := by
  classical
  have hs : coefficientWeight w c ∈ Finsupp.supported ℂ ℂ (↑c.support : Set ℕ) := by
    intro j hj
    exact Finsupp.mem_support_iff.mpr
      (mul_ne_zero_iff.mp (Finsupp.mem_support_iff.mp hj)).2
  unfold physicalCauchySynthesis
  rw [Finsupp.linearCombination_apply_of_mem_supported (R:=ℂ) hs]
  simp only [coefficient_weight_apply]

theorem weighted_synthesis_continuous (w : ℂ → ℕ → ℂ) (c : ℕ →₀ ℂ)
    (hw : ∀ j, ContinuousAt (fun z => w z j) 0) :
    ContinuousAt (fun z => physicalCauchySynthesis (coefficientWeight (w z) c)) 0 := by
  simp only [weighted_synthesis_sum]
  have hc (S : Finset ℕ) : ContinuousAt (fun z =>
      ∑ j ∈ S, (w z j*c j) • completedNativeChiralCauchyFeature j) 0 := by
    classical
    induction S using Finset.induction_on with
    | empty => simp; fun_prop
    | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((hw a).mul continuousAt_const).smul continuousAt_const |>.add ih
  exact hc c.support

theorem pair_remainder_continuous (r s : ℕ) :
    ContinuousAt (fun z : ℂ => pairKernel (remainderSamples (r+s+2) z) r s) 0 := by
  have hw (j : ℕ) : ContinuousAt (fun z : ℂ => remainderSamples (r+s+2) z j) 0 := by
    have ht : Tendsto (fun z : ℂ => ((j+1:ℕ):ℂ)*z) (nhds 0) (nhds 0) := by
      have hc : ContinuousAt (fun z : ℂ => ((j+1:ℕ):ℂ)*z) 0 := by fun_prop
      simpa using hc.tendsto
    have hR := ((native_remainder_analytic (r+s+2)).continuousAt.tendsto.comp ht)
    simp only [remainderSamples]
    have hc : ContinuousAt (fun z : ℂ => nativeRemainder (r+s+2) (((j+1:ℕ):ℂ)*z)) 0 := by
      simpa only [ContinuousAt, Function.comp_def, mul_zero] using hR
    exact continuousAt_const.mul hc
  have hr := weighted_synthesis_continuous (fun z => remainderSamples (r+s+2) z) (nativeEvenProfile r) hw
  have hs := weighted_synthesis_continuous (fun z => remainderSamples (r+s+2) z) (nativeEvenProfile s) hw
  change ContinuousAt (fun z : ℂ => inner ℂ _
    (physicalCauchySynthesis (coefficientWeight (remainderSamples (r+s+2) z) _))+
    inner ℂ _ (physicalCauchySynthesis (coefficientWeight (remainderSamples (r+s+2) z) _))) 0
  exact (continuousAt_const.inner hs).add (continuousAt_const.inner hr)

/-- Normalized original two-input flux, before its final real readout. -/
def normalizedPair (r s k : ℕ) : ℂ :=
  ((k:ℂ)+1)^(2*(r+s)+1)*pairKernel (responseSamples (radialStep k)) r s

theorem normalized_pair_expansion (r s : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      normalizedPair r s k=(h (r+s):ℂ)-(radialStep k:ℂ)^2*
        spatialCorrection (2*r) (2*s)*(h (r+s+1):ℂ)+(radialStep k:ℂ)^4*
          pairKernel (remainderSamples (r+s+2) (radialStep k)) r s := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  filter_upwards [ht.eventually (pair_response_expansion r s)] with k hk
  unfold normalizedPair
  rw [hk]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  rw [← mul_assoc, ← mul_pow, hi, one_pow, one_mul]

theorem normalized_pair_correction_tendsto (r s : ℕ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)^2*(normalizedPair r s k-(h (r+s):ℂ)))
      atTop (nhds (-spatialCorrection (2*r) (2*s)*(h (r+s+1):ℂ))) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hR := (pair_remainder_continuous r s).tendsto.comp ht
  have hlim := (tendsto_const_nhds (x := -spatialCorrection (2*r) (2*s)*(h (r+s+1):ℂ))).add
    ((ht.pow 2).mul hR)
  simp only [zero_pow (by decide : 2≠0), zero_mul, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [normalized_pair_expansion r s] with k hk
  rw [hk]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  have hi2 := congrArg (fun z : ℂ => z^2) hi
  simp only [mul_pow, one_pow] at hi2
  simp only [Function.comp_def]
  linear_combination (spatialCorrection (2*r) (2*s)*(h (r+s+1):ℂ))*hi2-
    (radialStep k:ℂ)^2*pairKernel (remainderSamples (r+s+2) (radialStep k)) r s*hi2

end
end CarryEnergyCorrection
