import CrossRadialGreen
import Cancellation

namespace CarryCrossRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

/-- The literal first two native radial jets, at independent regularizations. -/
def firstCrossPair (k l : ℕ) : ℂ :=
  crossSignedPair k l (radialJetCoefficients k 0) (radialJetCoefficients l 1)

theorem first_cross_exact {α : Type*} {f : Filter α} (u v : α → ℕ)
    (hu : Tendsto u f atTop) (hv : Tendsto v f atTop) :
    ∀ᶠ a in f, firstCrossPair (u a) (v a)=
      -Complex.I*((v a:ℂ)+1)*(crossScale (u a) (v a):ℂ)*
        (responseReadout (2*(radialStep (v a):ℂ))/3-
          responseReadout (radialStep (v a))/2-responseReadout (radialStep (u a))/6) := by
  have he : nativeEvenProfile 0=triple 1 0 0 := by
    rw [native_profile_zero]; simp [seedInput,triple]
  have ho : nativeOddProfile 0=triple Complex.I (-Complex.I) 0 := by
    rw [odd_profile_zero]; simp [triple]
  filter_upwards [cross_mixed_exact u v hu hv {0} {0} (fun _ => 1) (fun _ => 1)] with a ha
  norm_num only [crossMixedPair, finiteJetSource, finiteOddJetSource, Finset.sum_singleton,
    Nat.mul_zero, zero_add, one_smul] at ha
  rw [radial_even_calibration (u a) 0, radial_odd_calibration (v a) 0] at ha
  norm_num only [Nat.mul_zero, zero_add, pow_zero, pow_one, one_smul] at ha
  rw [he,ho] at ha
  simp only [kernel_smul_left, kernel_smul_right, map_add, map_natCast, map_one] at ha
  unfold kernel at ha
  rw [full_kernel_triple, full_kernel_triple] at ha
  norm_num [responseSamples] at ha
  unfold firstCrossPair
  rw [radial_even_calibration (u a) 0, radial_odd_calibration (v a) 0]
  norm_num only [Nat.mul_zero, zero_add, pow_zero, pow_one, one_smul]
  rw [he,ho]
  linear_combination ha

theorem doubled_index_tendsto : Tendsto (fun k : ℕ => 2*k+1) atTop atTop :=
  tendsto_atTop_mono (fun k => by dsimp; omega) tendsto_id

theorem doubled_step (k : ℕ) : (radialStep (2*k+1):ℂ)=(radialStep k:ℂ)/2 := by
  unfold radialStep
  push_cast
  rw [show 2*(k:ℂ)+1+1=2*((k:ℂ)+1) by ring, mul_inv_rev]
  norm_num [div_eq_mul_inv]

theorem doubled_cross_scale (k : ℕ) : crossScale k (2*k+1)=Real.sqrt 2*((k:ℝ)+1) := by
  unfold crossScale
  rw [show ((2*k+1:ℕ):ℝ)+1=2*((k:ℝ)+1) by push_cast; ring,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  calc
    _ = Real.sqrt 2*(Real.sqrt ((k:ℝ)+1))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)]

/-- A path through the original source, not a reweighted kernel. -/
def doubledFirstPair (k : ℕ) : ℂ := firstCrossPair k (2*k+1)

theorem doubled_first_exact :
    ∀ᶠ k : ℕ in atTop, doubledFirstPair k=
      Complex.I*(Real.sqrt 2:ℂ)*((k:ℂ)+1)^2*
        (responseReadout ((radialStep k:ℂ)/2)-responseReadout (radialStep k)/3) := by
  filter_upwards [first_cross_exact (fun k : ℕ => k) (fun k => 2*k+1)
    tendsto_id doubled_index_tendsto] with k hk
  unfold doubledFirstPair
  rw [hk, doubled_step, doubled_cross_scale]
  have he : 2*((radialStep k:ℂ)/2)=(radialStep k:ℂ) := by ring
  rw [he]
  push_cast
  ring

/-- Coefficients of the ORIGINAL path; neither is supplied as a sign hypothesis. -/
def doubledLeading : ℂ := Complex.I*(Real.sqrt 2:ℂ)*(h 0:ℂ)/6
def doubledNext : ℂ := 5*Complex.I*(Real.sqrt 2:ℂ)*(h 1:ℂ)/24

/-- The SAME native remainder at both addresses survives the exact expansion. -/
def doubledRemainder (z : ℂ) : ℂ :=
  Complex.I*(Real.sqrt 2:ℂ)*(nativeRemainder 2 (z/2)/32-nativeRemainder 2 z/3)

theorem doubled_remainder_continuous : ContinuousAt doubledRemainder 0 := by
  have hR := (native_remainder_analytic 2).continuousAt
  have hh : ContinuousAt (fun z : ℂ => nativeRemainder 2 (z/2)) 0 := by
    exact hR.comp_of_eq (show ContinuousAt (fun z : ℂ => z/2) 0 by fun_prop) (by simp)
  unfold doubledRemainder
  exact continuousAt_const.mul ((hh.div_const 32).sub (hR.div_const 3))

/-- The scale is derived with the native analytic tail and original crossed state. -/
theorem doubled_scaled_expansion :
    ∀ᶠ k : ℕ in atTop, (radialStep k:ℂ)*doubledFirstPair k=
      doubledLeading+(radialStep k:ℂ)^2*doubledNext+
        (radialStep k:ℂ)^4*doubledRemainder (radialStep k) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hhalf : Tendsto (fun k : ℕ => (radialStep k:ℂ)/2) atTop (nhds 0) := by
    simpa using ht.div_const 2
  have hp (z : ℂ) : oddTaylor 2 z=(h 0:ℂ)*z-(h 1:ℂ)*z^3 := by
    norm_num [oddTaylor, Finset.sum_range_succ]; ring
  filter_upwards [doubled_first_exact, ht.eventually (native_response_expansion 2),
    hhalf.eventually (native_response_expansion 2)] with k hk hq hh
  rw [hp] at hq hh
  rw [hk,hq,hh]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  have hi2 := congrArg (fun z : ℂ => z^2) hi
  simp only [mul_pow,one_pow] at hi2
  unfold doubledLeading doubledNext doubledRemainder
  norm_num only [show 2*2+1=5 by decide]
  linear_combination (Complex.I*(Real.sqrt 2:ℂ)*(h 0:ℂ)/6+
    (radialStep k:ℂ)^2*(5*Complex.I*(Real.sqrt 2:ℂ)*(h 1:ℂ)/24)+
    (radialStep k:ℂ)^4*(Complex.I*(Real.sqrt 2:ℂ)*
      (nativeRemainder 2 ((radialStep k:ℂ)/2)/32-nativeRemainder 2 (radialStep k)/3)))*hi2

/-- The uncancelled term grows as k+1; subtraction below is only a diagnostic
identity. It does not replace the original physical source or pairing. -/
theorem doubled_unscaled_expansion :
    ∀ᶠ k : ℕ in atTop, doubledFirstPair k=
      ((k:ℂ)+1)*doubledLeading+(radialStep k:ℂ)*doubledNext+
        (radialStep k:ℂ)^3*doubledRemainder (radialStep k) := by
  filter_upwards [doubled_scaled_expansion] with k hk
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  linear_combination ((k:ℂ)+1)*hk-doubledFirstPair k*hi+
    (radialStep k:ℂ)*doubledNext*hi+
    (radialStep k:ℂ)^3*doubledRemainder (radialStep k)*hi

theorem doubled_scaled_tendsto :
    Tendsto (fun k : ℕ => (radialStep k:ℂ)*doubledFirstPair k) atTop (nhds doubledLeading) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hR := doubled_remainder_continuous.tendsto.comp ht
  have hl := ((tendsto_const_nhds (x:=doubledLeading)).add
    ((ht.pow 2).mul_const doubledNext)).add ((ht.pow 4).mul hR)
  simp only [zero_pow (by decide : 2≠0),zero_pow (by decide : 4≠0),
    zero_mul,add_zero] at hl
  apply hl.congr'
  filter_upwards [doubled_scaled_expansion] with k hk
  exact hk.symm

theorem doubled_next_tendsto :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*(doubledFirstPair k-((k:ℂ)+1)*doubledLeading))
      atTop (nhds doubledNext) := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hR := doubled_remainder_continuous.tendsto.comp ht
  have hl := (tendsto_const_nhds (x:=doubledNext)).add ((ht.pow 2).mul hR)
  simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero] at hl
  apply hl.congr'
  filter_upwards [doubled_unscaled_expansion] with k hk
  rw [hk]
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  simp only [Function.comp_def]
  linear_combination -(doubledNext+(radialStep k:ℂ)^2*doubledRemainder (radialStep k))*hi

theorem doubled_green_scaled_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => (radialStep k:ℂ)*crossGreenPair eta h0 h1 k (2*k+1)
      (radialJetCoefficients k 0) (radialJetCoefficients (2*k+1) 1)) atTop (nhds doubledLeading) := by
  apply doubled_scaled_tendsto.congr'
  filter_upwards [] with k
  rw [cross_green_eq_original]
  rfl

end
end CarryCrossRadial
