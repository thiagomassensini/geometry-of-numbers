import SectorExpansion
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

namespace CarryCriticalTfvd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem full_kernel_triple (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w : ℕ → ℂ) (a b c d e f : ℂ) :
    sectorKernel false eta h0 h1 w (triple a b c) (triple d e f) =
      conj a*(w 0*d/2+w 1*e/3+w 2*f/4) +
      conj b*(w 0*d/3+w 1*e/4+w 2*f/5) +
      conj c*(w 0*d/4+w 1*e/5+w 2*f/6) := by
  simp only [sectorKernel,sectorField,coefficientStencil,Bool.false_eq_true,ite_false,
    weight_triple,synthesis_triple,inner_add_left,inner_add_right,inner_smul_left,
    inner_smul_right,inner_completedNativeChiralCauchyFeature]
  norm_num
  ring

theorem full_spatial_constants (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    spatialU false eta h0 h1 (monomialWeight 1)=0 ∧
    spatialV false eta h0 h1 (monomialWeight 1)=0 ∧
    spatialW false eta h0 h1 (monomialWeight 1)=1/2 ∧
    spatialU false eta h0 h1 (monomialWeight 3)=0 ∧
    spatialV false eta h0 h1 (monomialWeight 3)=1 ∧
    spatialU false eta h0 h1 (monomialWeight 5)=1/2 := by
  norm_num [spatialU,spatialV,spatialW,curvatureInput,seedInput,full_kernel_triple,monomialWeight]

def canonicalQuadratic (a : ℝ) : ℝ := h 2-2*a*h 1+a^2*h 0

theorem full_poles_zero (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    poleFour false eta h0 h1=0 ∧ poleTwo false eta h0 h1 a=0 := by
  obtain ⟨hu1,hv1,_,hu3,_,_⟩ := full_spatial_constants eta h0 h1
  simp [poleFour,poleTwo,hu1,hv1,hu3]

theorem full_finite_part (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    finitePart false eta h0 h1 a=canonicalQuadratic a := by
  obtain ⟨_,_,hw1,_,hv3,hu5⟩ := full_spatial_constants eta h0 h1
  rw [finitePart,hw1,hv3,hu5]
  unfold canonicalQuadratic
  ring

/-- New sector resolution of the old finite total balance. One analytic
remainder controls BOTH sectors; all divergent coefficients cancel exactly. -/
theorem complete_tfvd_expansion :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
      (a : ℝ), ∀ᶠ k : ℕ in atTop,
      mixedEnergy eta h0 h1 k (criticalInput k a)=
        ((k : ℝ)+1)^4*poleFour true eta h0 h1 + ((k : ℝ)+1)^2*poleTwo true eta h0 h1 a +
        finitePart true eta h0 h1 a + radialStep k^2*sectorError true eta h0 h1 R a (radialStep k) ∧
      bulkBoundaryEnergy eta h0 h1 k (criticalInput k a)=
        -((k : ℝ)+1)^4*poleFour true eta h0 h1 - ((k : ℝ)+1)^2*poleTwo true eta h0 h1 a +
        (canonicalQuadratic a-finitePart true eta h0 h1 a) +
        radialStep k^2*(sectorError false eta h0 h1 R a (radialStep k)-
          sectorError true eta h0 h1 R a (radialStep k)) ∧
      fullEnergy k (criticalInput k a)=canonicalQuadratic a +
        radialStep k^2*sectorError false eta h0 h1 R a (radialStep k) := by
  obtain ⟨R,hR,he⟩ := sector_flux_exact_expansion
  refine ⟨R,hR,?_⟩
  intro eta h0 h1 a
  filter_upwards [he false eta h0 h1 a,he true eta h0 h1 a,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hf hm hr
  have hF (j : Fin 4) := (hr j).2.1
  have hd (j : ℕ) (hj : j<4) := radial_weight_difference k j (hr ⟨j,hj⟩).2.1 (hr ⟨j,hj⟩).2.2
  rw [← full_original_flux eta h0 h1 k a hF hd] at hf
  rw [← mixed_original_flux eta h0 h1 k a hF hd] at hm
  obtain ⟨hz4,hz2⟩ := full_poles_zero eta h0 h1 a
  rw [hz4,hz2,full_finite_part] at hf
  simp only [mul_zero,zero_add] at hf
  refine ⟨hm,?_,hf⟩
  have hs := full_split eta h0 h1 k (criticalInput k a) (critical_input_support k a) hd
  have hgb : bulkBoundaryEnergy eta h0 h1 k (criticalInput k a)=
      fullEnergy k (criticalInput k a)-mixedEnergy eta h0 h1 k (criticalInput k a) := by linarith
  rw [hgb,hf,hm]
  ring

theorem full_critical_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    Tendsto (fun k => fullEnergy k (criticalInput k a)) atTop (nhds (canonicalQuadratic a)) := by
  obtain ⟨R,hR,he⟩ := complete_tfvd_expansion
  have ht := radial_step_tendsto
  have hr := (sector_error_continuous false eta h0 h1 R hR a).tendsto.comp ht
  have hv := (tendsto_const_nhds (x := canonicalQuadratic a)).add ((ht.pow 2).mul hr)
  simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero] at hv
  apply hv.congr'
  filter_upwards [he eta h0 h1 a] with k hk
  exact hk.2.2.symm

theorem mixed_renormalized_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    Tendsto (fun k => mixedEnergy eta h0 h1 k (criticalInput k a)-
      ((k : ℝ)+1)^4*poleFour true eta h0 h1 - ((k : ℝ)+1)^2*poleTwo true eta h0 h1 a)
      atTop (nhds (finitePart true eta h0 h1 a)) := by
  apply (sector_finite_part_limit true eta h0 h1 a).congr'
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hr
  rw [mixed_original_flux eta h0 h1 k a (fun j => (hr j).2.1)
    (fun j hj => radial_weight_difference k j (hr ⟨j,hj⟩).2.1 (hr ⟨j,hj⟩).2.2)]

theorem bulk_boundary_renormalized_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    Tendsto (fun k => bulkBoundaryEnergy eta h0 h1 k (criticalInput k a)+
      ((k : ℝ)+1)^4*poleFour true eta h0 h1 + ((k : ℝ)+1)^2*poleTwo true eta h0 h1 a)
      atTop (nhds (canonicalQuadratic a-finitePart true eta h0 h1 a)) := by
  have ht := (full_critical_limit eta h0 h1 a).sub (mixed_renormalized_limit eta h0 h1 a)
  apply ht.congr'
  filter_upwards [radial_weight_difference_eventually 4] with k hk
  rw [full_split eta h0 h1 k _ (critical_input_support k a) hk]
  ring

def criticalParameter : ℝ := h 1/h 0

theorem canonical_quadratic_schur (hh : h 0≠0) :
    canonicalQuadratic criticalParameter=h 2-h 1^2/h 0 := by
  unfold canonicalQuadratic criticalParameter
  field_simp [hh]
  ring

/-- This is the old PR41 residual, now reached by the new complete TFVD
sector cancellation. Nonvanishing of the OLD block is the only gate here. -/
theorem critical_tfvd_schur_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (hh : h 0≠0) :
    Tendsto (fun k => fullEnergy k (criticalInput k criticalParameter))
      atTop (nhds (h 2-h 1^2/h 0)) := by
  rw [← canonical_quadratic_schur hh]
  exact full_critical_limit eta h0 h1 criticalParameter

/-- Existing scalar size-one Schur identity, reused to name the PR41 residual. -/
theorem first_schur_formula (m : ℕ → ℝ) :
    sourceMomentSchur m 0 1=m 2-m 1^2/m 0 := by
  simp [sourceMomentSchur,sourceMomentCoupling,sourceMomentMatrix,
    Matrix.inv_subsingleton,Matrix.mulVec,dotProduct,Ring.inverse_eq_inv]
  ring

theorem critical_tfvd_named_schur_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (hh : h 0≠0) :
    Tendsto (fun k => fullEnergy k (criticalInput k criticalParameter))
      atTop (nhds (sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 1)) := by
  rw [first_schur_formula]
  exact critical_tfvd_schur_limit eta h0 h1 hh

end
end CarryCriticalTfvd
