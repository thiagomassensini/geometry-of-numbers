import PhaseCompensation

namespace CarryNativePhase
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryMixedGreen CarryCompletedGreenBalance
open CarryMaterialResponseComparison Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem analytic_conjugate {f : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) :
    AnalyticAt ℝ (fun t => conj (f t)) 0 :=
  (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp hf

theorem source_normalized_analytic : AnalyticAt ℝ carryMaterialNormalizedResponse 0 := by
  have hF := baseTwoCanonicalResponse_analyticAt 0
  have hn : baseTwoCanonicalResponse 0 ≠ 0 := by
    rw [baseTwoCanonicalResponse_eq_dressing_mul_signal]
    exact mul_ne_zero (baseTwoCanonicalDressingScalar_ne_zero 0) carryMaterial_origin_signal_ne_zero
  have h := hF.deriv.neg.div (analyticAt_const.mul hF)
    (show 2*baseTwoCanonicalResponse 0 ≠ 0 from mul_ne_zero (by norm_num) hn)
  apply h.congr
  exact Filter.Eventually.of_forall (fun t => (carryMaterialNormalizedResponse_eq t).symm)

theorem source_reduced_analytic : AnalyticAt ℝ carryMaterialReducedResponse 0 := by
  have hA : AnalyticAt ℝ carryMaterialResponseAxis 0 := by
    obtain ⟨p,hp⟩ := source_normalized_analytic
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  have hS : AnalyticAt ℝ (dslope carryMaterialResponseAxis 0) 0 := by
    obtain ⟨p,hp⟩ := hA
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  have ha : carryMaterialResponseAxis 0 = (carryMaterialResponseScale:ℂ) := by
    rw [material_axis_zero, material_scale_eq]
  exact hS.div (analyticAt_const.mul hA) (by
    rw [ha]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr material_scale_pos.ne')
      (Complex.ofReal_ne_zero.mpr material_scale_pos.ne'))

theorem source_remainder_row_analytic (u : ℝ) :
    AnalyticAt ℝ (fun t => remainderCoefficient t u) 0 := by
  have hN := source_normalized_analytic
  have hNc := analytic_conjugate hN
  have hD := carryScalar_dslope_row_analytic source_reduced_analytic u
  have hR : AnalyticAt ℝ (fun t => (carryMaterialRealResidual t u:ℂ)) 0 := by
    have hh := (hNc.mul (analyticAt_const (v := carryMaterialNormalizedResponse u))).mul hD
    exact ((Complex.ofRealCLM.comp Complex.reCLM).analyticAt _).comp hh
  have hF := baseTwoCanonicalResponse_analyticAt 0
  have hFc := analytic_conjugate hF
  have hf := forcing_scalar_analytic 0
  have hfc := analytic_conjugate hf
  have hP : AnalyticAt ℝ (fun t : ℝ => ((carryMaterialResponseScale^2*t*u:ℝ):ℂ)) 0 := by
    have hh := ((analyticAt_const (v := (carryMaterialResponseScale:ℂ)^2)).mul
        (Complex.ofRealCLM.analyticAt 0)).mul (analyticAt_const (v := (u:ℂ)))
    change AnalyticAt ℝ (fun t : ℝ => (carryMaterialResponseScale:ℂ)^2*(t:ℂ)*(u:ℂ)) 0 at hh
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using hh
  unfold remainderCoefficient completedCoefficient
  simp_rw [carryMaterialForcingGreen_rank_one]
  exact ((((analyticAt_const.mul hP).mul hFc).mul analyticAt_const).mul hR).sub
    (((analyticAt_const.mul hfc).mul analyticAt_const).mul analyticAt_const)

theorem confluent_retained_row_analytic (u : ℝ) :
    AnalyticAt ℝ (fun t => confluentRetained t u) 0 := by
  have hD := carryScalar_dslope_row_analytic native_ratio_analytic u
  have hfc := analytic_conjugate (forcing_scalar_analytic 0)
  have hP : AnalyticAt ℝ (fun t : ℝ => ((carryMaterialResponseScale^2*t*u:ℝ):ℂ)) 0 := by
    have hh := ((analyticAt_const (v := (carryMaterialResponseScale:ℂ)^2)).mul
        (Complex.ofRealCLM.analyticAt 0)).mul (analyticAt_const (v := (u:ℂ)))
    change AnalyticAt ℝ (fun t : ℝ => (carryMaterialResponseScale:ℂ)^2*(t:ℂ)*(u:ℂ)) 0 at hh
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using hh
  exact ((hP.mul hfc).mul analyticAt_const).mul hD

theorem companion_row_analytic (u : ℝ) :
    AnalyticAt ℝ (fun t => companionCoefficient t u) 0 := by
  have hfc := analytic_conjugate (forcing_scalar_analytic 0)
  have hpc := analytic_conjugate (companion_probe_analytic 0)
  unfold companionCoefficient
  fun_prop

/-- This is an actual scalar confluence theorem for the compensated group,
not a choice of zero for a singular quotient. -/
theorem compensated_row_analytic (u : ℝ) :
    AnalyticAt ℝ (fun t => compensatedCoefficient t u) 0 :=
  ((source_remainder_row_analytic u).sub (companion_row_analytic u)).sub
    (confluent_retained_row_analytic u)

private theorem compensated_right_continuous (t : ℝ)
    (hN : DifferentiableAt ℝ carryMaterialNormalizedResponse t)
    (hR : DifferentiableAt ℝ carryMaterialReducedResponse t)
    (hχ : DifferentiableAt ℝ valueRatio t) :
    ContinuousAt (fun u => compensatedCoefficient t u) t := by
  have hdR : ContinuousAt (dslope carryMaterialReducedResponse t) t :=
    continuousAt_dslope_same.mpr hR
  have hdχ : ContinuousAt (dslope valueRatio t) t := continuousAt_dslope_same.mpr hχ
  have hNr := hN.continuousAt
  have hF := (baseTwoCanonicalResponse_analyticAt t).continuousAt
  have hf := (forcing_scalar_analytic t).continuousAt
  have hp := (companion_probe_analytic t).continuousAt
  have hfg : ContinuousAt (fun u => carryMaterialForcingGreenKernel t u) t :=
    (carryMaterialForcingGreen_continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
  unfold compensatedCoefficient remainderCoefficient completedCoefficient companionCoefficient
    confluentRetained retainedWeight carryMaterialRealResidual
  fun_prop

/-- Every diagonal point in a source-derived neighborhood has the actual
punctured Green limit. No individual singular channel is assigned zero. -/
theorem compensated_diagonal_confluence :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U,
      Tendsto (fun u : ℝ => compensatedGreen t u/((u-t:ℝ):ℂ))
        (nhdsWithin t ({t}ᶜ)) (nhds (compensatedCoefficient t t)) := by
  have hreg := source_normalized_analytic.eventually_analyticAt.and
    (source_reduced_analytic.eventually_analyticAt.and native_ratio_analytic.eventually_analyticAt)
  obtain ⟨V,hV,hVo,hV0⟩ := mem_nhds_iff.mp hreg
  obtain ⟨U,hUo,hU0,hU⟩ := compensated_source_factor
  refine ⟨U ∩ V,hUo.inter hVo,⟨hU0,hV0⟩,?_⟩
  intro t ht
  have hr := hV ht.2
  have hc := compensated_right_continuous t hr.1.differentiableAt
    hr.2.1.differentiableAt hr.2.2.differentiableAt
  apply (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({t}ᶜ : Set ℝ)))).congr'
  have hn0 : ∀ᶠ u : ℝ in nhds t, u ∈ U := hUo.mem_nhds ht.1
  have hn : ∀ᶠ u : ℝ in nhdsWithin t ({t}ᶜ), u ∈ U :=
    hn0.filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,self_mem_nhdsWithin] with u hu hne
  rw [hU t ht.1 u hu]
  exact (mul_div_cancel_left₀ _
    (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (show u ≠ t by simpa using hne)))).symm

/-- Independent left/right jet indices are transported by the proved
divided-difference identity. They are jets of χ, NOT canonical h moments. -/
theorem native_ratio_kernel_jet (p q : ℕ) :
    carryKernelJet (fun t u => dslope valueRatio t u) p q =
      carryScalarJetShift (p+q+1) valueRatio 0 := by
  have he : (fun u => carryScalarJetShift p (fun t => dslope valueRatio t u) 0) =
      carryScalarJetShift (p+1) valueRatio := by
    funext u
    have hh := (carryScalar_dslope_row_shift native_ratio_analytic p u).eq_of_nhds
    rw [carryScalarJetShift_succ]
    exact hh
  unfold carryKernelJet
  rw [he, carryScalarJetShift_add]
  congr 1
  omega

theorem native_ratio_two_offdiagonal_jets :
    carryKernelJet (fun t u => dslope valueRatio t u) 1 0 = phaseCoefficient ∧
    carryKernelJet (fun t u => dslope valueRatio t u) 0 1 = phaseCoefficient := by
  constructor <;> rw [native_ratio_kernel_jet] <;> exact phase_coefficient_is_native_jet

/-- Conditional obstruction for THIS isolated divided-difference kernel.
Nonzero native phase is not assumed or concluded elsewhere in this file. -/
theorem phase_obstructs_isolated_hermitian (hphase : phaseCoefficient.im ≠ 0) :
    ¬ (carryKernelJet (fun t u => dslope valueRatio t u) 1 0 =
      conj (carryKernelJet (fun t u => dslope valueRatio t u) 0 1)) := by
  rw [native_ratio_two_offdiagonal_jets.1,native_ratio_two_offdiagonal_jets.2]
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  exact hphase (by linarith)

theorem confluent_retained_centered {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ) :
    (∑ i, ∑ j, conj (centeredCoefficients c t i)*
      confluentRetained (centeredParameters t i) (centeredParameters u j)*centeredCoefficients d u j) =
    ∑ i, ∑ j, conj (c i)*confluentRetained (t i) (u j)*d j := by
  rw [Fin.sum_univ_succ]
  simp only [centeredCoefficients, centeredParameters, Fin.cons_zero, Fin.cons_succ,
    confluentRetained, retainedWeight, mul_zero, zero_mul, Complex.ofReal_zero,
    Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp

/-- Full centered confluence with the signed compensated physical group.
No phase, hidden coordinate, source crossing or canonical coefficient is lost. -/
theorem centered_confluent_balance {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ) :
    (∑ i, ∑ j, conj (c i)*confluentRetained (t i) (u j)*d j) +
      (∑ i, ∑ j, conj (centeredCoefficients c t i)*
        compensatedCoefficient (centeredParameters t i) (centeredParameters u j)*centeredCoefficients d u j) =
    ∑ i, ∑ j, conj (c i)*completedCoefficient (t i) (u j)*d j := by
  simp only [compensatedCoefficient, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [remainder_centered_bilinear, companion_centered_bilinear, confluent_retained_centered]
  ring

theorem canonical_confluent_pullback {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (t : Fin N → ℝ) (u : Fin M → ℝ)
    (ht : ∀ i, t i ≠ 0) (hu : ∀ j, u j ≠ 0)
    (hFt : ∀ i, baseTwoCanonicalResponse (t i) ≠ 0)
    (hFu : ∀ j, baseTwoCanonicalResponse (u j) ≠ 0) :
    (∑ i, ∑ j, conj (regularInput c t i)*confluentRetained (t i) (u j)*regularInput d u j) +
      (∑ i, ∑ j, conj (centeredCoefficients (regularInput c t) t i)*
        compensatedCoefficient (centeredParameters t i) (centeredParameters u j)*
          centeredCoefficients (regularInput d u) u j) =
      (2:ℂ)*(carryMaterialResponseScale:ℂ)^2*
        ∑ i, ∑ j, conj (c i)*(carryMaterialRealResidual (t i) (u j):ℂ)*d j := by
  rw [centered_confluent_balance, completed_coefficient_bilinear]
  simp_rw [regularInput_exact c t ht hFt, regularInput_exact d u hu hFu]

end
end CarryNativePhase
