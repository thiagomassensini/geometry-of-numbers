import SixSource
import SourceJets

namespace CarryMaterialVariation
open CarrySelfAdjointOperator CarryMovingRadial Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

def sixNodeWeight (u v : ℝ) (z : ℂ) : Fin 6 → ℂ :=
  ![40*(u:ℂ)^2*z^4-1040*(u:ℂ)*(v:ℂ)*z^6-(62/21)*(u:ℂ)*z^2+
      4800*(v:ℂ)^2*z^8+(320/7)*(v:ℂ)*z^4+1/21,
    -40*(u:ℂ)^2*z^4+1280*(u:ℂ)*(v:ℂ)*z^6+(85/21)*(u:ℂ)*z^2-
      2400*(v:ℂ)^2*z^8-(710/7)*(v:ℂ)*z^4-5/84,
    (120/7)*(u:ℂ)^2*z^4-720*(u:ℂ)*(v:ℂ)*z^6-(65/21)*(u:ℂ)*z^2+
      120*(v:ℂ)*z^4+5/126,
    -(20/7)*(u:ℂ)^2*z^4+160*(u:ℂ)*(v:ℂ)*z^6+(92/63)*(u:ℂ)*z^2-
      80*(v:ℂ)*z^4-1/63,
    -(25/63)*(u:ℂ)*z^2+(200/7)*(v:ℂ)*z^4+5/1386,
    (1/21)*(u:ℂ)*z^2-(30/7)*(v:ℂ)*z^4-1/2772]

def sixKernel (u v : ℝ) (z : ℂ) : ℂ :=
  ∑ i : Fin 6, ∑ j : Fin 6, sixWeight u v z i*sixWeight u v z j*
    (-Complex.I*(completedNativeOperatorLogDerivative (Complex.I*((i:ℂ)+1)*z)+
      completedNativeOperatorLogDerivative (Complex.I*((j:ℂ)+1)*z))/((i:ℂ)+(j:ℂ)+2))

def sixEnergy (u v : ℝ) (z : ℂ) : ℂ := sixKernel u v z/(14400*z^11)

def sixLimit (u v : ℝ) : ℝ := 2*(
  canonicalCompletedNativeLogDerivativeMoment 5+2*u*canonicalCompletedNativeLogDerivativeMoment 4+
  (u^2+2*v)*canonicalCompletedNativeLogDerivativeMoment 3+
  2*u*v*canonicalCompletedNativeLogDerivativeMoment 2+v^2*canonicalCompletedNativeLogDerivativeMoment 1)

def sixCorrection (u v : ℝ) : ℝ :=
  -10*v^2*canonicalCompletedNativeLogDerivativeMoment 2-
    168*u*v*canonicalCompletedNativeLogDerivativeMoment 3-
    60*(u^2+14*v)*canonicalCompletedNativeLogDerivativeMoment 4-
    484*u*canonicalCompletedNativeLogDerivativeMoment 5-182*canonicalCompletedNativeLogDerivativeMoment 6

theorem six_kernel_reduction (u v : ℝ) (z : ℂ) :
    sixKernel u v z=∑ j : Fin 6, sixNodeWeight u v z j*
      (-Complex.I*completedNativeOperatorLogDerivative (Complex.I*((j:ℂ)+1)*z)) := by
  norm_num [sixKernel,sixWeight,sixNodeWeight,Fin.sum_univ_succ]
  ring

theorem source_taylor_fourteen (z : ℂ) :
    (∑ i ∈ Finset.range 14, (z^i/(i.factorial:ℂ)) •
      iteratedDeriv i completedNativeOperatorLogDerivative 0)=
      ∑ n ∈ Finset.range 7, z^(2*n+1)*(2*(canonicalCompletedNativeLogDerivativeMoment n:ℂ)) := by
  have ht (i : ℕ) : (z^i/(i.factorial:ℂ))*iteratedDeriv i completedNativeOperatorLogDerivative 0=
      z^i*CarryRadialFlow.tc completedNativeOperatorLogDerivative i := by unfold CarryRadialFlow.tc; ring
  simp_rw [smul_eq_mul,ht]
  have he0 := CarryRadialFlow.source_tc_even 0
  have he1 := CarryRadialFlow.source_tc_even 1
  have he2 := CarryRadialFlow.source_tc_even 2
  have he3 := CarryRadialFlow.source_tc_even 3
  have he4 := CarryRadialFlow.source_tc_even 4
  have he5 := CarryRadialFlow.source_tc_even 5
  have he6 := CarryRadialFlow.source_tc_even 6
  have ho0 := CarryRadialFlow.source_tc_odd 0
  have ho1 := CarryRadialFlow.source_tc_odd 1
  have ho2 := CarryRadialFlow.source_tc_odd 2
  have ho3 := CarryRadialFlow.source_tc_odd 3
  have ho4 := CarryRadialFlow.source_tc_odd 4
  have ho5 := CarryRadialFlow.source_tc_odd 5
  have ho6 := CarryRadialFlow.source_tc_odd 6
  norm_num [Finset.sum_range_succ] at he0 he1 he2 he3 he4 he5 he6 ho0 ho1 ho2 ho3 ho4 ho5 ho6 ⊢
  rw [he0,he1,he2,he3,he4,he5,he6,ho0,ho1,ho2,ho3,ho4,ho5,ho6]
  ring

/-- Exact six-source expansion: no crossing or source tail is truncated. -/
theorem six_exact_remainder (u v : ℝ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ z : ℂ in nhds 0,
      sixKernel u v z=14400*z^11*((sixLimit u v:ℂ)+
        (sixCorrection u v:ℂ)*z^2+z^3*R z) := by
  obtain ⟨G,hGa,hG⟩ := nativeSourceLogSlope_analyticAt.exists_eventuallyEq_sum_add_pow_mul 14
  let R : ℂ → ℂ := fun z =>
    z*(42*(canonicalCompletedNativeLogDerivativeMoment 3:ℂ)*(v:ℂ)^2+
      3948*(canonicalCompletedNativeLogDerivativeMoment 4:ℂ)*(u:ℂ)*(v:ℂ)+
      1254*(canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(u:ℂ)^2+
      65868*(canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(v:ℂ)+
      32032*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(u:ℂ))+
    z^3*(-170*(canonicalCompletedNativeLogDerivativeMoment 4:ℂ)*(v:ℂ)^2-
      75856*(canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(u:ℂ)*(v:ℂ)-
      22880*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(u:ℂ)^2-
      3649360*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(v:ℂ))+
    z^5*(682*(canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(v:ℂ)^2+
      1333332*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(u:ℂ)*(v:ℂ))+
    z^7*(-2730*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(v:ℂ)^2)+
    (Complex.I/14400)*(sixNodeWeight u v z 0*G (Complex.I*z)+
      16384*sixNodeWeight u v z 1*G (2*Complex.I*z)+
      4782969*sixNodeWeight u v z 2*G (3*Complex.I*z)+
      268435456*sixNodeWeight u v z 3*G (4*Complex.I*z)+
      6103515625*sixNodeWeight u v z 4*G (5*Complex.I*z)+
      78364164096*sixNodeWeight u v z 5*G (6*Complex.I*z))
  have hg (c : ℂ) : AnalyticAt ℂ (fun z => G (c*z)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  have hw (i : Fin 6) : AnalyticAt ℂ (fun z => sixNodeWeight u v z i) 0 := by
    fin_cases i <;> dsimp [sixNodeWeight] <;> fun_prop
  refine ⟨R,?_,?_⟩
  · have h0 := (hw 0).fun_mul (hg Complex.I)
    have h1 := ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (16384:ℂ)) 0).fun_mul (hw 1)).fun_mul (hg (2*Complex.I))
    have h2 := ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (4782969:ℂ)) 0).fun_mul (hw 2)).fun_mul (hg (3*Complex.I))
    have h3 := ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (268435456:ℂ)) 0).fun_mul (hw 3)).fun_mul (hg (4*Complex.I))
    have h4 := ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (6103515625:ℂ)) 0).fun_mul (hw 4)).fun_mul (hg (5*Complex.I))
    have h5 := ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (78364164096:ℂ)) 0).fun_mul (hw 5)).fun_mul (hg (6*Complex.I))
    apply AnalyticAt.fun_add
    · fun_prop
    · exact analyticAt_const.fun_mul (((((h0.fun_add h1).fun_add h2).fun_add h3).fun_add h4).fun_add h5)
  · have ht (c : ℂ) : Tendsto (fun z : ℂ => c*z) (nhds 0) (nhds 0) := by
      simpa using (tendsto_id : Tendsto (fun z : ℂ => z) (nhds 0) (nhds 0)).const_mul c
    filter_upwards [(ht Complex.I).eventually hG,(ht (2*Complex.I)).eventually hG,
      (ht (3*Complex.I)).eventually hG,(ht (4*Complex.I)).eventually hG,
      (ht (5*Complex.I)).eventually hG,(ht (6*Complex.I)).eventually hG] with z h1 h2 h3 h4 h5 h6
    rw [six_kernel_reduction]
    norm_num [Fin.sum_univ_succ]
    rw [mul_comm Complex.I (2:ℂ),mul_comm Complex.I (3:ℂ),mul_comm Complex.I (4:ℂ),
      mul_comm Complex.I (5:ℂ),mul_comm Complex.I (6:ℂ)]
    rw [h1,h2,h3,h4,h5,h6]
    simp only [source_taylor_fourteen]
    simp only [smul_eq_mul]
    dsimp [R,sixNodeWeight,sixLimit,sixCorrection]
    push_cast
    norm_num [Finset.sum_range_succ]
    ring_nf
    norm_num [Complex.I_pow_eq_pow_mod,Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]
    ring

theorem six_correction_tendsto (u v : ℝ) :
    Tendsto (fun k : ℕ => (sixEnergy u v (canonicalGreenJetStep k)-
      (sixLimit u v:ℂ))/canonicalGreenJetStep k^2) atTop (nhds (sixCorrection u v:ℂ)) := by
  obtain ⟨R,hRa,hR⟩ := six_exact_remainder u v
  have ht := canonicalGreenJetStep_tendsto_zero
  have hl : Tendsto (fun k : ℕ => (sixCorrection u v:ℂ)+
      canonicalGreenJetStep k*R (canonicalGreenJetStep k)) atTop (nhds (sixCorrection u v:ℂ)) := by
    simpa using tendsto_const_nhds.add (ht.mul (hRa.continuousAt.tendsto.comp ht))
  apply hl.congr'
  filter_upwards [ht.eventually hR] with k hk
  unfold sixEnergy
  rw [hk]
  have hs : canonicalGreenJetStep k≠0 := by
    unfold canonicalGreenJetStep
    apply inv_ne_zero
    exact_mod_cast (show (k:ℝ)+1≠0 by positivity)
  field_simp [hs]
  ring

end
end CarryMaterialVariation
