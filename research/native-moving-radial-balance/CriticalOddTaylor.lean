import SourceJets
import CriticalJetTransport

namespace CarryMovingRadial
open CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def criticalWeight (a : ℝ) (z : ℂ) : Fin 4 → ℂ :=
  ![-1-6*(a:ℂ)*z^2,3+6*(a:ℂ)*z^2,-3,1]

def criticalNodeWeight (a : ℝ) (z : ℂ) : Fin 4 → ℂ :=
  ![12*(a:ℂ)^2*z^4+(13/5)*(a:ℂ)*z^2+1/10,
    -6*(a:ℂ)^2*z^4-(16/5)*(a:ℂ)*z^2-1/10,
    (9/5)*(a:ℂ)*z^2+3/70,-(2/5)*(a:ℂ)*z^2-1/140]

def criticalKernel (a : ℝ) (z : ℂ) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, criticalWeight a z i*criticalWeight a z j*
    (-Complex.I*(completedNativeOperatorLogDerivative (Complex.I*((i:ℂ)+1)*z)+
      completedNativeOperatorLogDerivative (Complex.I*((j:ℂ)+1)*z))/((i:ℂ)+(j:ℂ)+2))

def criticalEnergy (a : ℝ) (z : ℂ) : ℂ := criticalKernel a z/(36*z^7)

def criticalLimit (a : ℝ) : ℝ := 2*(canonicalCompletedNativeLogDerivativeMoment 3-
  2*a*canonicalCompletedNativeLogDerivativeMoment 2+a^2*canonicalCompletedNativeLogDerivativeMoment 1)

def criticalCorrection (a : ℝ) : ℝ :=
  -10*a^2*canonicalCompletedNativeLogDerivativeMoment 2+
    168*a*canonicalCompletedNativeLogDerivativeMoment 3-60*canonicalCompletedNativeLogDerivativeMoment 4

theorem critical_kernel_reduction (a : ℝ) (z : ℂ) :
    criticalKernel a z=∑ j : Fin 4, criticalNodeWeight a z j*
      (-Complex.I*completedNativeOperatorLogDerivative (Complex.I*((j:ℂ)+1)*z)) := by
  norm_num [criticalKernel,criticalWeight,criticalNodeWeight,Fin.sum_univ_succ]
  ring

theorem source_taylor_ten (z : ℂ) :
    (∑ i ∈ Finset.range 10, (z^i/(i.factorial:ℂ)) •
      iteratedDeriv i completedNativeOperatorLogDerivative 0)=
      ∑ n ∈ Finset.range 5, z^(2*n+1)*(2*(canonicalCompletedNativeLogDerivativeMoment n:ℂ)) := by
  have ht (i : ℕ) : (z^i/(i.factorial:ℂ))*iteratedDeriv i completedNativeOperatorLogDerivative 0=
      z^i*CarryRadialFlow.tc completedNativeOperatorLogDerivative i := by unfold CarryRadialFlow.tc; ring
  simp_rw [smul_eq_mul,ht]
  have he0 := CarryRadialFlow.source_tc_even 0
  have he1 := CarryRadialFlow.source_tc_even 1
  have he2 := CarryRadialFlow.source_tc_even 2
  have he3 := CarryRadialFlow.source_tc_even 3
  have he4 := CarryRadialFlow.source_tc_even 4
  have ho0 := CarryRadialFlow.source_tc_odd 0
  have ho1 := CarryRadialFlow.source_tc_odd 1
  have ho2 := CarryRadialFlow.source_tc_odd 2
  have ho3 := CarryRadialFlow.source_tc_odd 3
  have ho4 := CarryRadialFlow.source_tc_odd 4
  norm_num [Finset.sum_range_succ] at he0 he1 he2 he3 he4 ho0 ho1 ho2 ho3 ho4 ⊢
  rw [he0,he1,he2,he3,he4,ho0,ho1,ho2,ho3,ho4]
  ring

/-- Exact two-term expansion of the SAME full four-address response.
The whole analytic tail survives in R. No pivot sign is assumed. -/
theorem critical_exact_remainder (a : ℝ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ z : ℂ in nhds 0,
      criticalKernel a z=36*z^7*((criticalLimit a:ℂ)+
        (criticalCorrection a:ℂ)*z^2+z^3*R z) := by
  obtain ⟨G,hGa,hG⟩ := nativeSourceLogSlope_analyticAt.exists_eventuallyEq_sum_add_pow_mul 10
  let R : ℂ → ℂ := fun z =>
    z*(42*(a:ℂ)^2*(canonicalCompletedNativeLogDerivativeMoment 3:ℂ)-
      3948*(a:ℂ)*(canonicalCompletedNativeLogDerivativeMoment 4:ℂ))+
    z^3*(-170*(a:ℂ)^2*(canonicalCompletedNativeLogDerivativeMoment 4:ℂ))+
    (Complex.I/36)*(criticalNodeWeight a z 0*G (Complex.I*z)+
      1024*criticalNodeWeight a z 1*G (2*Complex.I*z)+
      59049*criticalNodeWeight a z 2*G (3*Complex.I*z)+
      1048576*criticalNodeWeight a z 3*G (4*Complex.I*z))
  have hg (c : ℂ) : AnalyticAt ℂ (fun z => G (c*z)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  have hw (i : Fin 4) : AnalyticAt ℂ (fun z => criticalNodeWeight a z i) 0 := by
    fin_cases i <;> dsimp [criticalNodeWeight] <;> fun_prop
  refine ⟨R,?_,?_⟩
  · have h0 := (hw 0).fun_mul (hg Complex.I)
    have h1 := ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1024:ℂ)) 0).fun_mul (hw 1)).fun_mul (hg (2*Complex.I))
    have h2 := ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (59049:ℂ)) 0).fun_mul (hw 2)).fun_mul (hg (3*Complex.I))
    have h3 := ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1048576:ℂ)) 0).fun_mul (hw 3)).fun_mul (hg (4*Complex.I))
    have hp : AnalyticAt ℂ (fun z : ℂ =>
        z*(42*(a:ℂ)^2*(canonicalCompletedNativeLogDerivativeMoment 3:ℂ)-
          3948*(a:ℂ)*(canonicalCompletedNativeLogDerivativeMoment 4:ℂ))+
        z^3*(-170*(a:ℂ)^2*(canonicalCompletedNativeLogDerivativeMoment 4:ℂ))) 0 := by fun_prop
    exact hp.fun_add (analyticAt_const.fun_mul (((h0.fun_add h1).fun_add h2).fun_add h3))
  · have ht (c : ℂ) : Tendsto (fun z : ℂ => c*z) (nhds 0) (nhds 0) := by
      simpa using (tendsto_id : Tendsto (fun z : ℂ => z) (nhds 0) (nhds 0)).const_mul c
    filter_upwards [(ht Complex.I).eventually hG,(ht (2*Complex.I)).eventually hG,
      (ht (3*Complex.I)).eventually hG,(ht (4*Complex.I)).eventually hG] with z h1 h2 h3 h4
    rw [critical_kernel_reduction]
    norm_num [Fin.sum_univ_succ]
    rw [mul_comm Complex.I (2:ℂ),mul_comm Complex.I (3:ℂ),mul_comm Complex.I (4:ℂ)]
    rw [h1,h2,h3,h4]
    simp only [source_taylor_ten]
    simp only [smul_eq_mul]
    dsimp [R,criticalNodeWeight,criticalLimit,criticalCorrection]
    push_cast
    norm_num [Finset.sum_range_succ]
    ring_nf
    norm_num [Complex.I_pow_eq_pow_mod,Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]
    ring

theorem critical_correction_tendsto (a : ℝ) :
    Tendsto (fun k : ℕ => (criticalEnergy a (canonicalGreenJetStep k)-
      (criticalLimit a:ℂ))/canonicalGreenJetStep k^2) atTop (nhds (criticalCorrection a:ℂ)) := by
  obtain ⟨R,hRa,hR⟩ := critical_exact_remainder a
  have ht := canonicalGreenJetStep_tendsto_zero
  have hl : Tendsto (fun k : ℕ => (criticalCorrection a:ℂ)+
      canonicalGreenJetStep k*R (canonicalGreenJetStep k)) atTop (nhds (criticalCorrection a:ℂ)) := by
    simpa using tendsto_const_nhds.add (ht.mul (hRa.continuousAt.tendsto.comp ht))
  apply hl.congr'
  filter_upwards [ht.eventually hR] with k hk
  unfold criticalEnergy
  rw [hk]
  have hs : canonicalGreenJetStep k≠0 := by
    unfold canonicalGreenJetStep
    apply inv_ne_zero
    exact_mod_cast (show (k:ℝ)+1≠0 by positivity)
  field_simp [hs]
  ring

end
end CarryMovingRadial
