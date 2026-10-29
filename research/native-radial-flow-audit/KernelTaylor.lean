import FlowJets

namespace CarryRadialFlow
open CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def mu (n : ℕ) : ℂ := tc flowResponse (2*n+1)
def flowJetWitness : ℂ := (49/1000000)*mu 1-(7/500)*mu 2+mu 3

/-- Complex analytic extension of REAL four-address test coefficients.
The two difference stencils are retained in the same four original addresses. -/
def radialWeight (h : ℂ) : Fin 4 → ℂ :=
  ![-1-(21/500)*h^2,3+(21/500)*h^2,-3,1]

def address : Fin 4 → ℂ := ![1,2,3,4]

/-- Full two-argument response kernel on the imaginary radial grid.
For real h the weights are real. No positive metric is postulated. -/
def fourFlowKernel (h : ℂ) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, radialWeight h i*radialWeight h j*
    (-Complex.I*(flowResponse (Complex.I*address i*h)+
      flowResponse (Complex.I*address j*h))/(address i+address j))

def nodeWeight (h : ℂ) : Fin 4 → ℂ :=
  ![(147/250000)*h^4+(91/5000)*h^2+1/10,
    -(147/500000)*h^4-(14/625)*h^2-1/10,
    (63/5000)*h^2+3/70,-(7/2500)*h^2-1/140]

/-- All sixteen crosses are summed before the scalar reduction. -/
theorem fourFlowKernel_reduction (h : ℂ) :
    fourFlowKernel h=∑ j : Fin 4, nodeWeight h j*
      (-Complex.I*flowResponse (Complex.I*address j*h)) := by
  norm_num [fourFlowKernel,nodeWeight,radialWeight,address,Fin.sum_univ_succ]
  ring

theorem flow_taylor_polynomial (z : ℂ) :
    (∑ i ∈ Finset.range 8, (z^i/(i.factorial:ℂ)) • iteratedDeriv i flowResponse 0)=
      z*mu 0+z^3*mu 1+z^5*mu 2+z^7*mu 3 := by
  have ht (i : ℕ) : (z^i/(i.factorial:ℂ))*iteratedDeriv i flowResponse 0=
      z^i*tc flowResponse i := by unfold tc; ring
  have h0 : tc flowResponse 0=0 := by simpa [flowJetPolynomial] using flow_first_eight (0:Fin 8)
  have h2 : tc flowResponse 2=0 := by simpa [flowJetPolynomial] using flow_first_eight (2:Fin 8)
  have h4 : tc flowResponse 4=0 := by simpa [flowJetPolynomial] using flow_first_eight (4:Fin 8)
  have h6 : tc flowResponse 6=0 := by simpa [flowJetPolynomial] using flow_first_eight (6:Fin 8)
  simp_rw [smul_eq_mul,ht]
  norm_num [Finset.sum_range_succ,h0,h2,h4,h6,mu]

/-- Exact factorization of the ACTUAL response. The whole analytic remainder
is retained; this is not a truncation of the source. -/
theorem fourFlowKernel_exact_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ h : ℂ in nhds 0,
      fourFlowKernel h=36*flowJetWitness*h^7+h^8*R h := by
  obtain ⟨G,hGa,hG⟩ := flow_analytic.exists_eventuallyEq_sum_add_pow_mul 8
  let R : ℂ → ℂ := fun h =>
    h*(-(441/50000)*mu 2+(2646/125)*mu 3)+h^3*((9261/250000)*mu 3)+
      nodeWeight h 0*(-Complex.I*G (Complex.I*h))+
      nodeWeight h 1*(-Complex.I*256*G (2*Complex.I*h))+
      nodeWeight h 2*(-Complex.I*6561*G (3*Complex.I*h))+
      nodeWeight h 3*(-Complex.I*65536*G (4*Complex.I*h))
  have hg1 : AnalyticAt ℂ (fun h => G (Complex.I*h)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  have hg2 : AnalyticAt ℂ (fun h => G (2*Complex.I*h)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  have hg3 : AnalyticAt ℂ (fun h => G (3*Complex.I*h)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  have hg4 : AnalyticAt ℂ (fun h => G (4*Complex.I*h)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  refine ⟨R,?_,?_⟩
  · have hw (i : Fin 4) : AnalyticAt ℂ (fun h => nodeWeight h i) 0 := by
      fin_cases i <;> dsimp [nodeWeight] <;> fun_prop
    have hp : AnalyticAt ℂ (fun h : ℂ =>
        h*(-(441/50000)*mu 2+(2646/125)*mu 3)+h^3*((9261/250000)*mu 3)) 0 := by fun_prop
    have h1 := (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => -Complex.I) 0).fun_mul hg1
    have h2 := (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => -Complex.I*256) 0).fun_mul hg2
    have h3 := (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => -Complex.I*6561) 0).fun_mul hg3
    have h4 := (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => -Complex.I*65536) 0).fun_mul hg4
    exact (((hp.fun_add ((hw 0).fun_mul h1)).fun_add ((hw 1).fun_mul h2)).fun_add
      ((hw 2).fun_mul h3)).fun_add ((hw 3).fun_mul h4)
  · have ht1 : Tendsto (fun h : ℂ => Complex.I*h) (nhds 0) (nhds 0) := by
      simpa using (tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul Complex.I
    have ht2 : Tendsto (fun h : ℂ => 2*Complex.I*h) (nhds 0) (nhds 0) := by
      simpa using (tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul (2*Complex.I)
    have ht3 : Tendsto (fun h : ℂ => 3*Complex.I*h) (nhds 0) (nhds 0) := by
      simpa using (tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul (3*Complex.I)
    have ht4 : Tendsto (fun h : ℂ => 4*Complex.I*h) (nhds 0) (nhds 0) := by
      simpa using (tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul (4*Complex.I)
    filter_upwards [ht1.eventually hG,ht2.eventually hG,ht3.eventually hG,ht4.eventually hG]
      with h h1 h2 h3 h4
    rw [fourFlowKernel_reduction]
    norm_num [Fin.sum_univ_succ,address,nodeWeight] at ⊢
    rw [mul_comm Complex.I (2:ℂ),mul_comm Complex.I (3:ℂ),mul_comm Complex.I (4:ℂ)]
    rw [h1,h2,h3,h4]
    simp only [flow_taylor_polynomial]
    dsimp [R,nodeWeight,flowJetWitness]
    ring_nf
    norm_num [Complex.I_pow_eq_pow_mod,Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]

theorem fourFlowKernel_normalized_tendsto :
    Tendsto (fun k : ℕ => fourFlowKernel (canonicalGreenJetStep k)/canonicalGreenJetStep k^7)
      atTop (nhds (36*flowJetWitness)) := by
  obtain ⟨R,hRa,hR⟩ := fourFlowKernel_exact_remainder
  have ht := canonicalGreenJetStep_tendsto_zero
  have hlim : Tendsto (fun k : ℕ => 36*flowJetWitness+
      canonicalGreenJetStep k*R (canonicalGreenJetStep k)) atTop (nhds (36*flowJetWitness)) := by
    simpa using tendsto_const_nhds.add (ht.mul (hRa.continuousAt.tendsto.comp ht))
  apply hlim.congr'
  filter_upwards [ht.eventually hR] with k hk
  rw [hk]
  have hs : canonicalGreenJetStep k≠0 := by
    unfold canonicalGreenJetStep
    apply inv_ne_zero
    exact_mod_cast (show (k:ℝ)+1≠0 by positivity)
  field_simp [hs]

end
end CarryRadialFlow
