import FiniteEvaluationError

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CarryC3Gamma CPFormal.Analytic.Cp
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def convolution (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), a j*b (n-j)

theorem phased_product {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (a b : ℕ → ℝ) (ha : ∀ n, sourceJet n f=Complex.I^n*(a n:ℂ))
    (hb : ∀ n, sourceJet n g=Complex.I^n*(b n:ℂ)) (n : ℕ) :
    sourceJet n (fun w => f w*g w)=Complex.I^n*(convolution a b n:ℂ) := by
  rw [jet_mul hf hg]
  simp_rw [ha,hb]
  unfold convolution
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show Complex.I^n=Complex.I^j*Complex.I^(n-j) by rw [← pow_add,Nat.add_sub_of_le hjn]]
  ring

def reciprocalJet (c : ℕ → ℝ) : (n : ℕ) → ℝ
  | 0 => (c 0)⁻¹
  | n+1 => -(∑ j : Fin (n+1), reciprocalJet c j.val*c (n+1-j.val))/c 0
termination_by n => n

theorem phased_reciprocal {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0≠0)
    (c : ℕ → ℝ) (hc : ∀ n, sourceJet n f=Complex.I^n*(c n:ℂ)) (r : ℕ) :
    sourceJet r (fun w => (f w)⁻¹)=Complex.I^r*(reciprocalJet c r:ℂ) := by
  have hc0 : f 0=(c 0:ℂ) := by simpa [sourceJet] using hc 0
  have hcz : c 0≠0 := by intro hh; rw [hh,Complex.ofReal_zero] at hc0; exact hf0 hc0
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [sourceJet,reciprocalJet,hc0]
    | succ n =>
      have hlocal : (fun w => (f w)⁻¹*f w) =ᶠ[nhds (0:ℂ)] (fun _ => (1:ℂ)) := by
        filter_upwards [hf.continuousAt.eventually_ne hf0] with w hw
        exact inv_mul_cancel₀ hw
      have hz : sourceJet (n+1) (fun w => (f w)⁻¹*f w)=0 := by
        unfold sourceJet
        rw [hlocal.iteratedDeriv_eq]
        simp [iteratedDeriv_const]
      rw [jet_mul (f:=fun w => (f w)⁻¹) (g:=f) (hf.inv hf0) hf,Finset.sum_range_succ] at hz
      have hsum : (∑ j ∈ Finset.range (n+1), sourceJet j (fun w => (f w)⁻¹)*sourceJet (n+1-j) f)=
          Complex.I^(n+1)*((∑ j : Fin (n+1), reciprocalJet c j.val*c (n+1-j.val)):ℂ) := by
        rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
          (reciprocalJet c j:ℂ)*(c (n+1-j):ℂ)) (n+1)]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j<n+1 := Finset.mem_range.mp hj
        rw [ih j (by omega),hc]
        rw [show Complex.I^(n+1)=Complex.I^j*Complex.I^(n+1-j) by rw [← pow_add,Nat.add_sub_of_le (by omega)]]
        ring
      rw [hsum,Nat.sub_self,hc] at hz
      simp only [pow_zero,one_mul] at hz
      rw [reciprocalJet]
      push_cast
      rw [← mul_div_assoc]
      apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hcz)).2
      linear_combination hz

def polynomialRealJet (r : ℕ) : ℝ := if r=0 then -1/8 else if r=2 then 1/2 else 0
def exponentialRealJet (r : ℕ) : ℝ := Real.exp (-Real.log Real.pi/4)*(-Real.log Real.pi/2)^r/(r.factorial:ℝ)
def chartRealJet (r : ℕ) : ℝ :=
  (if r=0 then 1 else 0)-Real.exp (Real.log 3/2)*(-Real.log 3)^r/(r.factorial:ℝ)

def nativePolynomial (w : ℂ) : ℂ := (1/2:ℂ)*operatorHeightParameter w*(operatorHeightParameter w-1)
def nativeExponential (w : ℂ) : ℂ := Complex.exp (-(operatorHeightParameter w/2)*(Real.log Real.pi:ℂ))
def nativeChart (w : ℂ) : ℂ := cpChartFactor 3 (operatorHeightParameter w)

theorem polynomial_jet_formula (r : ℕ) :
    sourceJet r nativePolynomial=Complex.I^r*(polynomialRealJet r:ℂ) := by
  have he : nativePolynomial=(fun w : ℂ => (-1/8:ℂ)+(-1/2:ℂ)*w^2) := by
    funext w
    unfold nativePolynomial operatorHeightParameter
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [he,sourceJet_add r (fun _ => -1/8) (fun w => (-1/2:ℂ)*w^2) analyticAt_const (by fun_prop),
    jet_constant,jet_const_mul]
  have hp : sourceJet r (fun w : ℂ => w^2)=if r=2 then 1 else 0 := by
    unfold sourceJet
    rw [iteratedDeriv_fun_pow_zero]
    split_ifs with h
    · subst r; norm_num
    · simp
  rw [hp]
  unfold polynomialRealJet
  by_cases h0 : r=0
  · subst r; norm_num
  · by_cases h2 : r=2
    · subst r; norm_num
    · simp [h0,h2]

theorem exponential_jet_formula (r : ℕ) :
    sourceJet r nativeExponential=Complex.I^r*(exponentialRealJet r:ℂ) := by
  have he : nativeExponential=(fun w => (Real.exp (-Real.log Real.pi/4):ℂ)*
      Complex.exp ((Complex.I*(-(Real.log Real.pi:ℂ)/2))*w)) := by
    funext w
    unfold nativeExponential operatorHeightParameter
    rw [show -(((1/2:ℂ)+Complex.I*w)/2)*(Real.log Real.pi:ℂ)=
        ((-Real.log Real.pi/4:ℝ):ℂ)+(Complex.I*(-(Real.log Real.pi:ℂ)/2))*w by push_cast; ring,
      Complex.exp_add,← Complex.ofReal_exp]
  rw [he,jet_const_mul,jet_exp_linear]
  unfold exponentialRealJet
  push_cast
  rw [mul_pow]
  ring

theorem chart_jet_formula (r : ℕ) :
    sourceJet r nativeChart=Complex.I^r*(chartRealJet r:ℂ) := by
  have he : nativeChart=(fun w => 1-(Real.exp (Real.log 3/2):ℂ)*
      Complex.exp ((-Complex.I*(Real.log 3:ℂ))*w)) := by
    funext w
    unfold nativeChart cpChartFactor
    norm_num only [Nat.cast_ofNat]
    have hl : Complex.log 3=(Real.log 3:ℂ) := by
      simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_log (by norm_num : (0:ℝ)≤3)).symm
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0),hl]
    rw [show (Real.log 3:ℂ)*(1-operatorHeightParameter w)=
        ((Real.log 3/2:ℝ):ℂ)+(-Complex.I*(Real.log 3:ℂ))*w by unfold operatorHeightParameter; push_cast; ring,
      Complex.exp_add,← Complex.ofReal_exp]
  rw [he,jet_sub analyticAt_const (by fun_prop),jet_constant,jet_const_mul,jet_exp_linear]
  unfold chartRealJet
  push_cast
  have hh : -Complex.I*(Real.log 3:ℂ)=Complex.I*(-(Real.log 3:ℂ)) := by ring
  rw [hh,mul_pow]
  split_ifs with hr
  · subst r; simp
  · simp only [Complex.ofReal_zero,zero_sub]
    ring

def leftRealJet : ℕ → ℝ := convolution
  (convolution (convolution polynomialRealJet exponentialRealJet) (reciprocalJet chartRealJet)) (headRealJet 64)

theorem finite_left_jet_formula (r : ℕ) :
    sourceJet r finiteLeft=Complex.I^r*(leftRealJet r:ℂ) := by
  have hp : AnalyticAt ℂ nativePolynomial 0 := by unfold nativePolynomial operatorHeightParameter; fun_prop
  have he : AnalyticAt ℂ nativeExponential 0 := by unfold nativeExponential operatorHeightParameter; fun_prop
  have hc : AnalyticAt ℂ nativeChart 0 := canonicalC3ChartFactorHeight_analyticAt_zero
  have hcn : nativeChart 0≠0 := canonicalC3ChartFactorHeight_ne_zero zero_mem_completedNativeHeightDomain
  have hformula : finiteLeft=(fun w =>
      ((nativePolynomial w*nativeExponential w)*(nativeChart w)⁻¹)*acceleratedC3Head 64 w) := by
    funext w
    rfl
  rw [hformula]
  exact phased_product ((hp.mul he).mul (hc.inv hcn)) (accelerated_c3_head_analytic 64) _ _
    (phased_product (hp.mul he) (hc.inv hcn) _ _
      (phased_product hp he _ _ polynomial_jet_formula exponential_jet_formula)
      (phased_reciprocal hc hcn _ chart_jet_formula)) (accelerated_head_jet_formula 64) r

def finiteCompletedRealJet (r : Fin 7) : ℝ :=
  ∑ j ∈ Finset.range (r.val+1), leftRealJet j*(gammaRealReference ⟨r.val-j,by omega⟩:ℝ)

theorem finite_completed_jet_formula (r : Fin 7) :
    finiteCompletedJet r=Complex.I^r.val*(finiteCompletedRealJet r:ℂ) := by
  unfold finiteCompletedJet finiteCompletedRealJet
  simp_rw [finite_left_jet_formula,gammaReference]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r.val := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show Complex.I^r.val=Complex.I^j*Complex.I^(r.val-j) by rw [← pow_add,Nat.add_sub_of_le hjr]]
  ring

end
end CarryC3Tail
