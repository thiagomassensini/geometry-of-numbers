import ElementaryBoxes
import C3CompletionBounds

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CarryC3Gamma CPFormal.Analytic.Cp
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false

def boundaryWeight (k : Fin 12) : ℚ :=
  ![728/729,-1444/729,638/729,364/243,-815/243,880/243,-637/243,329/243,-121/243,91/729,-14/729,1/729] k

theorem boundary_stencil (f : ℕ → ℂ) (a : ℕ) :
    c3Boundary f a=∑ k : Fin 12, (boundaryWeight k:ℂ)*f (a+k.val) := by
  unfold c3Boundary
  simp only [fd,fwdDiff_iter_eq_sum_shift]
  norm_num [boundaryWeight,Fin.sum_univ_succ,Finset.sum_range_succ,zsmul_eq_mul,
    Nat.choose_succ_succ,Nat.add_assoc]
  ring

def sampleRealJet (n r : ℕ) : ℝ :=
  Real.exp (-Real.log n/2)*(-Real.log n)^r/(r.factorial:ℝ)

theorem sample_exp_formula (n : ℕ) (hn : 0 < n) (w : ℂ) :
    c3Sample n w=(Real.exp (-Real.log n/2):ℂ)*
      Complex.exp ((-Complex.I*(Real.log n:ℂ))*w) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [c3Sample,Complex.cpow_def_of_ne_zero hn0,← Complex.natCast_log]
  have he : (Real.log n:ℂ)*(-operatorHeightParameter w)=
      ((-Real.log n/2:ℝ):ℂ)+(-Complex.I*(Real.log n:ℂ))*w := by
    unfold operatorHeightParameter
    push_cast
    ring
  rw [he,Complex.exp_add,← Complex.ofReal_exp]

theorem sample_jet_formula (n : ℕ) (hn : 0 < n) (r : ℕ) :
    sourceJet r (c3Sample n)=Complex.I^r*(sampleRealJet n r:ℂ) := by
  have he : c3Sample n=(fun w => (Real.exp (-Real.log n/2):ℂ)*
      Complex.exp ((-Complex.I*(Real.log n:ℂ))*w)) := funext (sample_exp_formula n hn)
  rw [he,jet_const_mul,jet_exp_linear]
  unfold sampleRealJet
  push_cast
  have hh : -Complex.I*Complex.log (n:ℂ)=Complex.I*(-Complex.log (n:ℂ)) := by ring
  rw [hh,mul_pow]
  ring

theorem jet_constant (r : ℕ) (c : ℂ) :
    sourceJet r (fun _ : ℂ => c) = if r=0 then c else 0 := by
  cases r <;> simp [sourceJet,iteratedDeriv_const]

theorem jet_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (r : ℕ) :
    sourceJet r (fun w => f w-g w)=sourceJet r f-sourceJet r g := by
  unfold sourceJet
  change iteratedDeriv r (f-g) 0/(r.factorial:ℂ)=_
  rw [iteratedDeriv_sub hf.contDiffAt hg.contDiffAt,sub_div]

def headRealJet (M r : ℕ) : ℝ :=
  (if r=0 then 1 else 0)+
    (∑ m ∈ Finset.range M, (sampleRealJet (3*m+2) r-2*sampleRealJet (3*m+3) r+sampleRealJet (3*m+4) r))+
    ∑ k : Fin 12, (boundaryWeight k:ℝ)*sampleRealJet (3*M+2+k.val) r

theorem accelerated_head_jet_formula (M r : ℕ) :
    sourceJet r (acceleratedC3Head M)=Complex.I^r*(headRealJet M r:ℂ) := by
  have hs : acceleratedC3Head M=(fun w =>
      1+∑ m ∈ Finset.range M,
        (c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w)+
        ∑ k : Fin 12, (boundaryWeight k:ℂ)*c3Sample (3*M+2+k.val) w) := by
    funext w
    rw [acceleratedC3Head,finiteBracketedDirichletChart_three_eq_one_add_trace,
      finiteCanonicalBracketTrace,boundary_stencil]
    congr 2
    apply Finset.sum_congr rfl
    intro m hm
    rw [native_c3_cell_fd,fd_two]
    rw [show 3*m+2+2=3*m+4 by omega,show 3*m+2+1=3*m+3 by omega]
    ring
  have hc (m : ℕ) : AnalyticAt ℂ
      (fun w => c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w) 0 :=
    (((c3_sample_entire _ (by omega)).analyticAt 0).sub
      (analyticAt_const.mul ((c3_sample_entire _ (by omega)).analyticAt 0))).add
      ((c3_sample_entire _ (by omega)).analyticAt 0)
  have hb (k : Fin 12) : AnalyticAt ℂ
      (fun w => (boundaryWeight k:ℂ)*c3Sample (3*M+2+k.val) w) 0 :=
    analyticAt_const.mul ((c3_sample_entire _ (by omega)).analyticAt 0)
  have hjcell (m : ℕ) : sourceJet r
      (fun w => c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w)=
      Complex.I^r*((sampleRealJet (3*m+2) r-2*sampleRealJet (3*m+3) r+sampleRealJet (3*m+4) r):ℂ) := by
    have hl := (c3_sample_entire (3*m+2) (by omega)).analyticAt 0
    have hm := (c3_sample_entire (3*m+3) (by omega)).analyticAt 0
    have hr := (c3_sample_entire (3*m+4) (by omega)).analyticAt 0
    rw [sourceJet_add r (fun w => c3Sample (3*m+2) w-2*c3Sample (3*m+3) w)
      (c3Sample (3*m+4)) (hl.sub (analyticAt_const.mul hm)) hr,
      jet_sub (f:=c3Sample (3*m+2)) (g:=fun w => 2*c3Sample (3*m+3) w) hl (analyticAt_const.mul hm),jet_const_mul,
      sample_jet_formula (3*m+2) (by omega),sample_jet_formula (3*m+3) (by omega),
      sample_jet_formula (3*m+4) (by omega)]
    ring
  have hbs : sourceJet r (fun w => ∑ k : Fin 12, (boundaryWeight k:ℂ)*c3Sample (3*M+2+k.val) w)=
      ∑ k : Fin 12, (boundaryWeight k:ℂ)*sourceJet r (c3Sample (3*M+2+k.val)) := by
    unfold sourceJet
    have he : (fun w => ∑ k : Fin 12, (boundaryWeight k:ℂ)*c3Sample (3*M+2+k.val) w)=
        ∑ k : Fin 12, (fun w => (boundaryWeight k:ℂ)*c3Sample (3*M+2+k.val) w) := by ext w; simp
    rw [he,iteratedDeriv_sum (fun k _ => (hb k).contDiffAt),Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    exact jet_const_mul r _ _
  rw [hs,sourceJet_add r
    (fun w => 1+∑ m ∈ Finset.range M, (c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w))
    (fun w => ∑ k : Fin 12, (boundaryWeight k:ℂ)*c3Sample (3*M+2+k.val) w)
    (analyticAt_const.add (Finset.analyticAt_fun_sum _ (fun m _ => hc m)))
    (Finset.analyticAt_fun_sum _ (fun k _ => hb k)),
    sourceJet_add r (fun _ => 1)
      (fun w => ∑ m ∈ Finset.range M, (c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w))
      analyticAt_const (Finset.analyticAt_fun_sum _ (fun m _ => hc m)),
    jet_constant,jet_sum _ _ _ (fun m _ => hc m),hbs]
  simp_rw [hjcell]
  have hsample (k : Fin 12) := sample_jet_formula (3*M+2+k.val) (by omega) r
  simp_rw [hsample]
  unfold headRealJet
  push_cast
  split_ifs with hr
  · subst r
    simp
  · simp only [Complex.ofReal_zero,zero_add]
    rw [mul_add]
    simp only [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring

end
end CarryC3Tail
