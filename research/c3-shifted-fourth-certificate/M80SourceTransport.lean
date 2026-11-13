import C3Head48Jet
import TightHeadSource

namespace C3ShiftedFourth
open CarryC3Tail CarryC3Boxes CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets CPFormal.Analytic.Cp
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

theorem accelerated_head80_jet_formula (r : ℕ) :
    sourceJet r (acceleratedC3Head48 80) = Complex.I^r*(head80RealJet r:ℂ) := by
  have hs : acceleratedC3Head48 80 = (fun w =>
      1 + ∑ m ∈ Finset.range 80,
        (c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w) +
        ∑ k : Fin 24, (boundary48Weight k:ℂ)*c3Sample (242+k.val) w) := by
    funext w
    rw [acceleratedC3Head48, finiteBracketedDirichletChart_three_eq_one_add_trace,
      finiteCanonicalBracketTrace, boundary48_stencil]
    congr 2
    apply Finset.sum_congr rfl
    intro m hm
    rw [native_c3_cell_fd, fd_two]
    rw [show 3*m+2+2=3*m+4 by omega, show 3*m+2+1=3*m+3 by omega]
    ring
  have hc (m : ℕ) : AnalyticAt ℂ
      (fun w => c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w) 0 :=
    (((c3_sample_entire _ (by omega)).analyticAt 0).sub
      (analyticAt_const.mul ((c3_sample_entire _ (by omega)).analyticAt 0))).add
      ((c3_sample_entire _ (by omega)).analyticAt 0)
  have hb (k : Fin 24) : AnalyticAt ℂ
      (fun w => (boundary48Weight k:ℂ)*c3Sample (242+k.val) w) 0 :=
    analyticAt_const.mul ((c3_sample_entire (242+k.val) (by omega)).analyticAt 0)
  have hjcell (m : ℕ) : sourceJet r
      (fun w => c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w)=
      Complex.I^r*((sampleRealJet (3*m+2) r-2*sampleRealJet (3*m+3) r+
        sampleRealJet (3*m+4) r):ℂ) := by
    have hl := (c3_sample_entire (3*m+2) (by omega)).analyticAt 0
    have hm := (c3_sample_entire (3*m+3) (by omega)).analyticAt 0
    have hr := (c3_sample_entire (3*m+4) (by omega)).analyticAt 0
    rw [sourceJet_add r (fun w => c3Sample (3*m+2) w-2*c3Sample (3*m+3) w)
      (c3Sample (3*m+4)) (hl.sub (analyticAt_const.mul hm)) hr,
      jet_sub (f:=c3Sample (3*m+2)) (g:=fun w => 2*c3Sample (3*m+3) w)
        hl (analyticAt_const.mul hm), jet_const_mul,
      sample_jet_formula (3*m+2) (by omega),
      sample_jet_formula (3*m+3) (by omega),
      sample_jet_formula (3*m+4) (by omega)]
    ring
  have hbs : sourceJet r (fun w =>
      ∑ k : Fin 24, (boundary48Weight k:ℂ)*c3Sample (242+k.val) w) =
      ∑ k : Fin 24, (boundary48Weight k:ℂ)*sourceJet r (c3Sample (242+k.val)) := by
    unfold sourceJet
    have he : (fun w =>
        ∑ k : Fin 24, (boundary48Weight k:ℂ)*c3Sample (242+k.val) w) =
        ∑ k : Fin 24, (fun w => (boundary48Weight k:ℂ)*c3Sample (242+k.val) w) := by
      ext w
      simp
    rw [he, iteratedDeriv_sum (fun k _ => (hb k).contDiffAt), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    exact jet_const_mul r _ _
  rw [hs, sourceJet_add r
      (fun w => 1+∑ m ∈ Finset.range 80,
        (c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w))
      (fun w => ∑ k : Fin 24, (boundary48Weight k:ℂ)*c3Sample (242+k.val) w)
      (analyticAt_const.add (Finset.analyticAt_fun_sum _ (fun m _ => hc m)))
      (Finset.analyticAt_fun_sum _ (fun k _ => hb k)),
    sourceJet_add r (fun _ => 1)
      (fun w => ∑ m ∈ Finset.range 80,
        (c3Sample (3*m+2) w-2*c3Sample (3*m+3) w+c3Sample (3*m+4) w))
      analyticAt_const (Finset.analyticAt_fun_sum _ (fun m _ => hc m)),
    jet_constant, jet_sum _ _ _ (fun m _ => hc m), hbs]
  simp_rw [hjcell]
  have hsample (k : Fin 24) := sample_jet_formula (242+k.val) (by omega) r
  simp_rw [hsample]
  unfold head80RealJet
  push_cast
  split_ifs with hr
  · subst r
    simp
  · simp only [Complex.ofReal_zero, zero_add]
    rw [mul_add]
    simp only [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring


#print axioms accelerated_head80_jet_formula

end
end C3ShiftedFourth
