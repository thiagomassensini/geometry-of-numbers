import HeadNine
import OddHeadMargin

namespace CarryOddHeadSource
open CarryC3Tail CarryC3Boxes CarryC3Gamma CarrySelfAdjointOperator
open PhysicalSewing CarryTwoEvenJets CarrySourceBezout CarrySourceDimensionThree
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 25000

def finiteCompletedJet9 (r : Fin 9) : ℂ :=
  ∑ j ∈ Finset.range (r.val+1),
    sourceJet j finiteLeft * gammaReference9 ⟨r.val-j,by omega⟩

def finiteCompletedRealJet9 (r : Fin 9) : ℝ :=
  ∑ j ∈ Finset.range (r.val+1),
    leftRealJet j * (gammaRealReference9 ⟨r.val-j,by omega⟩ : ℝ)

theorem gamma_jet_replacement_error9 (r : Fin 9) :
    ‖sourceJet r.val completedHead64-finiteCompletedJet9 r‖ ≤
      (64*(∑ j ∈ Finset.range (r.val+1), (4:ℝ)^j))/10^18 := by
  change ‖sourceJet r.val (fun w => finiteLeft w*nativeGamma w)-finiteCompletedJet9 r‖ ≤ _
  rw [jet_mul finite_left_analytic (native_gamma_analytic 0 (by norm_num)),finiteCompletedJet9,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub,norm_mul]
  have hg := native_gamma_nine_boxes ⟨r.val-j,by omega⟩
  have hl := finite_left_jet_bound j
  exact (mul_le_mul hl hg (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem finite_completed_jet_formula9 (r : Fin 9) :
    finiteCompletedJet9 r = Complex.I^r.val*(finiteCompletedRealJet9 r:ℂ) := by
  unfold finiteCompletedJet9 finiteCompletedRealJet9
  simp_rw [finite_left_jet_formula,gammaReference9]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r.val := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show Complex.I^r.val=Complex.I^j*Complex.I^(r.val-j) by
    rw [← pow_add,Nat.add_sub_of_le hjr]]
  ring

def cachedCompletedJetBox9 (r : Fin 9) : Box :=
  bsumFin (fun j : Fin (r.val+1) => bmul (cachedLeftJetBox9 j.val)
    (Box.point (gammaRealReference9 ⟨r.val-j.val,by omega⟩)))

theorem cached_completed9_contains (r : Fin 9) :
    (cachedCompletedJetBox9 r).Contains (finiteCompletedRealJet9 r) := by
  have hh := bsumFin_contains
    (fun j : Fin (r.val+1) => bmul (cachedLeftJetBox9 j.val)
      (Box.point (gammaRealReference9 ⟨r.val-j.val,by omega⟩)))
    (fun j : Fin (r.val+1) => leftRealJet j.val*
      (gammaRealReference9 ⟨r.val-j.val,by omega⟩:ℝ))
    (fun j => bmul_contains (cached_left9_contains j.val) (Box.point_contains _))
  have he : (∑ j : Fin (r.val+1), leftRealJet j.val*
      (gammaRealReference9 ⟨r.val-j.val,by omega⟩:ℝ)) = finiteCompletedRealJet9 r := by
    unfold finiteCompletedRealJet9
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range.mp hj,dif_pos]
  rw [he] at hh
  exact hh

theorem head8_rational_upper :
    (cachedCompletedJetBox9 8).hi ≤ (3993/10^12:ℚ) := by
  decide +kernel

theorem finite_completed_real_8_upper :
    finiteCompletedRealJet9 8 ≤ (3993/10^12:ℝ) := by
  have hc := (cached_completed9_contains 8).2
  have hr : ((cachedCompletedJetBox9 8).hi : ℝ) ≤ ((3993/10^12:ℚ):ℝ) := by
    exact_mod_cast head8_rational_upper
  norm_num at hr ⊢
  exact hc.trans hr

theorem regrouped_head64_four_upper :
    (regroupedHead64 4).re ≤ (3999/10^12:ℝ) := by
  rw [regrouped_head64_jet]
  change (sourceJet 8 completedHead64).re ≤ (3999/10^12:ℝ)
  have he := gamma_jet_replacement_error9 8
  have hr := (Complex.abs_re_le_norm
    (sourceJet 8 completedHead64 - finiteCompletedJet9 8)).trans he
  have hu := (abs_le.mp hr).2
  have hf : finiteCompletedJet9 8 = (finiteCompletedRealJet9 8 : ℂ) := by
    rw [finite_completed_jet_formula9]
    norm_num [Complex.I_sq, pow_succ]
  rw [hf] at hu
  simp only [Complex.sub_re, Complex.ofReal_re] at hu
  norm_num at hu ⊢
  linarith [finite_completed_real_8_upper]

theorem native_c4_upper_from_completed_c3 :
    nativeC 4 ≤ (4/10^9:ℝ) :=
  native_c4_upper_of_head_upper regrouped_head64_four_upper

theorem odd_source_det_margin_from_completed_c3 :
    (9/10^17:ℝ) < (coefficientBlock (sourceKernel nativeC true) 2).det :=
  odd_source_det_margin_of_c4_upper native_c4_upper_from_completed_c3

theorem odd_source_det_pos_from_completed_c3 :
    0 < (coefficientBlock (sourceKernel nativeC true) 2).det :=
  odd_source_det_pos_of_head_upper regrouped_head64_four_upper

theorem odd_prefix_isUnit_from_completed_c3 :
    IsUnit (sourceMomentMatrix nativeH 1 2) :=
  odd_prefix_isUnit_of_head_upper regrouped_head64_four_upper

#print axioms regrouped_head64_four_upper
#print axioms native_c4_upper_from_completed_c3
#print axioms odd_source_det_margin_from_completed_c3
#print axioms odd_source_det_pos_from_completed_c3
#print axioms odd_prefix_isUnit_from_completed_c3
theorem odd_c4_ceiling_from_completed_c3 :
    nativeC 4 < oddPrefixC4Ceiling nativeC :=
  odd_c4_ceiling_of_head_upper regrouped_head64_four_upper

theorem third_odd_gate_from_completed_c3 :
    0 < sourceMomentSchur nativeH 1 2 ↔
      nativeC 6 < oddSourceCeiling nativeC / (6*nativeC 0) :=
  third_odd_gate_of_head_upper regrouped_head64_four_upper

#print axioms odd_c4_ceiling_from_completed_c3
#print axioms third_odd_gate_from_completed_c3

end
end CarryOddHeadSource
