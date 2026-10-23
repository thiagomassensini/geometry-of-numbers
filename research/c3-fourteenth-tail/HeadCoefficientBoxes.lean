import HeadEvaluatorData
namespace CarryC3Boxes
open CarryC3Tail CarryC3Gamma
open scoped BigOperators
set_option autoImplicit false
theorem head_reference_contains (r : Fin 7) : (headReferenceBox r).Contains (headRealJet 64 r.val) :=
  Box.subset_contains (head_evaluator_check r) (head_jet_box r.val)
def cachedHeadJetBox (r : ℕ) : Box := if h:r<7 then headReferenceBox ⟨r,h⟩ else headJetBox r
theorem cached_head_contains (r : ℕ) : (cachedHeadJetBox r).Contains (headRealJet 64 r) := by
  unfold cachedHeadJetBox
  split_ifs with h
  · exact head_reference_contains ⟨r,h⟩
  · exact head_jet_box r
def cachedLeftJetBox : ℕ → Box := convolutionBox
  (convolutionBox (convolutionBox polynomialJetBox exponentialJetBox) (reciprocalJetBox chartJetBox)) cachedHeadJetBox
def cachedCompletedJetBox (r : Fin 7) : Box := bsumFin (fun j : Fin (r.val+1) =>
  bmul (cachedLeftJetBox j.val) (Box.point (gammaRealReference ⟨r.val-j.val,by omega⟩)))
theorem cached_left_contains (r : ℕ) : (cachedLeftJetBox r).Contains (leftRealJet r) :=
  convolution_box _ _ _ _ (convolution_box _ _ _ _
    (convolution_box _ _ _ _ polynomial_jet_box exponential_jet_box)
    (reciprocal_jet_box chartJetBox chartRealJet chart_jet_box (Or.inr chart_center_interval_negative))) cached_head_contains r
theorem cached_completed_contains (r : Fin 7) : (cachedCompletedJetBox r).Contains (finiteCompletedRealJet r) := by
  have hh := bsumFin_contains
    (fun j : Fin (r.val+1) => bmul (cachedLeftJetBox j.val) (Box.point (gammaRealReference ⟨r.val-j.val,by omega⟩)))
    (fun j : Fin (r.val+1) => leftRealJet j.val*(gammaRealReference ⟨r.val-j.val,by omega⟩:ℝ))
    (fun j => bmul_contains (cached_left_contains j.val) (Box.point_contains _))
  have he : (∑ j : Fin (r.val+1), leftRealJet j.val*(gammaRealReference ⟨r.val-j.val,by omega⟩:ℝ))=finiteCompletedRealJet r :=
    by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range.mp hj,dif_pos]
  rw [he] at hh
  exact hh
end CarryC3Boxes
