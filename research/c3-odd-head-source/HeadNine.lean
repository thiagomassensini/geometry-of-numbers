import HeadCoefficientBoxes
import GammaNineValue

namespace CarryOddHeadSource
open CarryC3Tail CarryC3Boxes CarryC3Gamma
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 25000

def headReferenceBox9 (r : Fin 9) : Box :=
  if hr : r.val < 7 then headReferenceBox ⟨r.val,hr⟩
  else if r.val = 7 then
    ⟨(-469425525774469547/10000000000000000000000),
      (-469425525774469349/10000000000000000000000)⟩
  else ⟨(50413365580929121/10000000000000000000000),
    (12603341395232311/2500000000000000000000)⟩

theorem head_evaluator_check9 (r : Fin 9) :
    (headJetBox r.val).Subset (headReferenceBox9 r) := by
  by_cases hr : r.val < 7
  · simpa only [headReferenceBox9, dif_pos hr] using head_evaluator_check ⟨r.val,hr⟩
  · have he : r.val=7 ∨ r.val=8 := by omega
    rcases he with h7 | h8
    · have hr7 : r = 7 := Fin.ext h7
      subst r
      decide +kernel
    · have hr8 : r = 8 := Fin.ext h8
      subst r
      decide +kernel

theorem head_reference9_contains (r : Fin 9) :
    (headReferenceBox9 r).Contains (headRealJet 64 r.val) :=
  Box.subset_contains (head_evaluator_check9 r) (head_jet_box r.val)

def cachedHeadJetBox9 (r : ℕ) : Box :=
  if hr : r < 9 then headReferenceBox9 ⟨r,hr⟩ else headJetBox r

theorem cached_head9_contains (r : ℕ) :
    (cachedHeadJetBox9 r).Contains (headRealJet 64 r) := by
  unfold cachedHeadJetBox9
  split_ifs with h
  · exact head_reference9_contains ⟨r,h⟩
  · exact head_jet_box r

def cachedLeftJetBox9 : ℕ → Box := convolutionBox
  (convolutionBox (convolutionBox polynomialJetBox exponentialJetBox)
    (reciprocalJetBox chartJetBox)) cachedHeadJetBox9

theorem cached_left9_contains (r : ℕ) :
    (cachedLeftJetBox9 r).Contains (leftRealJet r) :=
  convolution_box _ _ _ _ (convolution_box _ _ _ _
    (convolution_box _ _ _ _ polynomial_jet_box exponential_jet_box)
    (reciprocal_jet_box chartJetBox chartRealJet chart_jet_box
      (Or.inr chart_center_interval_negative))) cached_head9_contains r

#print axioms head_evaluator_check9
#print axioms cached_left9_contains
end CarryOddHeadSource
