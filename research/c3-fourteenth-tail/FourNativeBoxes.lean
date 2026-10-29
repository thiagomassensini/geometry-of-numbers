import HeadCoefficientBoxes
import FourJetWitness

namespace CarryC3Boxes
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CarryC3Tail
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000

def referenceReal (j : Fin 4) : ℚ :=
  if j.val=0 then 497120778188314/1000000000000000 else
  if j.val=1 then -11485972157573/1000000000000000 else
  if j.val=2 then 123452018070/1000000000000000 else
    -832355481/1000000000000000

theorem reference_real_eq (j : Fin 4) : (referenceReal j:ℂ)=reference j := by
  fin_cases j <;> norm_num [referenceReal,reference]

def signedCompletedBox (j : Fin 4) : Box :=
  if j.val%2=0 then cachedCompletedJetBox ⟨2*j.val,by omega⟩
    else (cachedCompletedJetBox ⟨2*j.val,by omega⟩).neg

def signedCompletedReal (j : Fin 4) : ℝ :=
  if j.val%2=0 then finiteCompletedRealJet ⟨2*j.val,by omega⟩
    else -finiteCompletedRealJet ⟨2*j.val,by omega⟩

theorem signed_completed_contains (j : Fin 4) :
    (signedCompletedBox j).Contains (signedCompletedReal j) := by
  unfold signedCompletedBox signedCompletedReal
  split_ifs
  · exact cached_completed_contains _
  · exact Box.neg_contains (cached_completed_contains _)

theorem signed_completed_formula (j : Fin 4) :
    finiteCompletedJet ⟨2*j.val,by omega⟩=(signedCompletedReal j:ℂ) := by
  rw [finite_completed_jet_formula]
  fin_cases j <;> norm_num [signedCompletedReal,Complex.I_sq,pow_succ]

/-- Four exact rational checks. No floating input is used as an inclusion. -/
theorem four_finite_evaluator_checks (j : Fin 4) :
    (signedCompletedBox j).Subset ((Box.point (referenceReal j)).expand (1/10^13)) := by
  fin_cases j <;> decide +kernel

theorem finite_completed_reference_error (j : Fin 4) :
    ‖finiteCompletedJet ⟨2*j.val,by omega⟩-reference j‖ ≤ (1/10^13:ℝ) := by
  rw [signed_completed_formula,← reference_real_eq]
  have hh := Box.subset_contains (four_finite_evaluator_checks j) (signed_completed_contains j)
  have hl := hh.1
  have hu := hh.2
  dsimp only [Box.expand,Box.point] at hl hu
  rw [Rat.cast_sub] at hl
  rw [Rat.cast_add] at hu
  have hc : (referenceReal j:ℂ)=((referenceReal j:ℝ):ℂ) := by simp
  rw [hc,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_le]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] at hl hu
  constructor <;> linarith

/-- The four boxes requested in PR #67, now discharged from the SAME
native C3 source, with Xi/chart/Gamma, exact seed, all cells and the full tail. -/
theorem canonical_four_source_boxes (j : Fin 4) :
    ‖nativeEvenJets j-reference j‖ ≤ fourJetTolerance := by
  have hc : nativeEvenJets j=sourceJet (2*j.val) completedNativeOperatorCharacteristic := by
    rw [nativeEvenJets,← completedNativeFullCharacteristicTaylorCoefficient_even]
    rfl
  rw [hc]
  have h := norm_sub_le_norm_sub_add_norm_sub
    (sourceJet (2*j.val) completedNativeOperatorCharacteristic)
    (finiteCompletedJet ⟨2*j.val,by omega⟩) (reference j)
  apply (h.trans (add_le_add (completed_jet_evaluator_error ⟨2*j.val,by omega⟩)
    (finite_completed_reference_error j))).trans
  norm_num [fourJetTolerance]

/-- A finite source-derived sign. This is NOT an all-order positivity theorem. -/
theorem canonical_two_even_determinant_pos_from_c3 :
    0 < canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2-
      (canonicalCompletedNativeLogDerivativeMoment 1)^2 :=
  canonical_two_even_det_pos_of_four_jet_boxes canonical_four_source_boxes

end
end CarryC3Boxes
