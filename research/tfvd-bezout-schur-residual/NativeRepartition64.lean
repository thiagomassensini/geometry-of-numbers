import FourNativeBoxes
import TwoEvenSourceMargin
import SourceSchur
import CompanionJets

namespace CarrySourceBezout
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The fixed ORIGINAL C3 boundary, including the same completion multiplier. -/
def originalBoundaryJet (M n : ℕ) : ℂ := NativeTrace.sourceJet (2*n)
  (fun w => NativeTrace.valueMultiplier w *
    CarryC3Tail.c3Boundary (fun k => CarryC3Tail.c3Sample k w) (3*M+2))

def regroupedHead64 : ℕ → ℂ := literalHead 64+originalBoundaryJet 64
def regroupedTail64 : ℕ → ℂ := literalTail 64-originalBoundaryJet 64

theorem original_boundary_analytic (M : ℕ) : AnalyticAt ℂ
    (fun w => NativeTrace.valueMultiplier w *
      CarryC3Tail.c3Boundary (fun k => CarryC3Tail.c3Sample k w) (3*M+2)) 0 :=
  NativeTrace.valueMultiplier_analytic.mul
    ((CarryC3Tail.c3_boundary_entire (3*M+2) (by omega)).analyticAt 0)

theorem completed_head64_crosswalk (w : ℂ) :
    CarryC3Tail.completedHead64 w =
      NativeTrace.valueMultiplier w*CarryC3Tail.acceleratedC3Head 64 w := by
  have he := CarryC3Gamma.c3_value_multiplier_gamma_factorization w
  change NativeTrace.valueMultiplier w =
    CarryC3Tail.c3ElementaryMultiplier w*CarryC3Gamma.nativeGamma w at he
  rw [he,CarryC3Tail.completedHead64,CarryC3Tail.finiteLeft]
  ring

theorem regrouped_head64_jet (n : ℕ) : regroupedHead64 n =
    NativeTrace.sourceJet (2*n) CarryC3Tail.completedHead64 := by
  unfold regroupedHead64
  simp only [Pi.add_apply,literalHead,originalBoundaryJet]
  rw [← NativeTrace.sourceJet_add _ _ _ (NativeTrace.head_value_analytic 64) (original_boundary_analytic 64)]
  congr 1
  funext w
  rw [NativeTrace.head_value_formula,completed_head64_crosswalk,CarryC3Tail.acceleratedC3Head]
  ring

theorem regrouped_tail64_jet (n : ℕ) : regroupedTail64 n =
    NativeTrace.sourceJet (2*n) CarryC3Tail.completedTailError := by
  unfold regroupedTail64
  simp only [Pi.sub_apply,literalTail,originalBoundaryJet]
  have hsub := iteratedDeriv_sub (n:=2*n)
    (NativeTrace.tail_value_analytic 64).contDiffAt (original_boundary_analytic 64).contDiffAt
  simp only [NativeTrace.sourceJet]
  rw [← sub_div,← hsub]
  congr 1
  congr 1
  funext w
  dsimp only [Pi.sub_apply]
  rw [literal_tail_value_formula]
  unfold CarryC3Tail.completedTailError CarryC3Tail.acceleratedC3Tail
  change NativeTrace.valueMultiplier w*realCpBracketCutoffTail 3 64 (operatorHeightParameter w)-
    NativeTrace.valueMultiplier w*CarryC3Tail.c3Boundary (fun k => CarryC3Tail.c3Sample k w) (3*64+2) =
    NativeTrace.valueMultiplier w*(realCpBracketCutoffTail 3 64 (operatorHeightParameter w)-
      CarryC3Tail.c3Boundary (fun k => CarryC3Tail.c3Sample k w) (3*64+2))
  ring

theorem regrouped_source (n : ℕ) : regroupedHead64 n+regroupedTail64 n = (nativeC n:ℂ) := by
  have he := congrFun (literal_head_tail 64) n
  simp only [Pi.add_apply] at he
  simp only [regroupedHead64,regroupedTail64,Pi.add_apply,Pi.sub_apply]
  rw [he]
  ring

theorem two_reference_original (j : Fin 4) : twoEvenReference j.val=CarryTwoEvenJets.reference j := by
  fin_cases j <;> norm_num [twoEvenReference,twoEvenReferenceReal,CarryTwoEvenJets.reference]

/-- The EXISTING PR69 certificate is consumed, not recalculated or assumed. -/
theorem native_four_reference_bounds (j : Fin 4) :
    ‖(nativeC j.val:ℂ)-twoEvenReference j.val‖ ≤ (1/10^12:ℝ) := by
  rw [← completedNativeEvenCharacteristicCoefficient_eq_real,two_reference_original]
  have h := CarryC3Boxes.canonical_four_source_boxes j
  norm_num [CarryTwoEvenJets.nativeEvenJets,CarryTwoEvenJets.fourJetTolerance] at h ⊢
  exact h

theorem regrouped_tail64_four_bound (j : Fin 4) :
    ‖regroupedTail64 j.val‖ ≤ (1/10^15:ℝ) := by
  rw [regrouped_tail64_jet]
  have h := CarryC3Tail.completed_tail_jet_error (2*j.val)
  apply h.trans
  fin_cases j <;> norm_num

theorem regrouped_head64_four_bound (j : Fin 4) :
    ‖regroupedHead64 j.val-twoEvenReference j.val‖ ≤ (2/10^12:ℝ) := by
  have he : regroupedHead64 j.val-twoEvenReference j.val =
      ((nativeC j.val:ℂ)-twoEvenReference j.val)-regroupedTail64 j.val := by
    rw [← regrouped_source]
    ring
  rw [he]
  exact ((norm_sub_le _ _).trans (add_le_add (native_four_reference_bounds j)
    (regrouped_tail64_four_bound j))).trans (by norm_num)

/-- A margin for an interval of actual monic directions, before selecting Schur. -/
theorem native_regrouped64_interval_margin (t : ℝ) (ht : |t|≤1) :
    splitErrorBudget regroupedHead64 regroupedTail64 false 2 (twoMonic t) (twoMonic t) <
      (coefficientPair regroupedHead64 regroupedHead64 false 2 (twoMonic t) (twoMonic t)).re :=
  two_source_split_margin _ _ regrouped_head64_four_bound regrouped_tail64_four_bound t ht

theorem native_regrouped64_head_lower (t : ℝ) (ht : |t|≤1) :
    (1/10^8:ℝ) < (coefficientPair regroupedHead64 regroupedHead64 false 2 (twoMonic t) (twoMonic t)).re :=
  two_source_head_margin _ regrouped_head64_four_bound t ht

theorem native_regrouped64_error_upper (t : ℝ) (ht : |t|≤1) :
    splitErrorBudget regroupedHead64 regroupedTail64 false 2 (twoMonic t) (twoMonic t)≤(1/10^13:ℝ) := by
  have hnorm (i : Fin 4) : ‖regroupedHead64 i.val‖≤1 := by
    have hh := norm_le_norm_sub_add (regroupedHead64 i.val) (twoEvenReference i.val)
    have hr := two_reference_norm i
    linarith [regrouped_head64_four_bound i]
  exact two_source_error_upper _ _ hnorm regrouped_tail64_four_bound t ht

/-- A quantitative SOURCE property, proved from fixed boxes and original tails.
No moments, pivot sign, inverse or whitening occur in this statement. -/
theorem native_regrouped64_total_lower (t : ℝ) (ht : |t|≤1) :
    (1/10^8-1/10^13:ℝ) <
      (coefficientPair (regroupedHead64+regroupedTail64) (regroupedHead64+regroupedTail64)
        false 2 (twoMonic t) (twoMonic t)).re := by
  have he := split_error_bound regroupedHead64 regroupedTail64 false 2 (twoMonic t) (twoMonic t)
  have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans he)).1
  simp only [Complex.sub_re] at hh
  have hp := native_regrouped64_head_lower t ht
  have hb := native_regrouped64_error_upper t ht
  linarith

/-- Real coefficient errors are read only after the full source equality. -/
theorem native_real_four_reference_bounds (j : Fin 4) :
    |nativeC j.val-twoEvenReferenceReal j.val| ≤ (1/10^12:ℝ) := by
  have h := native_four_reference_bounds j
  simpa only [twoEvenReference,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h

theorem native_source_c0_positive_from_boxes : 0<nativeC 0 := by
  have h := (abs_le.mp (native_real_four_reference_bounds 0)).1
  norm_num [twoEvenReferenceReal] at h
  linarith

theorem native_source_c1_negative : nativeC 1 < -(1/100:ℝ) := by
  have h := (abs_le.mp (native_real_four_reference_bounds 1)).2
  norm_num [twoEvenReferenceReal] at h
  linarith

theorem native_source_c1_ne_zero : nativeC 1 ≠ 0 := ne_of_lt (native_source_c1_negative.trans (by norm_num))

/-- Prefix invertibility is discharged from the original coefficient boxes,
without invoking a prior moment-positivity consumer. -/
theorem native_even_one_isUnit_from_source : IsUnit (sourceMomentMatrix nativeH 0 1) := by
  have he := congrArg (fun f : PowerSeries ℝ => PowerSeries.coeff 0 f) native_source_recurrence
  have hd : PowerSeries.constantCoeff (PowerSeries.derivative ℝ (PowerSeries.mk nativeC))=nativeC 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [PowerSeries.coeff_derivative]
  have hrec : nativeC 0*nativeH 0 = -nativeC 1 := by
    simpa [PowerSeries.coeff_mul,sourceSeries,momentSeries,PowerSeries.coeff_derivative,hd] using he
  have hn : nativeH 0 ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hrec
    exact native_source_c1_ne_zero (by linarith)
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_fin_one]
  change IsUnit (nativeH 0)
  exact isUnit_iff_ne_zero.mpr hn

theorem native_source_c2_small : |nativeC 2|≤(1/1000:ℝ) := by
  have h := abs_le.mp (native_real_four_reference_bounds 2)
  norm_num [twoEvenReferenceReal] at h
  rw [abs_le]
  constructor <;> linarith [h.1,h.2]

theorem native_monic_two_coordinate_bound : |-(2:ℝ)*nativeC 2/nativeC 1|≤1 := by
  rw [abs_div,abs_mul]
  norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_one (abs_pos.mpr native_source_c1_ne_zero)).2
  have hd : (1/100:ℝ)≤|nativeC 1| := by
    linarith [neg_abs_le (nativeC 1),native_source_c1_negative]
  linarith [native_source_c2_small]

theorem native_monic_two_direction
    (hA : IsUnit (sourceMomentMatrix nativeH 0 1)) :
    monicSourceDirection nativeC nativeH 0 1 = twoMonic (-(2:ℝ)*nativeC 2/nativeC 1) := by
  let z := monicSourceDirection nativeC nativeH 0 1
  have hzlast : z 1=1 := monicSourceDirection_last nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero 0 1
  have he := monicSourceDirection_pair nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero native_source_recurrence false 1 hA ![1,0]
  have hrow : (-nativeC 0*nativeC 1)*z 0+(-2*nativeC 0*nativeC 2)*z 1=0 := by
    simpa [source_even_two,matrixPair,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using he
  rw [hzlast,mul_one] at hrow
  have hz0 : z 0=-(2:ℝ)*nativeC 2/nativeC 1 := by
    apply (eq_div_iff native_source_c1_ne_zero).2
    apply mul_left_cancel₀ completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
    linear_combination -hrow
  change z=twoMonic _
  funext i
  fin_cases i
  · simpa [twoMonic] using hz0
  · simpa [twoMonic] using hzlast

theorem native_critical_regrouped64_margin
    (hA : IsUnit (sourceMomentMatrix nativeH 0 1)) :
    let z := monicSourceDirection nativeC nativeH 0 1
    splitErrorBudget regroupedHead64 regroupedTail64 false 2 z z <
      (coefficientPair regroupedHead64 regroupedHead64 false 2 z z).re := by
  dsimp only
  rw [native_monic_two_direction hA]
  exact native_regrouped64_interval_margin _ native_monic_two_coordinate_bound

theorem native_second_even_remainder_pos_from_split
    (hA : IsUnit (sourceMomentMatrix nativeH 0 1)) :
    0<nativeSourceSchurRemainder 0 1 := by
  let z := monicSourceDirection nativeC nativeH 0 1
  have hs : coefficientPair (regroupedHead64+regroupedTail64)
      (regroupedHead64+regroupedTail64) false 2 z z =
      (nativeC 0*nativeSourceSchurRemainder 0 1:ℝ) := by
    rw [coefficientPair_four_terms]
    exact native_residual_repartition 64 64 (originalBoundaryJet 64) (originalBoundaryJet 64) false 1 hA
  have he := split_error_bound regroupedHead64 regroupedTail64 false 2 z z
  rw [hs] at he
  have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans he)).1
  simp only [Complex.sub_re,Complex.ofReal_re] at hh
  have hm := native_critical_regrouped64_margin hA
  have hc := native_source_c0_positive_from_boxes
  exact (mul_pos_iff_of_pos_left hc).mp (by linarith)

theorem native_second_even_pivot_pos_from_split
    (hA : IsUnit (sourceMomentMatrix nativeH 0 1)) :
    0<sourceMomentSchur nativeH 0 1 := by
  have h := native_second_even_remainder_pos_from_split hA
  rw [nativeSourceSchurRemainder_eq] at h
  have hc := native_source_c0_positive_from_boxes
  exact (mul_pos_iff_of_pos_left hc).mp h

theorem native_second_even_balance_lower_from_original_split :
    (1/10^8-1/10^13:ℝ) < nativeC 0*nativeSourceSchurRemainder 0 1 := by
  let z := monicSourceDirection nativeC nativeH 0 1
  have he := native_regrouped64_total_lower _ native_monic_two_coordinate_bound
  rw [← native_monic_two_direction native_even_one_isUnit_from_source] at he
  have hs : coefficientPair (regroupedHead64+regroupedTail64)
      (regroupedHead64+regroupedTail64) false 2 z z =
      (nativeC 0*nativeSourceSchurRemainder 0 1:ℝ) := by
    rw [coefficientPair_four_terms]
    exact native_residual_repartition 64 64 (originalBoundaryJet 64) (originalBoundaryJet 64)
      false 1 native_even_one_isUnit_from_source
  rw [hs] at he
  simpa only [Complex.ofReal_re] using he

/-- Unconditional finite source certificate: the only boxes consumed are PR69. -/
theorem native_second_even_remainder_pos_from_original_split :
    0<nativeSourceSchurRemainder 0 1 :=
  native_second_even_remainder_pos_from_split native_even_one_isUnit_from_source

theorem native_second_even_pivot_pos_from_original_split :
    0<sourceMomentSchur nativeH 0 1 :=
  native_second_even_pivot_pos_from_split native_even_one_isUnit_from_source

end
end CarrySourceBezout
