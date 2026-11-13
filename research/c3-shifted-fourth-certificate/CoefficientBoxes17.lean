import HighCoefficientBoxes17
import IntervalGate
import SourceBezout
import JetMagnitude17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets C3CofactorCorrelation CarrySourceBezout
open C3Cofactor
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- Absolute bounds for the original M=80 left jets, using the strict
low-order values and the uniform tail-of-jet estimate. -/
def leftJetMagnitudeBound17 (n : ℕ) : ℚ :=
  if n = 0 then 1/4 else if n = 1 then 1/2 else 1

theorem coefficient_left_jet_abs_bound17 (r : Fin 17) :
    |leftRealJet80 r.val| ≤ (leftJetMagnitudeBound17 r.val : ℝ) := by
  by_cases h0 : r.val = 0
  · have hr : r = ⟨0, by omega⟩ := Fin.ext h0
    rw [hr]
    simpa [leftJetMagnitudeBound17] using left_real_jet_zero_abs_bound17
  · by_cases h1 : r.val = 1
    · have hr : r = ⟨1, by omega⟩ := Fin.ext h1
      rw [hr]
      simpa [leftJetMagnitudeBound17] using left_real_jet_one_abs_bound17
    · have hb := left_real_jet_abs_bound17 r
      simpa [leftJetMagnitudeBound17, h0, h1] using hb

def nativeJetErrorBound17 (r : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (r+1),
    leftJetMagnitudeBound17 k * (2 * 4^(r-k) / 10^34 + 2 / 10^29)) + 2/10^27

def nativeFiniteCoefficientBox17 (j : Fin 9) : Box :=
  (Box.point ((-1 : ℚ)^j.val)).mul
    (completedJet48ScaleBox.mul
      (normalizedCompletedReferenceBoxVerified80 (2*j.val)))

def nativeCoefficientBox17 (j : Fin 9) : Box :=
  (nativeFiniteCoefficientBox17 j).expand (nativeJetErrorBound17 (2*j.val))

def nativeCoefficientCandidate17 (j : Fin 9) : RationalBall :=
  match j.val with
  | 0 => ⟨994241556376628219825547479370795439614587167989 /
      2000000000000000000000000000000000000000000000000, 1/10^21⟩
  | 1 => ⟨-1148597215757271876762493824881608513229656445821 /
      100000000000000000000000000000000000000000000000000, 1/10^21⟩
  | 2 => ⟨12345201807031800689034579149485113813606353281 /
      100000000000000000000000000000000000000000000000000, 1/10^22⟩
  | 3 => ⟨-20808887034638176800118968146115517590403491 /
      25000000000000000000000000000000000000000000000000, 1/10^22⟩
  | 4 => ⟨79844531026882743494505405260637479984159 /
      20000000000000000000000000000000000000000000000000, 1/10^23⟩
  | 5 => ⟨-1461602576011096086241214277653455424961 /
      100000000000000000000000000000000000000000000000000, 1/10^24⟩
  | 6 => ⟨26715875284605280985470062865970269 /
      625000000000000000000000000000000000000000000000, 1/10^25⟩
  | 7 => ⟨-5154813067309003277848560370401171 /
      50000000000000000000000000000000000000000000000000, 1/10^25⟩
  | 8 => ⟨4199539616299057501820755368757 /
      20000000000000000000000000000000000000000000000000, 1/10^24⟩
  | _ => ⟨0, 1⟩

def nativeCoefficientCandidateEnvelope17 (j : Fin 9) : Box :=
  ⟨(nativeCoefficientCandidate17 j).center - (nativeCoefficientCandidate17 j).radius,
    (nativeCoefficientCandidate17 j).center + (nativeCoefficientCandidate17 j).radius⟩

theorem native_coefficient_sourceJet_eq (n : ℕ) :
    (C3CofactorCorrelation.nativeC n : ℂ) =
      CarrySourceBezout.NativeTrace.sourceJet (2*n)
        completedNativeOperatorCharacteristic := by
  change (completedNativeRealEvenCharacteristicCoefficient n : ℂ) = _
  rw [← completedNativeEvenCharacteristicCoefficient_eq_real,
    ← completedNativeFullCharacteristicTaylorCoefficient_even]
  rfl

theorem native_jet_crosswalk_real_bound17 (j : Fin 9) :
    |C3CofactorCorrelation.nativeC j.val - (-1 : ℝ)^j.val *
      finiteCompletedRealJetCrosswalk80 ⟨2*j.val, by omega⟩| ≤
        (nativeJetErrorBound17 (2*j.val) : ℝ) := by
  have hjet := completed_native_jet_crosswalk_error80
    (⟨2*j.val, by omega⟩ : Fin 17)
  have hsum :
      (∑ k ∈ Finset.range (2*j.val+1),
        |leftRealJet80 k| *
          (2*4^(2*j.val-k)/10^34+(2/10^29:ℝ))) + 2/10^27 ≤
        (nativeJetErrorBound17 (2*j.val) : ℝ) := by
    unfold nativeJetErrorBound17
    have hweights :
        (∑ k ∈ Finset.range (2*j.val+1),
          |leftRealJet80 k| *
            ((2:ℝ)*4^(2*j.val-k)/(10:ℝ)^34+2/(10:ℝ)^29)) ≤
        (∑ k ∈ Finset.range (2*j.val+1),
          (leftJetMagnitudeBound17 k : ℝ) *
            ((2:ℝ)*4^(2*j.val-k)/(10:ℝ)^34+2/(10:ℝ)^29)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hklt : k < 17 := by
        have hk' := Finset.mem_range.mp hk
        have hj := j.isLt
        omega
      have hleft := coefficient_left_jet_abs_bound17 ⟨k, hklt⟩
      have hnonneg : 0 ≤
          (2:ℝ)*4^(2*j.val-k)/(10:ℝ)^34+2/(10:ℝ)^29 := by positivity
      exact mul_le_mul_of_nonneg_right hleft hnonneg
    have hweightCast :
        (∑ k ∈ Finset.range (2*j.val+1),
          (leftJetMagnitudeBound17 k : ℝ) *
            ((2:ℝ)*4^(2*j.val-k)/(10:ℝ)^34+2/(10:ℝ)^29)) =
        (↑(∑ k ∈ Finset.range (2*j.val+1),
          (leftJetMagnitudeBound17 k *
            (2*4^(2*j.val-k)/10^34+2/10^29) : ℚ)) : ℝ) := by
      norm_num [Rat.cast_sum, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
        Rat.cast_pow, Rat.cast_natCast]
    rw [Rat.cast_add]
    calc
      _ ≤ (∑ k ∈ Finset.range (2*j.val+1),
          (leftJetMagnitudeBound17 k : ℝ) *
            ((2:ℝ)*4^(2*j.val-k)/(10:ℝ)^34+2/(10:ℝ)^29)) + 2/10^27 :=
        add_le_add_left hweights _
      _ = (↑(∑ k ∈ Finset.range (2*j.val+1),
          (leftJetMagnitudeBound17 k *
            (2*4^(2*j.val-k)/10^34+2/10^29) : ℚ)) : ℝ) + 2/10^27 := by
        rw [hweightCast]
      _ = (↑(∑ k ∈ Finset.range (2*j.val+1),
          (leftJetMagnitudeBound17 k *
            (2*4^(2*j.val-k)/10^34+2/10^29) : ℚ)) : ℝ) +
          (↑(2/10^27 : ℚ) : ℝ) := by norm_num
  have hphase : Complex.I^(2*j.val) = ((-1:ℝ)^j.val : ℂ) := by
    calc
      Complex.I^(2*j.val) = (Complex.I^2)^j.val := by rw [pow_mul]
      _ = ((-1:ℝ)^j.val : ℂ) := by simp [Complex.I_sq]
  have hcomplex :
      ‖((C3CofactorCorrelation.nativeC j.val - (-1:ℝ)^j.val *
          finiteCompletedRealJetCrosswalk80 ⟨2*j.val, by omega⟩ : ℝ) : ℂ)‖ ≤
        (nativeJetErrorBound17 (2*j.val) : ℝ) := by
    have hcombined := hjet.trans hsum
    simpa [C3CofactorCorrelation.nativeC_eq_sourceJet, hphase] using hcombined
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hcomplex

theorem native_finite_coefficient_box17_contains (j : Fin 9) :
    (nativeFiniteCoefficientBox17 j).Contains
      ((-1:ℝ)^j.val * finiteCompletedRealJetCrosswalk80
        ⟨2*j.val, by omega⟩) := by
  have hsign : (Box.point ((-1:ℚ)^j.val)).Contains ((-1:ℝ)^j.val) := by
    fin_cases j <;> norm_num [Box.point, Box.Contains]
  have hscale := completed_jet48_scale_box_contains
  have hn : (normalizedCompletedReferenceBoxVerified80 (2*j.val)).Contains
      (normalizedCompletedReferenceJet80 (2*j.val)) :=
    normalized_completed_reference_box_verified80_contains ⟨2*j.val, by omega⟩
  have hprod := Box.mul_contains hscale hn
  have hprod' := Box.mul_contains hsign hprod
  rw [finite_completed_crosswalk_eq_normalized80]
  simpa [nativeFiniteCoefficientBox17, completedJet48Scale,
    C3CofactorCorrelation.gammaReferenceScale, mul_assoc] using hprod'

theorem native_coefficient_box17_contains (j : Fin 9) :
    (nativeCoefficientBox17 j).Contains (C3CofactorCorrelation.nativeC j.val) := by
  apply Box.expand_contains (native_finite_coefficient_box17_contains j)
  exact native_jet_crosswalk_real_bound17 j

theorem native_coefficient_grid_box17_c7 :
    GridBox.ofBox (nativeCoefficientBox17 ⟨7, by omega⟩) =
      ⟨-103096261385986, -103096261306448⟩ := by
  decide +kernel

theorem native_coefficient_grid_box17_c8 :
    GridBox.ofBox (nativeCoefficientBox17 ⟨8, by omega⟩) =
      ⟨209976582231, 209977379476⟩ := by
  decide +kernel

theorem native_coefficient_box17_subset_candidate_c7 :
    (nativeCoefficientBox17 ⟨7, by omega⟩).Subset
      (nativeCoefficientCandidateEnvelope17 ⟨7, by omega⟩) := by
  have hgrid : Box.Subset
      (GridBox.toBox (GridBox.ofBox (nativeCoefficientBox17 ⟨7, by omega⟩)))
      (nativeCoefficientCandidateEnvelope17 ⟨7, by omega⟩) := by
    rw [native_coefficient_grid_box17_c7]
    norm_num [GridBox.toBox, nativeCoefficientCandidateEnvelope17,
      grid_denominator_rat_value, nativeCoefficientCandidate17, Box.Subset]
  have hround := grid_toBox_ofBox_contains (nativeCoefficientBox17 ⟨7, by omega⟩)
  exact ⟨hgrid.1.trans hround.1, hround.2.trans hgrid.2⟩

theorem native_coefficient_box17_subset_candidate_c8 :
    (nativeCoefficientBox17 ⟨8, by omega⟩).Subset
      (nativeCoefficientCandidateEnvelope17 ⟨8, by omega⟩) := by
  have hgrid : Box.Subset
      (GridBox.toBox (GridBox.ofBox (nativeCoefficientBox17 ⟨8, by omega⟩)))
      (nativeCoefficientCandidateEnvelope17 ⟨8, by omega⟩) := by
    rw [native_coefficient_grid_box17_c8]
    norm_num [GridBox.toBox, nativeCoefficientCandidateEnvelope17,
      grid_denominator_rat_value, nativeCoefficientCandidate17, Box.Subset]
  have hround := grid_toBox_ofBox_contains (nativeCoefficientBox17 ⟨8, by omega⟩)
  exact ⟨hgrid.1.trans hround.1, hround.2.trans hgrid.2⟩

theorem native_coefficient_candidate17_contains_c7 :
    (nativeCoefficientCandidate17 ⟨7, by omega⟩).Contains
      (C3CofactorCorrelation.nativeC 7) := by
  have hbox := Box.subset_contains native_coefficient_box17_subset_candidate_c7
    (native_coefficient_box17_contains ⟨7, by omega⟩)
  change ((nativeCoefficientCandidateEnvelope17 ⟨7, by omega⟩).lo : ℝ) ≤ _ ∧
      _ ≤ ((nativeCoefficientCandidateEnvelope17 ⟨7, by omega⟩).hi : ℝ) at hbox
  simp only [nativeCoefficientCandidateEnvelope17] at hbox
  change |C3CofactorCorrelation.nativeC 7 -
    (nativeCoefficientCandidate17 ⟨7, by omega⟩).center| ≤
      (nativeCoefficientCandidate17 ⟨7, by omega⟩).radius
  rw [abs_le]
  constructor
  · push_cast at hbox ⊢
    linarith [hbox.1]
  · push_cast at hbox ⊢
    linarith [hbox.2]

theorem native_coefficient_candidate17_contains_c8 :
    (nativeCoefficientCandidate17 ⟨8, by omega⟩).Contains
      (C3CofactorCorrelation.nativeC 8) := by
  have hbox := Box.subset_contains native_coefficient_box17_subset_candidate_c8
    (native_coefficient_box17_contains ⟨8, by omega⟩)
  change ((nativeCoefficientCandidateEnvelope17 ⟨8, by omega⟩).lo : ℝ) ≤ _ ∧
      _ ≤ ((nativeCoefficientCandidateEnvelope17 ⟨8, by omega⟩).hi : ℝ) at hbox
  simp only [nativeCoefficientCandidateEnvelope17] at hbox
  change |C3CofactorCorrelation.nativeC 8 -
    (nativeCoefficientCandidate17 ⟨8, by omega⟩).center| ≤
      (nativeCoefficientCandidate17 ⟨8, by omega⟩).radius
  rw [abs_le]
  constructor
  · push_cast at hbox ⊢
    linarith [hbox.1]
  · push_cast at hbox ⊢
    linarith [hbox.2]

#print axioms native_jet_crosswalk_real_bound17
#print axioms native_finite_coefficient_box17_contains
#print axioms native_coefficient_box17_contains
#print axioms native_coefficient_grid_box17_c7
#print axioms native_coefficient_grid_box17_c8
#print axioms native_coefficient_box17_subset_candidate_c7
#print axioms native_coefficient_box17_subset_candidate_c8
#print axioms native_coefficient_candidate17_contains_c7
#print axioms native_coefficient_candidate17_contains_c8

end
end C3ShiftedFourth
