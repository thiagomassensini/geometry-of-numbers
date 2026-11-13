import CoefficientBoxes17
import SourceGate
import SourceCoefficientGreen
import SourceSchurShift
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets C3CofactorCorrelation CarrySourceBezout
  C3Cofactor
open scoped BigOperators Matrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

private abbrev nativeOddPrefixCoefficients17 : Fin 7 → ℝ :=
  fun i => C3CofactorCorrelation.nativeC i.val

theorem native_odd_third_block_eq17 :
    coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 3 =
      oddThirdB (sourceOddA nativeOddPrefixCoefficients17)
        (sourceOddB nativeOddPrefixCoefficients17)
        (sourceOddD nativeOddPrefixCoefficients17)
        (sourceOddE nativeOddPrefixCoefficients17)
        (sourceOddF nativeOddPrefixCoefficients17)
        (sourceOddG nativeOddPrefixCoefficients17) := by
  rw [CarrySourceDimensionThree.odd_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oddThirdB, nativeOddPrefixCoefficients17, sourceOddA, sourceOddB,
      sourceOddD, sourceOddE, sourceOddF, sourceOddG] <;> ring

theorem native_odd_third_det_positive17 :
    0 < (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 3).det := by
  rw [native_odd_third_block_eq17,
    odd_third_cofactor_identity _ _ _ _ _ _ (refXBall.center : ℝ)
      (refYBall.center : ℝ)]
  exact (candidate_source_gate
    C3CofactorCorrelation.native_even_source_coefficient_boxes).2.2

/-- The coefficient centers are the exact rational centers of the M=80
original C3 coefficient ratios. The radii are outward rounded rational bounds
from the literal head, original Gamma ledger, and the original C3 tail. -/
def normalizedCoefficientCandidate17 (j : Fin 9) : RationalBall :=
  match j.val with
  | 0 => ⟨1, 0⟩
  | 1 => ⟨-72203103485684283715418157594809418760568366659 /
      3125000000000000000000000000000000000000000000000, 1/10^21⟩
  | 2 => ⟨12416702689457208786192822260440886310080868461 /
      50000000000000000000000000000000000000000000000000, 1/10^21⟩
  | 3 => ⟨-83717631399247493049431472120541388567852411 /
      50000000000000000000000000000000000000000000000000, 1/10^22⟩
  | 4 => ⟨401534871052185585562329495387503137062931 /
      50000000000000000000000000000000000000000000000000, 1/10^23⟩
  | 5 => ⟨-735033939507466653277315658679455732617 /
      25000000000000000000000000000000000000000000000000, 1/10^24⟩
  | 6 => ⟨8598594613395154178313043220336253331 /
      100000000000000000000000000000000000000000000000000, 1/10^24⟩
  | 7 => ⟨-2592334344832147982997324397047571 /
      12500000000000000000000000000000000000000000000000, 1/10^25⟩
  | 8 => ⟨21119312451612270425471462183 /
      50000000000000000000000000000000000000000000000, 1/10^24⟩
  | _ => ⟨0, 1⟩

def normalizedCoefficientEnvelope17 (j : Fin 9) : Box :=
  ⟨(normalizedCoefficientCandidate17 j).center -
      (normalizedCoefficientCandidate17 j).radius,
    (normalizedCoefficientCandidate17 j).center +
      (normalizedCoefficientCandidate17 j).radius⟩

private def normalizedCoefficientResidualBox17 (j : Fin 9) : Box :=
  (nativeCoefficientBox17 j).sub
    ((Box.point (normalizedCoefficientCandidate17 j).center).mul
      (nativeCoefficientBox17 ⟨0, by omega⟩))

private def normalizedCoefficientResidualEnvelope17 (j : Fin 9) : Box :=
  ⟨-((normalizedCoefficientCandidate17 j).radius * 49/100),
    (normalizedCoefficientCandidate17 j).radius * 49/100⟩

/-- Exact integer-grid enclosures of the residual boxes.  These small
intermediate certificates keep the source-table reduction separate from the
rational comparison against the requested coefficient radii. -/
private def normalizedCoefficientResidualGrid17 : Fin 9 → GridBox
  | ⟨0, _⟩ => ⟨-702249010, 702249010⟩
  | ⟨1, _⟩ => ⟨-469587202, 469587165⟩
  | ⟨2, _⟩ => ⟨-171523537, 171523240⟩
  | ⟨3, _⟩ => ⟨-27884629, 27885179⟩
  | ⟨4, _⟩ => ⟨-3028230, 3027849⟩
  | ⟨5, _⟩ => ⟨-374181, 374315⟩
  | ⟨6, _⟩ => ⟨-69071, 69082⟩
  | ⟨7, _⟩ => ⟨-39806, 39732⟩
  | ⟨8, _⟩ => ⟨-398584, 398661⟩

private theorem normalized_coefficient_residual_grid17 (j : Fin 9)
    (hj : 1 ≤ j.val) :
    GridBox.ofBox (normalizedCoefficientResidualBox17 j) =
      normalizedCoefficientResidualGrid17 j := by
  fin_cases j <;> norm_num at hj
  all_goals decide +kernel

/-- The correlated residual boxes fit inside the normalized coefficient
envelopes after multiplying the permitted ratio error by the independent
source lower bound `c₀ > 0.49`. -/
theorem normalized_coefficient_residual_box17_subset (j : Fin 9)
    (hj : 1 ≤ j.val) :
    (normalizedCoefficientResidualBox17 j).Subset
      (normalizedCoefficientResidualEnvelope17 j) := by
  have hgrid := normalized_coefficient_residual_grid17 j hj
  have hrounded := grid_toBox_ofBox_contains (normalizedCoefficientResidualBox17 j)
  have htable :
      (GridBox.toBox (GridBox.ofBox (normalizedCoefficientResidualBox17 j))).Subset
        (normalizedCoefficientResidualEnvelope17 j) := by
    rw [hgrid]
    fin_cases j
    · norm_num at hj
    all_goals norm_num [normalizedCoefficientResidualEnvelope17,
      normalizedCoefficientCandidate17, normalizedCoefficientResidualGrid17,
      GridBox.toBox, grid_denominator_rat_value, Box.Subset]
  exact ⟨htable.1.trans hrounded.1, hrounded.2.trans htable.2⟩

theorem native_c0_gt_49_100 :
    (49/100 : ℝ) < C3CofactorCorrelation.nativeC 0 := by
  have h := C3CofactorCorrelation.native_even_coefficient_candidate_contains
    (⟨0, by omega⟩ : Fin 7)
  have hl := (abs_le.mp h).1
  norm_num [C3Cofactor.candidateCoefficientBall] at hl
  linarith

def normalizedNativeCoefficient17 (j : Fin 9) : ℝ :=
  C3CofactorCorrelation.nativeC j.val / C3CofactorCorrelation.nativeC 0

theorem normalized_native_coefficient17_contains (j : Fin 9) :
    (normalizedCoefficientCandidate17 j).Contains
      (normalizedNativeCoefficient17 j) := by
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hj]
    have hpos := lt_trans (by norm_num : (0 : ℝ) < 49/100) native_c0_gt_49_100
    simp [normalizedNativeCoefficient17, normalizedCoefficientCandidate17,
      RationalBall.Contains, ne_of_gt hpos]
  · have hj : 1 ≤ j.val := by omega
    have hcj := native_coefficient_box17_contains j
    have hc0 := native_coefficient_box17_contains (⟨0, by omega⟩ : Fin 9)
    have hprod := Box.mul_contains
      (Box.point_contains (normalizedCoefficientCandidate17 j).center) hc0
    have hdiff := Box.sub_contains hcj hprod
    have hres := Box.subset_contains
      (normalized_coefficient_residual_box17_subset j hj) hdiff
    have hnum :
        |C3CofactorCorrelation.nativeC j.val -
          (normalizedCoefficientCandidate17 j).center *
            C3CofactorCorrelation.nativeC 0| ≤
          ((normalizedCoefficientCandidate17 j).radius * 49/100 : ℚ) := by
      have hres' :
          (-((normalizedCoefficientCandidate17 j).radius * 49/100 : ℚ) : ℝ) ≤
              C3CofactorCorrelation.nativeC j.val -
                (normalizedCoefficientCandidate17 j).center *
                  C3CofactorCorrelation.nativeC 0 ∧
            C3CofactorCorrelation.nativeC j.val -
                (normalizedCoefficientCandidate17 j).center *
                  C3CofactorCorrelation.nativeC 0 ≤
              ((normalizedCoefficientCandidate17 j).radius * 49/100 : ℚ) := by
        simpa [normalizedCoefficientResidualEnvelope17,
          normalizedCoefficientResidualBox17, Box.Contains] using hres
      rw [abs_le]
      simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using hres'
    have h0 := native_c0_gt_49_100
    have h0pos : 0 < C3CofactorCorrelation.nativeC 0 :=
      lt_trans (by norm_num : (0 : ℝ) < 49/100) h0
    have heq : normalizedNativeCoefficient17 j -
        (normalizedCoefficientCandidate17 j).center =
          (C3CofactorCorrelation.nativeC j.val -
            (normalizedCoefficientCandidate17 j).center *
              C3CofactorCorrelation.nativeC 0) /
            C3CofactorCorrelation.nativeC 0 := by
      unfold normalizedNativeCoefficient17
      field_simp [ne_of_gt h0pos]
    change |normalizedNativeCoefficient17 j -
      (normalizedCoefficientCandidate17 j).center| ≤
        (normalizedCoefficientCandidate17 j).radius
    rw [heq, abs_div, abs_of_pos h0pos]
    apply (div_le_iff₀ h0pos).2
    have hrQ : 0 ≤ (normalizedCoefficientCandidate17 j).radius := by
      fin_cases j <;> norm_num [normalizedCoefficientCandidate17]
    have hr : 0 ≤ ((normalizedCoefficientCandidate17 j).radius : ℝ) := by
      exact_mod_cast hrQ
    have hcompare := mul_le_mul_of_nonneg_left (le_of_lt h0) hr
    calc
      |C3CofactorCorrelation.nativeC j.val -
          (normalizedCoefficientCandidate17 j).center *
            C3CofactorCorrelation.nativeC 0| ≤
          ((normalizedCoefficientCandidate17 j).radius * 49/100 : ℚ) := hnum
      _ = (normalizedCoefficientCandidate17 j).radius * (49/100:ℝ) := by
        push_cast
        ring_nf
      _ ≤ (normalizedCoefficientCandidate17 j).radius * C3CofactorCorrelation.nativeC 0 :=
        hcompare

end
end C3ShiftedFourth
