import FourNativeBoxes
import CentralFourthGate17
import NativeRepartition64
import NativeEvenCertificate

namespace C3ShiftedFourth

open C3Cofactor C3GeneralCofactor CarrySourceBezout CarrySelfAdjointOperator
  C3CofactorCorrelation
open scoped BigOperators Matrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 50000

private def sourceResponseEvenReal17 (c : ℕ → ℝ) : PowerSeries ℝ :=
  PowerSeries.X * (-(PowerSeries.derivative ℝ (sourceSeries c)))

private def sourceResponseEvenCoefficientReal17 (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n (sourceResponseEvenReal17 c)

private theorem mixed_source_even_kernel_coefficient_real17
    (c d : ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i
      (bezout (sourceResponseEvenReal17 c) (sourceSeries d))) =
      (∑ k ∈ Finset.range (j+1), d (j-k)*sourceResponseEvenCoefficientReal17 c (i+k+1)) -
        ∑ k ∈ Finset.range (j+1),
          sourceResponseEvenCoefficientReal17 c (j-k)*d (i+k+1) := by
  change PowerSeries.coeff j (PowerSeries.coeff i
    (right (sourceSeries d)*divided (sourceResponseEvenReal17 c) -
        right (sourceResponseEvenReal17 c)*divided (sourceSeries d))) = _
  simp only [map_sub, right, PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sourceSeries, divided, sourceResponseEvenCoefficientReal17,
    sourceResponseEvenReal17]

private theorem sourceResponseEvenCoefficientReal17_eq
    (c : ℕ → ℝ) (n : ℕ) :
    sourceResponseEvenCoefficientReal17 c n = -(n:ℝ)*c n := by
  cases n with
  | zero => simp [sourceResponseEvenCoefficientReal17, sourceResponseEvenReal17, sourceSeries]
  | succ n =>
      simp [sourceResponseEvenCoefficientReal17, sourceResponseEvenReal17, sourceSeries,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      ring

private theorem sourceKernel_even_coefficient_explicit17
    (c : ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel c false)) =
      ∑ k ∈ Finset.range (j+1),
        (((j:ℝ)-(i:ℝ)-2*(k:ℝ)-1) * c (j-k) * c (i+k+1)) := by
  have h := mixed_source_even_kernel_coefficient_real17 c c i j
  change PowerSeries.coeff j (PowerSeries.coeff i
    (bezout (sourceResponseEvenReal17 c) (sourceSeries c))) = _
  rw [h, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j := by
    simp only [Finset.mem_range] at hk
    omega
  rw [sourceResponseEvenCoefficientReal17_eq, sourceResponseEvenCoefficientReal17_eq]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hkj]
  ring

theorem native_even_fourth_block_eq17 :
    coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 4 =
      evenFourthB17 (fun j => C3CofactorCorrelation.nativeC j.val) := by
  ext i j
  simp only [coefficientBlock]
  change PowerSeries.coeff j.val
      (PowerSeries.coeff i.val (sourceKernel C3CofactorCorrelation.nativeC false)) =
    evenFourthB17 (fun j => C3CofactorCorrelation.nativeC j.val) i j
  fin_cases i <;> fin_cases j <;>
    rw [sourceKernel_even_coefficient_explicit17] <;>
    simp [evenFourthB17, evenAReal17, evenBReal17, evenEReal17,
      evenDReal17, evenFReal17, evenGReal17, evenHReal17, evenIReal17,
      evenJReal17, evenKReal17, Finset.sum_range_succ] <;> ring

private theorem native_even_fourth_block_normalized_scale17 :
    evenFourthB17 (fun j => C3CofactorCorrelation.nativeC j.val) =
      (C3CofactorCorrelation.nativeC 0 ^ 2) • evenFourthB17 normalizedNativeCoefficient17 := by
  have h0pos : 0 < C3CofactorCorrelation.nativeC 0 := native_source_c0_positive_from_boxes
  have hcoeff (j : Fin 9) :
      C3CofactorCorrelation.nativeC j.val = C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 j := by
    unfold normalizedNativeCoefficient17
    field_simp [ne_of_gt h0pos]
  have hnorm0 : normalizedNativeCoefficient17 (0 : Fin 9) = 1 := by
    simp [normalizedNativeCoefficient17, ne_of_gt h0pos]
  have hc1 : C3CofactorCorrelation.nativeC 1 = C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (1 : Fin 9) := by
    simpa using hcoeff (1 : Fin 9)
  have hc2 : C3CofactorCorrelation.nativeC 2 = C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (2 : Fin 9) := by
    simpa using hcoeff (2 : Fin 9)
  have hc3 : C3CofactorCorrelation.nativeC 3 = C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (3 : Fin 9) := by
    simpa using hcoeff (3 : Fin 9)
  have hc4 : C3CofactorCorrelation.nativeC 4 = C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (4 : Fin 9) := by
    simpa using hcoeff (4 : Fin 9)
  have hc5 : C3CofactorCorrelation.nativeC 5 = C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (5 : Fin 9) := by
    simpa using hcoeff (5 : Fin 9)
  have hc6 : C3CofactorCorrelation.nativeC 6 = C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (6 : Fin 9) := by
    simpa using hcoeff (6 : Fin 9)
  have hc7 : C3CofactorCorrelation.nativeC 7 = C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (7 : Fin 9) := by
    simpa using hcoeff (7 : Fin 9)
  have hc8 : C3CofactorCorrelation.nativeC 8 = C3CofactorCorrelation.nativeC 0 * normalizedNativeCoefficient17 (8 : Fin 9) := by
    simpa using hcoeff (8 : Fin 9)
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [evenFourthB17, evenAReal17, evenBReal17, evenEReal17,
      evenDReal17, evenFReal17, evenGReal17, evenHReal17, evenIReal17,
      evenJReal17, evenKReal17, hnorm0, hc1, hc2, hc3, hc4, hc5, hc6, hc7] <;>
    ring

theorem native_even_fourth_bezout_determinant_positive17 :
    0 < (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 4).det := by
  rw [native_even_fourth_block_eq17, native_even_fourth_block_normalized_scale17,
    Matrix.det_smul]
  have hcard : Fintype.card (Fin 4) = 4 := rfl
  rw [hcard]
  have h0pos : 0 < C3CofactorCorrelation.nativeC 0 := native_source_c0_positive_from_boxes
  have hscale : 0 < (C3CofactorCorrelation.nativeC 0 ^ 2) ^ 4 := pow_pos (pow_pos h0pos 2) 4
  have hdet : 0 < (evenFourthB17 normalizedNativeCoefficient17).det := by
    rw [native_normalized_even_fourth_determinant_eq_gate17]
    exact native_normalized_even_fourth_cofactor_gate17
  exact mul_pos hscale hdet

private theorem native_even_fourth_is_border17 :
    coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 4 =
      C3GeneralCofactor.border
        (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 3)
        (sourceCoupling C3CofactorCorrelation.nativeC false 3)
        (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 4
          (Fin.last 3) (Fin.last 3)) := by
  let B := coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 4
  have hsymmetric : B.transpose = B := by
    dsimp [B]
    exact source_block_transpose C3CofactorCorrelation.nativeC nativeH native_source_recurrence false 4
  ext i j
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => rw [C3GeneralCofactor.border_last_last]
    | cast j =>
      rw [C3GeneralCofactor.border_last_castSucc]
      have h := congrFun (congrFun hsymmetric j.castSucc) (Fin.last 3)
      simpa [B, sourceCoupling, coefficientBlock] using h
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      rw [C3GeneralCofactor.border_castSucc_last]
      simp [sourceCoupling, coefficientBlock]
    | cast j =>
      rw [C3GeneralCofactor.border_castSucc_castSucc]
      simp [coefficientBlock]

private theorem native_even_fourth_det_factor_sourceSchur17 :
    (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 4).det =
      (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 3).det *
        sourceSchur C3CofactorCorrelation.nativeC false 3 := by
  let A := coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 3
  let b := sourceCoupling C3CofactorCorrelation.nativeC false 3
  let d := coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 4
    (Fin.last 3) (Fin.last 3)
  have hdetA0 : 0 <
      (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 3).det := by
    have h := C3CofactorChiral.c3_even_third_bezout_det_lower
    have hCarry : 0 <
        (coefficientBlock (sourceKernel CarrySourceBezout.nativeC false) 3).det :=
      lt_trans (by norm_num) h
    simpa [C3CofactorCorrelation.nativeC, CarrySourceBezout.nativeC] using hCarry
  have hAunit : IsUnit A := by
    apply (Matrix.isUnit_iff_isUnit_det A).mpr
    exact isUnit_iff_ne_zero.mpr (ne_of_gt hdetA0)
  letI := hAunit.invertible
  have hadj : A.adjugate = A.det • A⁻¹ := by
    calc
      A.adjugate = (1 : Matrix (Fin 3) (Fin 3) ℝ) * A.adjugate := by simp
      _ = (A⁻¹ * A) * A.adjugate := by rw [Matrix.inv_mul_of_invertible]
      _ = A⁻¹ * (A * A.adjugate) := by rw [Matrix.mul_assoc]
      _ = A⁻¹ * (A.det • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
        rw [Matrix.mul_adjugate]
      _ = A.det • A⁻¹ := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hterm : dotProduct b (A.adjugate.mulVec b) =
      A.det * dotProduct b (A⁻¹.mulVec b) := by
    rw [hadj, Matrix.smul_mulVec]
    simp only [dotProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hterm' : (∑ i : Fin 3, b i * (A.adjugate.mulVec b) i) =
      A.det * dotProduct b (A⁻¹.mulVec b) := by
    simpa [dotProduct] using hterm
  rw [native_even_fourth_is_border17, C3GeneralCofactor.border_det, hterm']
  change A.det * d - A.det * dotProduct b (A⁻¹.mulVec b) =
    A.det * (d - dotProduct b (A⁻¹.mulVec b))
  ring

theorem native_even_fourth_sourceSchur_positive17 :
    0 < sourceSchur C3CofactorCorrelation.nativeC false 3 := by
  have hdetPrefix : 0 <
      (coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC false) 3).det := by
    have h := C3CofactorChiral.c3_even_third_bezout_det_lower
    have hCarry : 0 <
        (coefficientBlock (sourceKernel CarrySourceBezout.nativeC false) 3).det :=
      lt_trans (by norm_num) h
    simpa [C3CofactorCorrelation.nativeC, CarrySourceBezout.nativeC] using hCarry
  have hdetFull := native_even_fourth_bezout_determinant_positive17
  rw [native_even_fourth_det_factor_sourceSchur17] at hdetFull
  exact (mul_pos_iff_of_pos_left hdetPrefix).mp hdetFull

private theorem native_even_prefix3_posDef17 :
    (sourceMomentMatrix nativeH 0 3).PosDef := by
  have hEmpty : (sourceMomentMatrix nativeH 0 0).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
      (sourceMomentMatrix_isHermitian nativeH 0 0)
    intro x hx
    exact (hx (Subsingleton.elim _ _)).elim
  have hc0 : 0 < C3CofactorCorrelation.nativeC 0 := by
    simpa [C3CofactorCorrelation.nativeC, CarrySourceBezout.nativeC] using
      native_source_c0_positive_from_boxes
  have hc1 : C3CofactorCorrelation.nativeC 1 < 0 := by
    have h := lt_trans native_source_c1_negative (by norm_num : -(1/100:ℝ) < 0)
    simpa [C3CofactorCorrelation.nativeC, CarrySourceBezout.nativeC] using h
  have hrec0 := CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment_real_recurrence 0
  have hprod : C3CofactorCorrelation.nativeC 0 * nativeH 0 = -C3CofactorCorrelation.nativeC 1 := by
    simpa [C3CofactorCorrelation.nativeC, nativeH, Finset.sum_range_succ] using hrec0
  have hmoment0 : 0 < nativeH 0 := by
    have hmul : 0 < C3CofactorCorrelation.nativeC 0 * nativeH 0 := by
      rw [hprod]
      exact neg_pos.mpr hc1
    exact (mul_pos_iff_of_pos_left hc0).mp hmul
  have hpivot0 : 0 < sourceMomentSchur nativeH 0 0 := by
    simpa [sourceMomentSchur, sourceMomentCoupling, sourceMomentMatrix] using hmoment0
  have hH1 : (sourceMomentMatrix nativeH 0 1).PosDef :=
    (sourceMomentMatrix_succ_posDef_iff nativeH 0 0 hEmpty).mpr hpivot0
  have hminor2 : 0 < nativeH 0 * nativeH 2 - nativeH 1 ^ 2 := by
    simpa [CarrySourceBezout.nativeH] using
      CarryC3Boxes.canonical_two_even_determinant_pos_from_c3
  have hH2 : (sourceMomentMatrix nativeH 0 2).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
      (sourceMomentMatrix_isHermitian nativeH 0 2)
    intro x hx
    let u := x 0
    let v := x 1
    have hq : dotProduct x (sourceMomentMatrix nativeH 0 2 *ᵥ x) =
        nativeH 0 * u ^ 2 + 2 * nativeH 1 * u * v + nativeH 2 * v ^ 2 := by
      simp [u, v, sourceMomentMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
      ring
    have hcomplete : nativeH 0 * u ^ 2 + 2 * nativeH 1 * u * v + nativeH 2 * v ^ 2 =
        nativeH 0 * (u + nativeH 1 / nativeH 0 * v) ^ 2 +
          ((nativeH 0 * nativeH 2 - nativeH 1 ^ 2) / nativeH 0) * v ^ 2 := by
      field_simp [ne_of_gt hmoment0]
      ring
    simp only [star_trivial]
    rw [hq, hcomplete]
    by_cases hv : v = 0
    · have hu : u ≠ 0 := by
        intro hu
        apply hx
        ext i
        fin_cases i <;> simp [u, v, hu, hv]
      have hpos : 0 < nativeH 0 * u ^ 2 :=
        mul_pos hmoment0 (sq_pos_of_ne_zero hu)
      simpa [hv] using hpos
    · have hratio : 0 <
          (nativeH 0 * nativeH 2 - nativeH 1 ^ 2) / nativeH 0 :=
        div_pos hminor2 hmoment0
      have hterm : 0 <
          ((nativeH 0 * nativeH 2 - nativeH 1 ^ 2) / nativeH 0) * v ^ 2 :=
        mul_pos hratio (sq_pos_of_ne_zero hv)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (le_of_lt hmoment0) (sq_nonneg _)) hterm
  have hpivot2 := C3CofactorChiral.c3_even_third_native_pivot_positive
  exact (sourceMomentMatrix_succ_posDef_iff nativeH 0 2 hH2).mpr hpivot2

theorem native_even_fourth_momentSchur_positive17 :
    0 < sourceMomentSchur nativeH 0 3 := by
  have hA : IsUnit (sourceMomentMatrix nativeH 0 3) :=
    native_even_prefix3_posDef17.isUnit
  have hscale := sourceSchur_eq_scaled C3CofactorCorrelation.nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
    native_source_recurrence false 3 hA
  have hpivot := native_even_fourth_sourceSchur_positive17
  rw [hscale] at hpivot
  have hc0 : 0 < C3CofactorCorrelation.nativeC 0 := by
    simpa [C3CofactorCorrelation.nativeC, CarrySourceBezout.nativeC] using
      native_source_c0_positive_from_boxes
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hc0)).mp hpivot

theorem native_even_fourth_moment_posDef17 :
    (sourceMomentMatrix nativeH 0 4).PosDef := by
  exact (sourceMomentMatrix_succ_posDef_iff nativeH 0 3
    native_even_prefix3_posDef17).mpr native_even_fourth_momentSchur_positive17

#print axioms native_even_fourth_momentSchur_positive17
#print axioms native_even_fourth_moment_posDef17

end
end C3ShiftedFourth
