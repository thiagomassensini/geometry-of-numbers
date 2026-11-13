import ResidualPadé
import SourceNative
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Native adapter and regressions for the division-free cofactor residual. -/

namespace C3ResidualPade

open CarrySourceBezout CarrySelfAdjointOperator
open scoped Matrix

noncomputable section
set_option autoImplicit false

abbrev nativeC : ℕ → ℝ := CarrySourceBezout.nativeC
abbrev nativeH : ℕ → ℝ := CarrySourceBezout.nativeH

theorem hankelPrefix_eq_sourceMomentMatrix (h : ℕ → ℝ) (s n : ℕ) :
    hankelPrefix h s n = CarrySelfAdjointOperator.sourceMomentMatrix h s n := by
  ext i j
  simp [hankelPrefix, CarrySelfAdjointOperator.sourceMomentMatrix,
    Nat.add_comm, Nat.add_left_comm]

theorem hankelCoupling_eq_sourceMomentCoupling (h : ℕ → ℝ) (s n : ℕ) :
    hankelCoupling h s n = CarrySelfAdjointOperator.sourceMomentCoupling h s n := by
  ext i
  simp [hankelCoupling, CarrySelfAdjointOperator.sourceMomentCoupling,
    Nat.add_comm, Nat.add_left_comm]

theorem hankelBorder_eq_extendedSourceMatrix (h : ℕ → ℝ) (s n : ℕ) :
    hankelBorder h s n = CarrySelfAdjointOperator.sourceMomentMatrix h s (n+1) := by
  ext i j
  simp [hankelBorder, CarrySelfAdjointOperator.sourceMomentMatrix,
    Nat.add_comm, Nat.add_left_comm]

theorem hankelPivot_eq_sourceMomentSchur (h : ℕ → ℝ) (s n : ℕ) :
    hankelPivot h s n = CarrySelfAdjointOperator.sourceMomentSchur h s n := by
  simp [hankelPivot, CarrySelfAdjointOperator.sourceMomentSchur,
    hankelPrefix_eq_sourceMomentMatrix, hankelCoupling_eq_sourceMomentCoupling,
    Nat.add_comm]

theorem native_residual_recurrence :
    characteristicSeries nativeC * momentSeries nativeH =
      -(PowerSeries.derivative ℝ (characteristicSeries nativeC)) := by
  change CarrySourceBezout.sourceSeries nativeC * CarrySourceBezout.momentSeries nativeH =
    -(PowerSeries.derivative ℝ (CarrySourceBezout.sourceSeries nativeC))
  exact CarrySourceBezout.native_source_recurrence

theorem native_prefixDet_ne_zero (s n : ℕ)
    (hA : IsUnit (CarrySelfAdjointOperator.sourceMomentMatrix nativeH s n)) :
    (hankelPrefix nativeH s n).det ≠ 0 := by
  have hunit : IsUnit (CarrySelfAdjointOperator.sourceMomentMatrix nativeH s n).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hne := hunit.ne_zero
  rw [← hankelPrefix_eq_sourceMomentMatrix] at hne
  exact hne

theorem native_normalized_residual_coeff_low (s n k : ℕ)
    (hA : IsUnit (CarrySelfAdjointOperator.sourceMomentMatrix nativeH s n))
    (hk : k < 2*n+s) :
    PowerSeries.coeff k (normalizedResidual nativeC nativeH s n
      (native_prefixDet_ne_zero s n hA)) = 0 :=
  normalizedResidual_coeff_low nativeC nativeH s n k
    (native_prefixDet_ne_zero s n hA) native_residual_recurrence hk

theorem native_normalized_residual_coeff_leading (s n : ℕ)
    (hA : IsUnit (CarrySelfAdjointOperator.sourceMomentMatrix nativeH s n)) :
    PowerSeries.coeff (2*n+s) (normalizedResidual nativeC nativeH s n
      (native_prefixDet_ne_zero s n hA)) =
      nativeC 0 * CarrySelfAdjointOperator.sourceMomentSchur nativeH s n := by
  rw [normalizedResidual_coeff_leading nativeC nativeH s n
    (native_prefixDet_ne_zero s n hA) native_residual_recurrence,
    hankelPivot_eq_sourceMomentSchur]

theorem native_normalized_residual_eq_sourceRemainder (s n : ℕ)
    (hA : IsUnit (CarrySelfAdjointOperator.sourceMomentMatrix nativeH s n)) :
    PowerSeries.coeff (2*n+s) (normalizedResidual nativeC nativeH s n
      (native_prefixDet_ne_zero s n hA)) =
      CarrySelfAdjointOperator.nativeSourceSchurRemainder s n := by
  rw [native_normalized_residual_coeff_leading s n hA,
    CarrySelfAdjointOperator.nativeSourceSchurRemainder_eq]

theorem native_even_third_residual_coefficient
    (hA : IsUnit (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 0 3)) :
    PowerSeries.coeff 6 (normalizedResidual nativeC nativeH 0 3
      (native_prefixDet_ne_zero 0 3 hA)) =
      nativeC 0 * CarrySelfAdjointOperator.sourceMomentSchur nativeH 0 3 := by
  simpa using native_normalized_residual_coeff_leading 0 3 hA

theorem native_odd_third_residual_coefficient
    (hA : IsUnit (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 1 3)) :
    PowerSeries.coeff 7 (normalizedResidual nativeC nativeH 1 3
      (native_prefixDet_ne_zero 1 3 hA)) =
      nativeC 0 * CarrySelfAdjointOperator.sourceMomentSchur nativeH 1 3 := by
  simpa using native_normalized_residual_coeff_leading 1 3 hA

theorem native_even_third_newCoefficientIndex : 2*3+0+1=7 := by norm_num

theorem native_odd_third_newCoefficientIndex : 2*3+1+1=8 := by norm_num

theorem native_even_third_newCharacteristicCoefficient :
    PowerSeries.coeff 7 (characteristicSeries nativeC) = nativeC 7 := by
  simp [characteristicSeries]

theorem native_odd_third_newCharacteristicCoefficient :
    PowerSeries.coeff 8 (characteristicSeries nativeC) = nativeC 8 := by
  simp [characteristicSeries]

theorem native_even_third_newDerivativeCoefficient :
    PowerSeries.coeff 6 (PowerSeries.derivative ℝ (characteristicSeries nativeC)) =
      7 * nativeC 7 := by
  rw [PowerSeries.coeff_derivative]
  simp [characteristicSeries, PowerSeries.coeff_mk]
  ring

theorem native_odd_third_newDerivativeCoefficient :
    PowerSeries.coeff 7 (PowerSeries.derivative ℝ (characteristicSeries nativeC)) =
      8 * nativeC 8 := by
  rw [PowerSeries.coeff_derivative]
  simp [characteristicSeries, PowerSeries.coeff_mk]
  ring

/-! Fixed-order regressions: the universal coefficient theorem specializes at
n=0 and n=1, while the constant sequence gives a rank-one singular prefix. -/

example (h : ℕ → ℝ) (s : ℕ) :
    PowerSeries.coeff 0
      (cofactorReversed h s 0 * shiftedMoments h s - cofactorNumerator h s 0) =
        hankelDefect h s 0 := by
  simpa using cofactorDefect_coeff_leading h s 0

example (h : ℕ → ℝ) (s : ℕ) :
    PowerSeries.coeff 1
      (cofactorReversed h s 1 * shiftedMoments h s - cofactorNumerator h s 1) = 0 := by
  exact cofactorDefect_coeff_low h s 1 1 (by omega)

example (h : ℕ → ℝ) (s : ℕ) :
    PowerSeries.coeff 2
      (cofactorReversed h s 1 * shiftedMoments h s - cofactorNumerator h s 1) =
        hankelDefect h s 1 := by
  simpa using cofactorDefect_coeff_leading h s 1

def constantMoments : ℕ → ℝ := fun _ => 1

example : hankelPrefix constantMoments 0 2 = !![1,1;1,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hankelPrefix, constantMoments]

example : (hankelPrefix constantMoments 0 2).det = 0 := by
  norm_num [hankelPrefix, constantMoments, Matrix.det_fin_two]

example : (hankelPrefix constantMoments 0 2).rank = 1 := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hrange : Set.range (hankelPrefix constantMoments 0 2).col =
      {(fun _ : Fin 2 => (1 : ℝ))} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      funext i
      simp [hankelPrefix, constantMoments]
    · intro hx
      subst x
      exact ⟨0, by
        funext i
        simp [hankelPrefix, constantMoments]⟩
  rw [hrange]
  have hv : (fun _ : Fin 2 => (1 : ℝ)) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  simpa using (finrank_span_singleton hv)

example : (hankelPrefix constantMoments 0 2) 0 0 ≠ 0 := by
  norm_num [hankelPrefix, constantMoments]

example : PowerSeries.coeff 4
    (cofactorReversed constantMoments 0 2 * shiftedMoments constantMoments 0 -
      cofactorNumerator constantMoments 0 2) = 0 := by
  calc
    PowerSeries.coeff 4
        (cofactorReversed constantMoments 0 2 * shiftedMoments constantMoments 0 -
          cofactorNumerator constantMoments 0 2) = hankelDefect constantMoments 0 2 := by
            simpa using cofactorDefect_coeff_leading constantMoments 0 2
    _ = 0 := by
      rw [hankelDefect, Matrix.det_fin_three]
      norm_num [hankelBorder, constantMoments]

def signedMoments : ℕ → ℝ := fun k => if Even k then (k:ℝ)+1 else -((k:ℝ)+1)

example : PowerSeries.coeff 3
    (cofactorReversed signedMoments 0 2 * shiftedMoments signedMoments 0 -
      cofactorNumerator signedMoments 0 2) = 0 := by
  exact cofactorDefect_coeff_low signedMoments 0 2 3 (by norm_num)

example : PowerSeries.coeff 4
    (cofactorReversed signedMoments 0 2 * shiftedMoments signedMoments 0 -
      cofactorNumerator signedMoments 0 2) = hankelDefect signedMoments 0 2 := by
  simpa using cofactorDefect_coeff_leading signedMoments 0 2

end
end C3ResidualPade
