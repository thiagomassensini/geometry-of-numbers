import LiteralTfvd

namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

def sourceResponse (c : ℕ → ℂ) (b : Bool) : PowerSeries ℂ :=
  if b then -(PowerSeries.derivative ℂ (sourceSeries c))
  else PowerSeries.X * -(PowerSeries.derivative ℂ (sourceSeries c))

def responseCoefficient (c : ℕ → ℂ) (b : Bool) (n : ℕ) : ℂ :=
  PowerSeries.coeff n (sourceResponse c b)

theorem mixed_kernel_coefficient (c d : ℕ → ℂ) (b : Bool) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (mixedSourceKernel c d b)) =
      (∑ k ∈ Finset.range (j+1), d (j-k)*responseCoefficient c b (i+k+1)) -
      ∑ k ∈ Finset.range (j+1), responseCoefficient c b (j-k)*d (i+k+1) := by
  change PowerSeries.coeff j (PowerSeries.coeff i
    (right (sourceSeries d)*divided (sourceResponse c b) -
      right (sourceResponse c b)*divided (sourceSeries d))) = _
  simp only [map_sub, right, PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sourceSeries, divided, responseCoefficient]

def coefficientBudget (c d : ℕ → ℂ) (b : Bool) (i j : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (j+1), ‖d (j-k)‖*‖responseCoefficient c b (i+k+1)‖) +
    ∑ k ∈ Finset.range (j+1), ‖responseCoefficient c b (j-k)‖*‖d (i+k+1)‖

theorem coefficientBudget_nonneg (c d : ℕ → ℂ) (b : Bool) (i j : ℕ) :
    0 ≤ coefficientBudget c d b i j := by
  unfold coefficientBudget
  positivity

theorem mixed_coefficient_bound (c d : ℕ → ℂ) (b : Bool) (i j : ℕ) :
    ‖PowerSeries.coeff j (PowerSeries.coeff i (mixedSourceKernel c d b))‖ ≤
      coefficientBudget c d b i j := by
  rw [mixed_kernel_coefficient]
  apply (norm_sub_le _ _).trans
  exact add_le_add
    ((norm_sum_le _ _).trans_eq (by simp))
    ((norm_sum_le _ _).trans_eq (by simp))

def directionalBudget (c d : ℕ → ℂ) (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) : ℝ :=
  ∑ i : Fin r, ∑ j : Fin r, |x i| * coefficientBudget c d b i.val j.val * |y j|

theorem directionalBudget_nonneg (c d : ℕ → ℂ) (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) : 0 ≤ directionalBudget c d b r x y := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (coefficientBudget_nonneg _ _ _ _ _)) (abs_nonneg _)

theorem mixed_direction_bound (c d : ℕ → ℂ) (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) :
    ‖complexPair (coefficientBlock (mixedSourceKernel c d b) r)
      (fun i => (x i : ℂ)) (fun j => (y j : ℂ))‖ ≤ directionalBudget c d b r x y := by
  simp only [complexPair, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mixed_coefficient_bound c d b i.val j.val) (abs_nonneg _))
    (abs_nonneg _) |>.trans_eq (by ring)

def literalErrorBudget (M P : ℕ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) : ℝ :=
  directionalBudget (literalHead M) (literalTail P) b r x y +
    directionalBudget (literalTail M) (literalHead P) b r x y +
    directionalBudget (literalTail M) (literalTail P) b r x y

/-- A finite, explicitly evaluable error, without any Hankel sign input. -/
theorem literal_error_bound (M P : ℕ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
      literalTerm M P true true b r x y‖ ≤ literalErrorBudget M P b r x y := by
  rw [literal_four_terms M P b r x y]
  rw [show literalTerm M P true true b r x y + literalTerm M P true false b r x y +
      literalTerm M P false true b r x y + literalTerm M P false false b r x y -
        literalTerm M P true true b r x y =
      (literalTerm M P true false b r x y+literalTerm M P false true b r x y)+
        literalTerm M P false false b r x y by ring]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_add_le _ _).trans (add_le_add
      (mixed_direction_bound (literalHead M) (literalTail P) b r x y)
      (mixed_direction_bound (literalTail M) (literalHead P) b r x y))
  · exact mixed_direction_bound (literalTail M) (literalTail P) b r x y

/-- This sufficient inequality compares finite source data and a proven error;
it is not used as an unconditional hypothesis about the Carry source. -/
theorem native_residual_pos_of_literal_margin (M P : ℕ) (b : Bool) (n : ℕ)
    (hA : IsUnit (CarrySelfAdjointOperator.sourceMomentMatrix nativeH (if b then 1 else 0) n))
    (hmargin : literalErrorBudget M P b (n+1)
      (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)
      (monicSourceDirection nativeC nativeH (if b then 1 else 0) n) <
        (literalResidualTerm M P true true b n).re) :
    0 < CarrySelfAdjointOperator.nativeSourceSchurRemainder (if b then 1 else 0) n := by
  have he := literal_error_bound M P b (n+1)
    (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)
    (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)
  rw [native_monicSourceDirection_remainder b n hA] at he
  have hr := Complex.abs_re_le_norm
    (((nativeC 0*CarrySelfAdjointOperator.nativeSourceSchurRemainder (if b then 1 else 0) n : ℝ):ℂ)-
      literalResidualTerm M P true true b n)
  have hc : 0 < nativeC 0 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/3)
    CarrySelfAdjointOperator.completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have hne : (literalResidualTerm M P true true b n).re -
      literalErrorBudget M P b (n+1)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) n) ≤
          nativeC 0*CarrySelfAdjointOperator.nativeSourceSchurRemainder (if b then 1 else 0) n := by
    have hh := (abs_le.mp (hr.trans he)).1
    simp only [Complex.sub_re, Complex.ofReal_re] at hh
    linarith
  exact (mul_pos_iff_of_pos_left hc).mp (lt_of_lt_of_le (sub_pos.mpr hmargin) hne)

end
end CarrySourceBezout
