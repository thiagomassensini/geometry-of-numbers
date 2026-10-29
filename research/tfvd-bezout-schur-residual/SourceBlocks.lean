module
public import SourceBezout

@[expose] public section
namespace CarrySourceBezout
noncomputable section

theorem source_even_two (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c false) 2 =
      !![-c 0*c 1, -2*c 0*c 2;
         -2*c 0*c 2, -c 1*c 2-3*c 0*c 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coefficientBlock, sourceKernel, bezout, right, divided, sourceSeries,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      PowerSeries.coeff_derivative, PowerSeries.coeff_X, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_X_mul, Finset.sum_range_succ] <;> ring

theorem source_odd_two (c : ℕ → ℝ) :
    coefficientBlock (sourceKernel c true) 2 =
      !![c 1^2-2*c 0*c 2, c 1*c 2-3*c 0*c 3;
         c 1*c 2-3*c 0*c 3, 2*c 2^2-2*c 1*c 3-4*c 0*c 4] := by
  have hd : PowerSeries.constantCoeff (PowerSeries.derivative ℝ (PowerSeries.mk c)) = c 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [PowerSeries.coeff_derivative]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coefficientBlock, sourceKernel, bezout, right, divided, sourceSeries,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      PowerSeries.coeff_derivative, Finset.sum_range_succ, hd] <;> ring

theorem source_even_two_det (c : ℕ → ℝ) :
    (coefficientBlock (sourceKernel c false) 2).det =
      c 0*c 1^2*c 2 + 3*c 0^2*c 1*c 3 - 4*c 0^2*c 2^2 := by
  rw [source_even_two, Matrix.det_fin_two]
  norm_num
  ring

/-- An algebraic control sequence, NOT a substitute for the Carry source. -/
def negativeControl : ℕ → ℝ := fun n =>
  if n = 0 then 1 else if n = 1 then -1 else if n = 2 then -1 else 0

theorem negative_control_center : negativeControl 0 = 1 := by
  norm_num [negativeControl]

theorem negative_control_source_det :
    (coefficientBlock (sourceKernel negativeControl false) 2).det = -5 := by
  rw [source_even_two_det]
  norm_num [negativeControl]

/-- Bezout provenance and nonzero c0 alone do not imply a positive kernel. -/
theorem negative_control_not_posSemidef :
    ¬(coefficientBlock (sourceKernel negativeControl false) 2).PosSemidef := by
  intro hp
  have hd := hp.diag_nonneg (i := (1 : Fin 2))
  rw [source_even_two] at hd
  norm_num [negativeControl] at hd

/-- Full retention of the source does not itself determine the sign. -/
theorem negative_control_entire_source :
    sourceSeries negativeControl =
      (1-PowerSeries.X-PowerSeries.X^2 : PowerSeries ℝ) := by
  apply PowerSeries.ext
  intro n
  simp [sourceSeries, negativeControl, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  split_ifs <;> simp_all

def negativeControlH (n : ℕ) : ℝ := PowerSeries.coeff n
  (-(PowerSeries.derivative ℝ (sourceSeries negativeControl)) *
    (sourceSeries negativeControl)⁻¹)

/-- The same logarithmic recurrence holds in every order for this control. -/
theorem negative_control_recurrence : SourceRecurrence negativeControl negativeControlH := by
  have hm : momentSeries negativeControlH =
      -(PowerSeries.derivative ℝ (sourceSeries negativeControl)) *
        (sourceSeries negativeControl)⁻¹ := by
    apply PowerSeries.ext
    intro n
    simp [momentSeries, negativeControlH]
  have hz : PowerSeries.constantCoeff (sourceSeries negativeControl) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    norm_num [sourceSeries, negativeControl]
  change sourceSeries negativeControl * momentSeries negativeControlH = _
  rw [hm]
  calc
    _ = -(PowerSeries.derivative ℝ (sourceSeries negativeControl)) *
        (sourceSeries negativeControl * (sourceSeries negativeControl)⁻¹) := by ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel _ hz, mul_one]

theorem negative_control_hankel_not_posSemidef :
    ¬(hankelMatrix negativeControlH 0 2).PosSemidef := by
  intro hp
  have hn := (source_bezout_posSemidef_iff negativeControl negativeControlH
    negative_control_recurrence (by norm_num [negativeControl]) false 2).mpr hp
  exact negative_control_not_posSemidef hn

end
end CarrySourceBezout
