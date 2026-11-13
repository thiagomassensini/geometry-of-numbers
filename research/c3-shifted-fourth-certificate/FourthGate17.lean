import HighCoefficientBoxes17
import SourceBezout

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets C3CofactorCorrelation CarrySourceBezout
  C3Cofactor
open scoped BigOperators Matrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

private def sourceResponseReal (c : ℕ → ℝ) : PowerSeries ℝ :=
  -(PowerSeries.derivative ℝ (sourceSeries c))

private def sourceResponseCoefficientReal (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n (sourceResponseReal c)

private theorem mixed_source_kernel_coefficient_real
    (c d : ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i
      (bezout (sourceResponseReal c) (sourceSeries d))) =
      (∑ k ∈ Finset.range (j+1), d (j-k)*sourceResponseCoefficientReal c (i+k+1)) -
        ∑ k ∈ Finset.range (j+1),
          sourceResponseCoefficientReal c (j-k)*d (i+k+1) := by
  change PowerSeries.coeff j (PowerSeries.coeff i
    (right (sourceSeries d)*divided (sourceResponseReal c) -
        right (sourceResponseReal c)*divided (sourceSeries d))) = _
  simp only [map_sub, right, PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sourceSeries, divided, sourceResponseCoefficientReal, sourceResponseReal]

private theorem sourceResponseCoefficientReal_eq
    (c : ℕ → ℝ) (n : ℕ) :
    sourceResponseCoefficientReal c n = -(n+1:ℝ)*c (n+1) := by
  simp [sourceResponseCoefficientReal, sourceResponseReal, sourceSeries,
    PowerSeries.coeff_derivative]
  ring

private theorem sourceKernel_odd_coefficient_explicit
    (c : ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (sourceKernel c true)) =
      ∑ k ∈ Finset.range (j+1),
        ((j-k+1:ℝ)*c (j-k+1)*c (i+k+1) -
          (i+k+2:ℝ)*c (j-k)*c (i+k+2)) := by
  have h := mixed_source_kernel_coefficient_real c c i j
  change PowerSeries.coeff j (PowerSeries.coeff i
    (bezout (sourceResponseReal c) (sourceSeries c))) = _
  rw [h]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j := by simp only [Finset.mem_range] at hk; omega
  rw [sourceResponseCoefficientReal_eq, sourceResponseCoefficientReal_eq]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hkj]
  ring

def oddFourthB (c : Fin 9 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![
  c 1*c 1-2*(c 0*c 2),
  c 1*c 2-3*(c 0*c 3),
  c 1*c 3-4*(c 0*c 4),
  c 1*c 4-5*(c 0*c 5);
  c 1*c 2-3*(c 0*c 3),
  2*(c 2*c 2)-2*(c 1*c 3)-4*(c 0*c 4),
  2*(c 2*c 3)-3*(c 1*c 4)-5*(c 0*c 5),
  2*(c 2*c 4)-4*(c 1*c 5)-6*(c 0*c 6);
  c 1*c 3-4*(c 0*c 4),
  2*(c 2*c 3)-3*(c 1*c 4)-5*(c 0*c 5),
  3*c 3*c 3-2*(c 2*c 4)-4*(c 1*c 5)-6*(c 0*c 6),
  3*(c 3*c 4)-3*(c 2*c 5)-5*(c 1*c 6)-7*(c 0*c 7);
  c 1*c 4-5*(c 0*c 5),
  2*(c 2*c 4)-4*(c 1*c 5)-6*(c 0*c 6),
  3*(c 3*c 4)-3*(c 2*c 5)-5*(c 1*c 6)-7*(c 0*c 7),
  4*c 4*c 4-2*(c 3*c 5)-4*(c 2*c 6)-6*(c 1*c 7)-8*(c 0*c 8)
]

theorem native_odd_fourth_block_eq :
    coefficientBlock (sourceKernel C3CofactorCorrelation.nativeC true) 4 =
      oddFourthB (fun j => C3CofactorCorrelation.nativeC j.val) := by
  ext i j
  simp only [coefficientBlock]
  change PowerSeries.coeff j.val
      (PowerSeries.coeff i.val (sourceKernel C3CofactorCorrelation.nativeC true)) =
    oddFourthB (fun j => C3CofactorCorrelation.nativeC j.val) i j
  fin_cases i <;> fin_cases j <;>
    rw [sourceKernel_odd_coefficient_explicit] <;>
    simp [oddFourthB, Finset.sum_range_succ] <;> ring

#print axioms native_odd_fourth_block_eq

end
end C3ShiftedFourth
