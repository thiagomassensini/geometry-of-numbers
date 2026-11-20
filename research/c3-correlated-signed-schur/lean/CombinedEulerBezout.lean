import SignedSourceTail

/-!
For the EVEN Schur sector, B and p use the SAME source-lifted vector.
The two source parity response operators combine into ONE local weighted
Bezout response. This does not claim positivity of its kernel.
-/
namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1300000

def combinedEulerResponse (c : ℕ → ℝ) (alpha betaA : ℝ) :
    PowerSeries ℝ :=
  ((PowerSeries.C alpha - PowerSeries.C betaA * PowerSeries.X) *
    (-(PowerSeries.derivative ℝ (sourceSeries c))))

def combinedEulerKernel (c : ℕ → ℝ) (alpha betaA : ℝ) :
    BiSeries ℝ :=
  bezout (combinedEulerResponse c alpha betaA) (sourceSeries c)

theorem left_C_eq_right_C (x : ℝ) :
    left (PowerSeries.C x) = right (PowerSeries.C x) := by
  simp [left, right]

theorem combinedEulerKernel_eq_two_parities
    (c : ℕ → ℝ) (alpha betaA : ℝ) :
    combinedEulerKernel c alpha betaA =
      right (PowerSeries.C alpha)*sourceKernel c true -
      right (PowerSeries.C betaA)*sourceKernel c false := by
  apply mul_left_cancel₀ uv_ne_zero
  unfold combinedEulerKernel combinedEulerResponse
  change uv * bezout
    ((PowerSeries.C alpha - PowerSeries.C betaA * PowerSeries.X) *
        (-(PowerSeries.derivative ℝ (sourceSeries c))))
    (sourceSeries c) =
    uv*(right (PowerSeries.C alpha) *
        bezout (-(PowerSeries.derivative ℝ (sourceSeries c))) (sourceSeries c) -
      right (PowerSeries.C betaA) *
        bezout (PowerSeries.X * -(PowerSeries.derivative ℝ (sourceSeries c)))
          (sourceSeries c))
  rw [bezout_numerator]
  rw [show uv*(right (PowerSeries.C alpha) *
       bezout (-(PowerSeries.derivative ℝ (sourceSeries c))) (sourceSeries c) -
     right (PowerSeries.C betaA) *
       bezout (PowerSeries.X * -(PowerSeries.derivative ℝ (sourceSeries c)))
         (sourceSeries c)) =
    right (PowerSeries.C alpha) * (uv*bezout
      (-(PowerSeries.derivative ℝ (sourceSeries c))) (sourceSeries c)) -
    right (PowerSeries.C betaA) * (uv*bezout
      (PowerSeries.X * -(PowerSeries.derivative ℝ (sourceSeries c)))
      (sourceSeries c)) by ring]
  rw [bezout_numerator, bezout_numerator]
  simp only [map_sub, map_mul, map_neg, left_C_eq_right_C]
  ring


/-- Multiplication by a scalar in the original common source jet scales
the entire coefficient block; no scalar is smuggled into a moment definition. -/
theorem coefficientBlock_const_source_mul
    (lambda : ℝ) (f : BiSeries ℝ) (r : ℕ) :
    coefficientBlock (right (PowerSeries.C lambda) * f) r =
      lambda • coefficientBlock f r := by
  ext i j
  simp [coefficientBlock, right, PowerSeries.coeff_C_mul, Matrix.smul_apply,
    smul_eq_mul]

/-- The common weighted Euler–Schur source is literally one Bezout block,
for any test direction, in the even Schur sector. -/
theorem combinedEulerKernel_pair
    (c : ℕ → ℝ) (alpha betaA : ℝ) (r : ℕ) (x y : Fin r → ℝ) :
    matrixPair (coefficientBlock (combinedEulerKernel c alpha betaA) r) x y =
      alpha * matrixPair (coefficientBlock (sourceKernel c true) r) x y -
      betaA * matrixPair (coefficientBlock (sourceKernel c false) r) x y := by
  rw [combinedEulerKernel_eq_two_parities]
  have hb : coefficientBlock
      (right (PowerSeries.C alpha)*sourceKernel c true -
       right (PowerSeries.C betaA)*sourceKernel c false) r =
       alpha • coefficientBlock (sourceKernel c true) r -
       betaA • coefficientBlock (sourceKernel c false) r := by
    have hsub (A B : BiSeries ℝ) :
        coefficientBlock (A-B) r = coefficientBlock A r - coefficientBlock B r := by
      ext i j
      simp [coefficientBlock]
    rw [hsub, coefficientBlock_const_source_mul,
       coefficientBlock_const_source_mul]
  rw [hb]
  simp only [matrixPair, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]


/-- The native even-Schur signed correction is ONE ORIGINAL Bezout
quadratic probe with response (alpha-betaA*X)*(-C').
The source c stays nativeC and the source direction is the transported
actual Schur vector; no new positive measure is inserted. -/
theorem native_even_signed_S_one_response
    (n : ℕ) (v : Fin (n+1) → ℝ) (alpha betaA : ℝ) :
    alpha * matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 1 (n+1)) v v -
    betaA * matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 0 (n+1)) v v =
      matrixPair (coefficientBlock (combinedEulerKernel nativeC alpha betaA) (n+1))
        (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) := by
  have hB : matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 1 (n+1)) v v =
    matrixPair (coefficientBlock (sourceKernel nativeC true) (n+1))
      (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) := by
    simpa using native_mixed_pair_transport true (n+1) v v
  have hP : matrixPair (CarrySelfAdjointOperator.sourceMomentMatrix nativeH 0 (n+1)) v v =
    matrixPair (coefficientBlock (sourceKernel nativeC false) (n+1))
      (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) := by
    simpa using native_mixed_pair_transport false (n+1) v v
  rw [hB,hP]
  exact (combinedEulerKernel_pair nativeC alpha betaA (n+1)
    (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v)).symm

end
end CarrySourceBezout
