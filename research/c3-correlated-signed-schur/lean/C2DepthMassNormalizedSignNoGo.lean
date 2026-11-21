import C2ConnectedLogTfvdDyadicSign

/-!
Depth-mass normalization suggested by the ORIGINAL quadratic geometry:
weight=2^(-k), amplitude=2^(-k/2). Multiplying a signed C2
connected-defect kernel by 2^k is compatible with dividing by
amplitude squared, but is NOT a proof that this kernel *is* the
completed-native moment energy.

The normalized connected defect tends to 3/8, and the NORMALIZED
2x2 kernel remains INDEFINITE with invariant determinant -1/64.
This is the crucial scale-vs-sign separation.
-/

namespace CarryWheelNativeSignedGate

def depthNormalizedDefect (k p q : ℕ) : ℚ :=
  (2:ℚ)^k * dyadicConnectedPositiveDefect k p q

theorem normalized_35_exact (k : ℕ) :
    depthNormalizedDefect k 3 5 =
      (3/8:ℚ) + (1/32:ℚ)*(1/2:ℚ)^k := by
  unfold depthNormalizedDefect
  rw [dyadic_defect_3_5, mul_add]
  have hhalf : (2:ℚ)^k*(1/2:ℚ)^k = 1 := by
    rw [← mul_pow]
    norm_num
  have hquarter : (2:ℚ)^k*(1/4:ℚ)^k = (1/2:ℚ)^k := by
    rw [← mul_pow]
    norm_num
  rw [show (2:ℚ)^k * ((3/8:ℚ)*(1/2:ℚ)^k) =
       (3/8:ℚ)*((2:ℚ)^k*(1/2:ℚ)^k) by ring,
      show (2:ℚ)^k * ((1/32:ℚ)*(1/4:ℚ)^k) =
       (1/32:ℚ)*((2:ℚ)^k*(1/4:ℚ)^k) by ring]
  rw [hhalf, hquarter]
  ring

theorem normalized_35_strict_positive (k : ℕ) :
    0 < depthNormalizedDefect k 3 5 := by
  rw [normalized_35_exact]
  positivity

/-- Scale-normalizing the entire 2x2 matrix by the squared
half-density leaves its sign NEGATIVE, at EVERY dyadic cutoff. -/
theorem depth_normalized_defect_matrix_det_const_negative (k : ℕ) :
    depthNormalizedDefect k 3 3 * depthNormalizedDefect k 5 5 -
      (depthNormalizedDefect k 3 5)^2 = -(1/64:ℚ) := by
  unfold depthNormalizedDefect
  have h := dyadic_naive_defect_matrix_det_negative_exact k
  have hp : ((2:ℚ)^k)^2 = (4:ℚ)^k := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hscale : (4:ℚ)^k * (1/4:ℚ)^k = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (2:ℚ)^k * dyadicConnectedPositiveDefect k 3 3 *
        ((2:ℚ)^k * dyadicConnectedPositiveDefect k 5 5) -
        ((2:ℚ)^k * dyadicConnectedPositiveDefect k 3 5)^2 =
      ((2:ℚ)^k)^2 *
       (dyadicConnectedPositiveDefect k 3 3 *
         dyadicConnectedPositiveDefect k 5 5 -
        (dyadicConnectedPositiveDefect k 3 5)^2) := by ring
    _ = ((2:ℚ)^k)^2 * (-(1/64:ℚ)*(1/4:ℚ)^k) := by rw [h]
    _ = -(1/64:ℚ) := by rw [hp]; nlinarith [hscale]

end CarryWheelNativeSignedGate
