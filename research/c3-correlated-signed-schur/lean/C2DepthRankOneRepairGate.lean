import C2DepthMassNormalizedSignNoGo

/-!
Exact Schur compensation threshold for the tentative 2x2 C2 connected
defect candidate. This is NOT the completed native Schur matrix; the
rank-one correction is a hypothetical test to quantify how much
positive source energy is missing in this naive candidate.
-/

namespace CarryWheelNativeSignedGate

theorem depth_normalized_defect_33_exact (k : ℕ) :
    depthNormalizedDefect k 3 3 =
      (1/4:ℚ)+(1/64:ℚ)*(1/2:ℚ)^k := by
  unfold depthNormalizedDefect
  rw [dyadic_defect_3_3,mul_add]
  have hhalf : (2:ℚ)^k*(1/2:ℚ)^k=1 := by
    rw [←mul_pow];norm_num
  have hquarter : (2:ℚ)^k*(1/4:ℚ)^k=(1/2:ℚ)^k := by
    rw [←mul_pow];norm_num
  calc
    (2:ℚ)^k * ((1/4:ℚ)*(1/2:ℚ)^k) +
      (2:ℚ)^k * ((1/64:ℚ)*(1/4:ℚ)^k) =
      (1/4:ℚ)*((2:ℚ)^k*(1/2:ℚ)^k) +
      (1/64:ℚ)*((2:ℚ)^k*(1/4:ℚ)^k) := by ring
    _ = _ := by rw [hhalf,hquarter];ring

theorem depth_rank_one_repaired_det_exact (k : ℕ) (delta : ℚ) :
    depthNormalizedDefect k 3 3 *
      (depthNormalizedDefect k 5 5 + delta) -
      (depthNormalizedDefect k 3 5)^2 =
      (((16:ℚ)+(1/2:ℚ)^k)*delta - 1)/64 := by
  have hdet := depth_normalized_defect_matrix_det_const_negative k
  rw [depth_normalized_defect_33_exact] at *
  linarith [hdet]

/-- To make the naive normalized 2x2 connected kernel PSD by adding
a positive correction only to its last diagonal, its size must
exceed this EXPLICIT Schur threshold. -/
theorem depth_rank_one_repair_threshold (k : ℕ) (delta : ℚ) :
    0 ≤ depthNormalizedDefect k 3 3 *
      (depthNormalizedDefect k 5 5 + delta) -
      (depthNormalizedDefect k 3 5)^2 ↔
        1/((16:ℚ)+(1/2:ℚ)^k) ≤ delta := by
  rw [depth_rank_one_repaired_det_exact]
  have hp : (0:ℚ) < 16+(1/2:ℚ)^k := by positivity
  constructor
  · intro h
    apply (div_le_iff₀ hp).2
    linarith
  · intro h
    have hh := (div_le_iff₀ hp).1 h
    linarith

end CarryWheelNativeSignedGate
