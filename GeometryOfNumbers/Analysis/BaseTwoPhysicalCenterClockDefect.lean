import GeometryOfNumbers.Analysis.BaseTwoPhysicalEdgeTfvdBridge
import GeometryOfNumbers.Analysis.CompletedClockCandidateObstructions

/-! # Center correction to the odd-endpoint logarithmic clock
The defect is defined by subtracting the endpoint diagonal clock from the
already certified transported clock. Both legs retain the same decoded center.
No depth frequency, physical source amplitude, or moment is used.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open C2GlobalGreenBridge

def baseTwoPhysicalOddEndpointLog (e : BaseTwoPhysicalEdge) : ℝ :=
  Real.log (((baseTwoPhysicalEdgeOddEndpoint e).val : ℕ) : ℝ)

def baseTwoPhysicalEndpointClock (t : ℝ) (e : BaseTwoPhysicalEdge) : ℂ :=
  (baseTwoPhysicalOddEndpointLog e : ℂ) *
    criticalMaterialGradient t (baseTwoPhysicalEdgeIndex e)

/-- Primary definition: true material clock minus the odd-endpoint clock. -/
def baseTwoPhysicalCenterClockDefect (t : ℝ) (e : BaseTwoPhysicalEdge) : ℂ :=
  baseTwoNativeLogGradientFormula t (baseTwoPhysicalEdgeIndex e) -
    baseTwoPhysicalEndpointClock t e

private theorem nativeLogFormula_samples (t : ℝ) (n : ℕ) :
    baseTwoNativeLogGradientFormula t n =
      (Real.log ((n+2 : ℕ) : ℝ) : ℂ) * criticalMaterialSample t (n+2) -
      (Real.log ((n+1 : ℕ) : ℝ) : ℂ) * criticalMaterialSample t (n+1) := by
  rw [← baseTwoCompletedClockCoordinate_eq_nativeLogFormula,
    baseTwoCompletedBoundaryHilbertClockCoordinate_eq]

theorem baseTwoPhysicalCenterClockDefect_left (t : ℝ) (k : ℕ) :
    baseTwoPhysicalCenterClockDefect t (k,0) =
      ((Real.log (baseTwoCenter k : ℝ) -
        Real.log ((baseTwoCenter k - 1 : ℕ) : ℝ)) : ℂ) *
        criticalMaterialSample t (baseTwoCenter k) := by
  unfold baseTwoPhysicalCenterClockDefect baseTwoPhysicalEndpointClock baseTwoPhysicalOddEndpointLog
  rw [baseTwoPhysicalEdgeIndex_left, nativeLogFormula_samples]
  simp only [criticalMaterialGradient, baseTwoPhysicalEdgeOddEndpoint_left, baseTwo_center_eq]
  have h1 : 4*k+2+2 = 4*(k+1) := by omega
  have h2 : 4*k+2+1 = 4*(k+1)-1 := by omega
  rw [h1, h2]
  have h3 : 4*(k+1)-1 = 4*k+3 := by omega
  rw [h3]
  push_cast
  ring

theorem baseTwoPhysicalCenterClockDefect_right (t : ℝ) (k : ℕ) :
    baseTwoPhysicalCenterClockDefect t (k,1) =
      ((Real.log ((baseTwoCenter k + 1 : ℕ) : ℝ) -
        Real.log (baseTwoCenter k : ℝ)) : ℂ) *
        criticalMaterialSample t (baseTwoCenter k) := by
  unfold baseTwoPhysicalCenterClockDefect baseTwoPhysicalEndpointClock baseTwoPhysicalOddEndpointLog
  rw [baseTwoPhysicalEdgeIndex_right, nativeLogFormula_samples]
  simp only [criticalMaterialGradient, baseTwoPhysicalEdgeOddEndpoint_right, baseTwo_center_eq]
  have h1 : 4*k+3+2 = 4*(k+1)+1 := by omega
  have h2 : 4*k+3+1 = 4*(k+1) := by omega
  rw [h1, h2]
  have h3 : 4*(k+1)+1 = 4*k+5 := by omega
  rw [h3]
  push_cast
  ring

/-- The center appearing in both formulas is the center of the existing C2 chart. -/
theorem baseTwoPhysicalCenterClockDefect_decoded_center (t : ℝ) (e : BaseTwoPhysicalEdge) :
    criticalMaterialSample t
      (2 ^ c2BranchDepth (baseTwoPhysicalEdgeC2Address e).2 *
        (baseTwoPhysicalEdgeC2Address e).1.val) =
      criticalMaterialSample t (baseTwoCenter e.1) := by
  rw [baseTwoPhysicalEdgeC2Address_center]

private theorem log_step_bound (n : ℕ) (hn : 0 < n) :
    0 ≤ Real.log ((n+1 : ℕ) : ℝ) - Real.log (n : ℝ) ∧
    Real.log ((n+1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ (n : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq : (0 : ℝ) < (n+1 : ℕ) := by positivity
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hp (by exact_mod_cast Nat.le_succ n))
  · have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at h
    have he : ((n+1 : ℕ) : ℝ) / n - 1 = (n : ℝ)⁻¹ := by
      push_cast; field_simp; ring
    rwa [he] at h

private theorem sample_norm_le_one (t : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖criticalMaterialSample t n‖ ≤ 1 := by
  have h := criticalMaterialSample_norm_sq t n hn
  have hi : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  nlinarith [norm_nonneg (criticalMaterialSample t n)]

/-- A weaker 1/(k+1) bound already suffices for square summability. -/
theorem baseTwoPhysicalCenterClockDefect_norm_le (t : ℝ) (e : BaseTwoPhysicalEdge) :
    ‖baseTwoPhysicalCenterClockDefect t e‖ ≤ ((e.1+1 : ℕ) : ℝ)⁻¹ := by
  rcases e with ⟨k,a⟩
  fin_cases a
  · change ‖baseTwoPhysicalCenterClockDefect t (k,0)‖ ≤ ((k+1 : ℕ) : ℝ)⁻¹
    rw [baseTwoPhysicalCenterClockDefect_left, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hc : baseTwoCenter k = 4*k+4 := by simp [baseTwo_center_eq]; omega
    have hm : baseTwoCenter k-1 = 4*k+3 := by omega
    have hs := log_step_bound (4*k+3) (by omega)
    have hp := sample_norm_le_one t (baseTwoCenter k) (by omega)
    have he : baseTwoCenter k = (4*k+3)+1 := by omega
    rw [hm, he, abs_of_nonneg hs.1]
    exact (mul_le_of_le_one_right hs.1 hp).trans
      (hs.2.trans ((inv_le_inv₀ (by positivity) (by positivity)).mpr (by norm_cast; omega)))
  · change ‖baseTwoPhysicalCenterClockDefect t (k,1)‖ ≤ ((k+1 : ℕ) : ℝ)⁻¹
    rw [baseTwoPhysicalCenterClockDefect_right, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hc : baseTwoCenter k = 4*k+4 := by simp [baseTwo_center_eq]; omega
    have hs := log_step_bound (baseTwoCenter k) (by omega)
    have hp := sample_norm_le_one t (baseTwoCenter k) (by omega)
    rw [abs_of_nonneg hs.1]
    simp only [hc] at hs hp ⊢
    exact (mul_le_of_le_one_right hs.1 hp).trans
      (hs.2.trans ((inv_le_inv₀ (by positivity) (by positivity)).mpr (by norm_cast; omega)))

theorem baseTwoPhysicalCenterClockDefect_memℓp (t : ℝ) :
    Memℓp (baseTwoPhysicalCenterClockDefect t) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hp : Summable (fun k : ℕ => (((k+1 : ℕ) : ℝ)⁻¹)^2) := by
    simpa only [inv_pow] using (summable_nat_add_iff 1).mpr
      (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ)))
  have hmajor : Summable (fun e : BaseTwoPhysicalEdge => (((e.1+1 : ℕ) : ℝ)⁻¹)^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simpa using hp.mul_left 2
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun e => (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (baseTwoPhysicalCenterClockDefect_norm_le t e)) hmajor

def baseTwoPhysicalCenterClockDefectL2 (t : ℝ) : ℓ²(BaseTwoPhysicalEdge,ℂ) :=
  ⟨baseTwoPhysicalCenterClockDefect t, baseTwoPhysicalCenterClockDefect_memℓp t⟩

@[simp] theorem baseTwoPhysicalCenterClockDefectL2_apply (t : ℝ) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalCenterClockDefectL2 t e = baseTwoPhysicalCenterClockDefect t e := rfl

/-- Same address equivalence and exact real quadratures, with no amplitude change. -/
def baseTwoPhysicalCenterClockDefectC2State (t : ℝ) : GlobalC2BranchCarrier :=
  ⟨fun a => baseTwoMaterialEdgeRealification
      (baseTwoPhysicalCenterClockDefectL2 t (baseTwoPhysicalEdgeEquivC2Address.symm a)), by
    apply memℓp_gen
    have h := ((lp.memℓp (baseTwoPhysicalCenterClockDefectL2 t)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal))
    have he := baseTwoPhysicalEdgeEquivC2Address.symm.summable_iff.mpr h
    simpa only [LinearIsometry.norm_map, Function.comp_def] using he⟩

theorem baseTwoPhysicalCenterClockDefectC2State_apply (t : ℝ) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalCenterClockDefectC2State t (baseTwoPhysicalEdgeC2Address e) =
      baseTwoMaterialEdgeRealification (baseTwoPhysicalCenterClockDefect t e) := by
  change baseTwoMaterialEdgeRealification
    (baseTwoPhysicalCenterClockDefectL2 t
      (baseTwoPhysicalEdgeEquivC2Address.symm (baseTwoPhysicalEdgeEquivC2Address e))) = _
  rw [Equiv.symm_apply_apply]; rfl

end GeometryOfNumbers.Analysis.BaseTwoCompletion
