import NativePortCalibration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Literal omitted C3 cells, before Mellin or any boundary pairing.
The three arithmetic addresses and their coefficients are unchanged.
This is a transport of the stored analytic tail, not a new physical norm. -/
namespace CarryCameraTail
open CarryMaterialTheta CarrySelfAdjointOperator CPFormal.Analytic.Cp
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def heat (n : ℕ) (x : ℝ) : ℝ := Real.exp (-Real.pi*(n : ℝ)^2*x)

def cameraHeatBlock (m : ℕ) (x : ℝ) : ℂ :=
  heatSample (3*m+2) x - 2*heatSample (3*m+3) x + heatSample (3*m+4) x

def cameraHeatTail (M : ℕ) (x : ℝ) : ℂ :=
  ∑' k : ℕ, cameraHeatBlock (k+M) x

def cameraHeatPrefix (M L : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range L, cameraHeatBlock (k+M) x

theorem heat_antitone {x : ℝ} (hx : 0 ≤ x) : Antitone (fun n : ℕ => heat n x) := by
  intro a b hab
  unfold heat
  apply Real.exp_le_exp.mpr
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hsq : (a : ℝ)^2 ≤ (b : ℝ)^2 := by gcongr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonpos_left hsq (by linarith [Real.pi_pos])) hx

theorem summable_heat {x : ℝ} (hx : 0 < x) : Summable (fun n : ℕ => heat n x) := by
  have h := Real.summable_exp_nat_mul_of_ge (c := -Real.pi*x)
    (by nlinarith [Real.pi_pos]) (f := fun n : ℕ => (n : ℝ)^2) (by
      intro n
      exact_mod_cast (Nat.le_self_pow (by norm_num : 2 ≠ 0) n))
  simpa only [heat, mul_assoc, mul_left_comm, mul_comm] using h

theorem summable_camera_blocks (M : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => cameraHeatBlock (k+M) x) := by
  have h := Complex.summable_ofReal.mpr (summable_heat hx)
  have hsub (r : ℕ) := h.comp_injective
    (show Function.Injective (fun k : ℕ => 3*(k+M)+r) by
      intro a b hab
      dsimp only at hab
      omega)
  simpa only [Function.comp_def, cameraHeatBlock, heatSample, heat] using
    ((hsub 2).sub ((hsub 3).mul_left 2)).add (hsub 4)

/-- The bound is obtained after assembling the whole 1,-2,1 cell.
It telescopes across omitted cells; no individual Dirichlet tail is summed. -/
theorem camera_block_norm_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖cameraHeatBlock m x‖ ≤ heat (3*m+2) x - heat (3*(m+1)+2) x := by
  have h := heat_antitone hx
  have hab := h (show 3*m+2 ≤ 3*m+3 by omega)
  have hbc := h (show 3*m+3 ≤ 3*m+4 by omega)
  have hcd := h (show 3*m+4 ≤ 3*(m+1)+2 by omega)
  have heq : cameraHeatBlock m x =
      ((heat (3*m+2) x - 2*heat (3*m+3) x + heat (3*m+4) x : ℝ) : ℂ) := by
    simp only [cameraHeatBlock, heatSample, heat, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem camera_prefix_norm_le (M L : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖cameraHeatPrefix M L x‖ ≤ heat (3*M+2) x := by
  have hsum : ∀ L : ℕ, ∑ k ∈ Finset.range L, ‖cameraHeatBlock (k+M) x‖ ≤
      heat (3*M+2) x - heat (3*(L+M)+2) x := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ]
      have h := camera_block_norm_le (L+M) hx
      have he : L+M+1 = (L+1)+M := by omega
      rw [he] at h
      linarith
  exact (norm_sum_le _ _).trans ((hsum L).trans (sub_le_self _ (by
    exact (Real.exp_pos _).le)))

theorem camera_prefix_tendsto (M : ℕ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun L : ℕ => cameraHeatPrefix M L x) atTop (𝓝 (cameraHeatTail M x)) :=
  (summable_camera_blocks M hx).hasSum.tendsto_sum_nat

theorem camera_tail_norm_le (M : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖cameraHeatTail M x‖ ≤ heat (3*M+2) x :=
  le_of_tendsto ((camera_prefix_tendsto M hx).norm)
    (Eventually.of_forall fun L => camera_prefix_norm_le M L hx.le)

theorem camera_prefix_continuous (M L : ℕ) : Continuous (cameraHeatPrefix M L) := by
  unfold cameraHeatPrefix cameraHeatBlock heatSample
  fun_prop

theorem camera_tail_measurable (M : ℕ) :
    AEStronglyMeasurable (cameraHeatTail M) (volume.restrict (Ioi 0)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun L => (camera_prefix_continuous M L).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact camera_prefix_tendsto M hx

end
end CarryCameraTail
