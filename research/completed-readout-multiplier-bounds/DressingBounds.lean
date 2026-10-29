import CameraBounds
import Mathlib.Analysis.Calculus.LogDeriv

/-! Bounds are for each original completion factor separately. The resulting
logarithmic derivative keeps the polynomial, exponential, Gamma and camera. -/
namespace CarryReadoutBounds
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryFourthTail CarryMaterialParts
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def polynomialFactor (w : ℂ) : ℂ := (1/2:ℂ)*baseTwoDressingParameter w*(baseTwoDressingParameter w-1)
def exponentialFactor (w : ℂ) : ℂ := Complex.exp (-(baseTwoDressingParameter w/2)*(Real.log Real.pi:ℂ))
def complexDressing (w : ℂ) : ℂ := canonicalArchimedeanCompletionComplex w*
  (baseTwoCanonicalCameraFactorComplex w)⁻¹

theorem parameter_analytic (w : ℂ) : AnalyticAt ℂ baseTwoDressingParameter w := by
  apply Differentiable.analyticAt
  unfold baseTwoDressingParameter
  fun_prop

theorem polynomial_analytic (w : ℂ) : AnalyticAt ℂ polynomialFactor w :=
  (analyticAt_const.mul (parameter_analytic w)).mul ((parameter_analytic w).sub analyticAt_const)
theorem exponential_analytic (w : ℂ) : AnalyticAt ℂ exponentialFactor w :=
  ((((parameter_analytic w).div_const (c:=2)).neg).mul analyticAt_const).cexp

theorem gamma_factor_analytic (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) : AnalyticAt ℂ gammaFactor w := by
  have hd : DifferentiableOn ℂ gammaFactor (Metric.ball 0 (1/2:ℝ)) := by
    intro v hv
    have hre : 0 < (baseTwoDressingParameter v/2).re := by
      have hi := Complex.im_le_norm v
      have hv' : ‖v‖ < (1/2:ℝ) := by simpa using hv
      norm_num [baseTwoDressingParameter, Complex.div_re, Complex.mul_re]
      linarith
    exact (((Complex.differentiableAt_Gamma _ (fun m hm => by
      have h := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at h
      linarith [Nat.cast_nonneg (α:=ℝ) m])).comp v
        ((parameter_analytic v).differentiableAt.div_const 2))).differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))

theorem polynomial_factor_bounds (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖polynomialFactor w‖ ≤ 1 ∧ polynomialFactor w ≠ 0 ∧ ‖(polynomialFactor w)⁻¹‖ ≤ 32 := by
  obtain ⟨hl,hu,_⟩ := gamma_argument_bounds w hw
  have hs : (1/4:ℝ) ≤ (baseTwoDressingParameter w).re ∧
      (baseTwoDressingParameter w).re ≤ 3/4 := by
    norm_num [Complex.div_re] at hl hu
    constructor <;> linarith
  have hsn : ‖baseTwoDressingParameter w‖ ≤ 3/4 := by
    have h := norm_add_le (1/2:ℂ) (Complex.I*w)
    norm_num [norm_mul] at h
    unfold baseTwoDressingParameter
    linarith
  have htn : ‖baseTwoDressingParameter w-1‖ ≤ 3/4 := by
    have he : baseTwoDressingParameter w-1 = (-1/2:ℂ)+Complex.I*w := by
      unfold baseTwoDressingParameter; ring
    rw [he]
    have h := norm_add_le (-1/2:ℂ) (Complex.I*w)
    norm_num [norm_mul] at h
    linarith
  have hsl : (1/4:ℝ) ≤ ‖baseTwoDressingParameter w‖ := by
    linarith [Complex.re_le_norm (baseTwoDressingParameter w)]
  have htl : (1/4:ℝ) ≤ ‖baseTwoDressingParameter w-1‖ := by
    have h : -(baseTwoDressingParameter w-1).re ≤ ‖baseTwoDressingParameter w-1‖ := by
      linarith [neg_abs_le (baseTwoDressingParameter w-1).re, Complex.abs_re_le_norm (baseTwoDressingParameter w-1)]
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have he : ‖polynomialFactor w‖ = (1/2:ℝ)*‖baseTwoDressingParameter w‖*‖baseTwoDressingParameter w-1‖ := by
    simp [polynomialFactor]
  have hu' : ‖polynomialFactor w‖ ≤ 1 := by
    rw [he]
    nlinarith [mul_le_mul hsn htn (norm_nonneg _) (by norm_num : (0:ℝ)≤3/4)]
  have hl' : (1/32:ℝ) ≤ ‖polynomialFactor w‖ := by
    rw [he]
    nlinarith [mul_le_mul hsl htl (by norm_num : (0:ℝ)≤1/4) (norm_nonneg _)]
  refine ⟨hu', norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hl'), ?_⟩
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hl')).2 (by linarith)

theorem log_pi_bounds : 0 ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ 2 := by
  refine ⟨Real.log_nonneg (by linarith [Real.two_le_pi]), ?_⟩
  have h := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
  have he : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  linarith [log_two_bounds.2]

theorem exponential_factor_bounds (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖exponentialFactor w‖ ≤ 3 ∧ ‖(exponentialFactor w)⁻¹‖ ≤ 3 := by
  have hg := (gamma_argument_bounds w hw).2.2
  have hn : ‖-(baseTwoDressingParameter w/2)*(Real.log Real.pi:ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg log_pi_bounds.1]
    nlinarith [mul_le_mul hg log_pi_bounds.2 log_pi_bounds.1 (by norm_num : (0:ℝ)≤3/8)]
  have h (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖Complex.exp z‖ ≤ 3 :=
    (Complex.norm_exp_le_exp_norm z).trans ((Real.exp_le_exp.mpr hz).trans Real.exp_one_lt_three.le)
  constructor
  · exact h _ hn
  · rw [exponentialFactor, ← Complex.exp_neg]
    exact h _ (by simpa only [norm_neg] using hn)

theorem derivative_eighth_bound {f : ℂ → ℂ} {C : ℝ}
    (ha : ∀ w, ‖w‖ ≤ (1/4:ℝ) → AnalyticAt ℂ f w)
    (hb : ∀ w, ‖w‖ ≤ (1/4:ℝ) → ‖f w‖ ≤ C)
    (w : ℂ) (hw : ‖w‖ ≤ (1/8:ℝ)) : ‖deriv f w‖ ≤ 8*C := by
  have hmem (v : ℂ) (hv : v ∈ Metric.closedBall w (1/8:ℝ)) : ‖v‖ ≤ (1/4:ℝ) := by
    have ht := norm_add_le (v-w) w
    simp only [sub_add_cancel] at ht
    have hv' : ‖v-w‖ ≤ (1/8:ℝ) := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hv
    linarith
  have hd : DiffContOnCl ℂ f (Metric.ball w (1/8:ℝ)) :=
    (show DifferentiableOn ℂ f (Metric.closedBall w (1/8:ℝ)) from
      fun v hv => (ha v (hmem v hv)).differentiableAt.differentiableWithinAt).diffContOnCl_ball
      (by intro v hv; exact hv)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c:=w) (f:=f) 1 (by norm_num : (0:ℝ)<1/8) hd (fun v hv => hb v (hmem v (Metric.sphere_subset_closedBall hv)))
  simpa only [Nat.factorial_one, Nat.cast_one, iteratedDeriv_one, one_mul, mul_one, pow_one, div_inv_eq_mul, one_div, mul_comm] using h

theorem complex_dressing_formula : complexDressing = fun w =>
    polynomialFactor w*exponentialFactor w*gammaFactor w/baseTwoCanonicalCameraFactorComplex w := by
  funext w
  rfl

theorem complex_dressing_analytic (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) : AnalyticAt ℂ complexDressing w := by
  rw [complex_dressing_formula]
  exact (((polynomial_analytic w).mul (exponential_analytic w)).mul
    (gamma_factor_analytic w (by linarith))).div
    (baseTwoCanonicalCameraFactorComplex_differentiable.analyticAt w) (camera_complex_nonzero w hw)

theorem complex_dressing_nonzero (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) : complexDressing w ≠ 0 := by
  rw [complex_dressing_formula]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (polynomial_factor_bounds w hw).2.1
    (Complex.exp_ne_zero _)) (Complex.Gamma_ne_zero_of_re_pos (by
      have h := (gamma_argument_bounds w hw).1; linarith))) (camera_complex_nonzero w hw)

theorem dressing_log_split (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    logDeriv complexDressing w = logDeriv polynomialFactor w+logDeriv exponentialFactor w+
      logDeriv gammaFactor w-logDeriv baseTwoCanonicalCameraFactorComplex w := by
  have hp := (polynomial_factor_bounds w hw).2.1
  have he : exponentialFactor w ≠ 0 := Complex.exp_ne_zero _
  have hg : gammaFactor w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    have h := (gamma_argument_bounds w hw).1; linarith)
  have hdP := (polynomial_analytic w).differentiableAt
  have hdE := (exponential_analytic w).differentiableAt
  have hdG := (gamma_factor_analytic w (by linarith)).differentiableAt
  have hdC := baseTwoCanonicalCameraFactorComplex_differentiable w
  rw [complex_dressing_formula, logDeriv_div (f:=fun v => polynomialFactor v*exponentialFactor v*gammaFactor v)
    (g:=baseTwoCanonicalCameraFactorComplex) w (mul_ne_zero (mul_ne_zero hp he) hg)
    (camera_complex_nonzero w hw) ((hdP.mul hdE).mul hdG) hdC,
    logDeriv_mul (f:=fun v => polynomialFactor v*exponentialFactor v) (g:=gammaFactor) w (mul_ne_zero hp he) hg (hdP.mul hdE) hdG,
    logDeriv_mul (f:=polynomialFactor) (g:=exponentialFactor) w hp he hdP hdE]

theorem dressing_log_bound (w : ℂ) (hw : ‖w‖ ≤ (1/8:ℝ)) :
    ‖logDeriv complexDressing w‖ ≤ 8192 := by
  have hw' : ‖w‖ ≤ (1/4:ℝ) := by linarith
  have hP := derivative_eighth_bound (fun v _ => polynomial_analytic v)
    (fun v hv => (polynomial_factor_bounds v hv).1) w hw
  have hE := derivative_eighth_bound (fun v _ => exponential_analytic v)
    (fun v hv => (exponential_factor_bounds v hv).1) w hw
  have hG := derivative_eighth_bound (fun v hv => gamma_factor_analytic v (by linarith)) gamma_factor_bound w hw
  have hC := derivative_eighth_bound (fun v _ => baseTwoCanonicalCameraFactorComplex_differentiable.analyticAt v)
    camera_complex_bound w hw
  norm_num at hP hE hG hC
  have hb (f : ℂ → ℂ) (d a : ℝ) (hd : ‖deriv f w‖ ≤ d) (hi : ‖(f w)⁻¹‖ ≤ a) (ha : 0 ≤ d) :
      ‖logDeriv f w‖ ≤ d*a := by
    rw [logDeriv_apply, div_eq_mul_inv, norm_mul]
    exact mul_le_mul hd hi (norm_nonneg _) ha
  have hp := hb _ 8 32 (by simpa using hP) (polynomial_factor_bounds w hw').2.2 (by norm_num)
  have he := hb _ 24 3 (by simpa using hE) (exponential_factor_bounds w hw').2 (by norm_num)
  have hg := hb _ 64 8 (by simpa using hG) (inverse_gamma_factor_bound w hw') (by norm_num)
  have hc := hb _ 48 72 (by simpa using hC) (camera_complex_inverse_bound w hw') (by norm_num)
  rw [dressing_log_split w hw']
  have h := (norm_sub_le (logDeriv polynomialFactor w+logDeriv exponentialFactor w+logDeriv gammaFactor w)
    (logDeriv baseTwoCanonicalCameraFactorComplex w)).trans
    (add_le_add (norm_add_le _ _) (le_refl _))
  have h' := norm_add_le (logDeriv polynomialFactor w) (logDeriv exponentialFactor w)
  linarith

end
end CarryReadoutBounds
