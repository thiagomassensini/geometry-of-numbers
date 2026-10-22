import AcceleratedGreen
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Quantitative bounds for the original Gamma factor, independent of native
moment signs. These are coarse analytic estimates, not fitted moments. -/
namespace CarryReadoutBounds
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryFourthTail CarryMaterialParts
open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem real_gamma_le_inverse {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.Gamma x ≤ 1/x := by
  have h := Real.convexOn_Gamma.2 (by norm_num : (1:ℝ) ∈ Ioi 0)
    (by norm_num : (2:ℝ) ∈ Ioi 0) (sub_nonneg.mpr hx1) hx.le
    (by ring : (1-x)+x=1)
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two, mul_one] at h
  have he : 1-x+x*2=x+1 := by ring
  rw [he, Real.Gamma_add_one hx.ne'] at h
  apply (le_div_iff₀ hx).2
  nlinarith

theorem complex_gamma_norm_le_real {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.one_re]

theorem complex_gamma_norm_le {z : ℂ} (hz : 0 < z.re) (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma z‖ ≤ 1/z.re :=
  (complex_gamma_norm_le_real hz).trans (real_gamma_le_inverse hz hz1)

theorem complex_sin_norm_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.sin]
  have hp : ‖Complex.exp (-z*Complex.I)‖ ≤ Real.exp ‖z‖ := by
    simpa only [norm_mul, norm_neg, Complex.norm_I, mul_one] using Complex.norm_exp_le_exp_norm (-z*Complex.I)
  have hm : ‖Complex.exp (z*Complex.I)‖ ≤ Real.exp ‖z‖ := by
    simpa only [norm_mul, Complex.norm_I, mul_one] using Complex.norm_exp_le_exp_norm (z*Complex.I)
  rw [norm_div]
  norm_num [norm_mul]
  have h := norm_sub_le (Complex.exp (-(z*Complex.I))) (Complex.exp (z*Complex.I))
  rw [neg_mul] at hp
  linarith

theorem exp_two_le_nine : Real.exp 2 ≤ 9 := by
  have h := Real.exp_one_lt_three
  have he := Real.exp_pos 1
  rw [show (2:ℝ)=1+1 by norm_num, Real.exp_add]
  nlinarith

def gammaFactor (w : ℂ) : ℂ := Complex.Gamma (baseTwoDressingParameter w/2)

theorem gamma_argument_bounds (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    (1/8:ℝ) ≤ (baseTwoDressingParameter w/2).re ∧
    (baseTwoDressingParameter w/2).re ≤ 3/8 ∧
    ‖baseTwoDressingParameter w/2‖ ≤ 3/8 := by
  have hi := Complex.abs_im_le_norm w
  have hn := norm_add_le (1/2:ℂ) (Complex.I*w)
  norm_num [norm_mul] at hn
  constructor
  · norm_num [baseTwoDressingParameter, Complex.div_re, Complex.mul_re]
    have hh := le_abs_self w.im
    linarith
  constructor
  · norm_num [baseTwoDressingParameter, Complex.div_re, Complex.mul_re]
    have hh := neg_abs_le w.im
    linarith
  · unfold baseTwoDressingParameter
    rw [norm_div]
    norm_num
    linarith

theorem gamma_factor_bound (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) : ‖gammaFactor w‖ ≤ 8 := by
  obtain ⟨hl,hu,_⟩ := gamma_argument_bounds w hw
  exact (complex_gamma_norm_le (by linarith) (by linarith)).trans
    ((div_le_iff₀ (by linarith)).2 (by linarith))

theorem inverse_gamma_factor_bound (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖(gammaFactor w)⁻¹‖ ≤ 8 := by
  let z := baseTwoDressingParameter w/2
  obtain ⟨hl,hu,hn⟩ := gamma_argument_bounds w hw
  have hz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by dsimp [z]; linarith)
  have hs : Complex.sin (Real.pi*z) ≠ 0 := by
    intro he
    have h := Complex.Gamma_mul_Gamma_one_sub z
    rw [he, div_zero] at h
    exact (mul_ne_zero hz (Complex.Gamma_ne_zero_of_re_pos (by
      change 0 < 1-(baseTwoDressingParameter w/2).re; linarith))) h
  have he : (Complex.Gamma z)⁻¹ = Complex.Gamma (1-z)*Complex.sin (Real.pi*z)/Real.pi := by
    have h := Complex.Gamma_mul_Gamma_one_sub z
    have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hh := (eq_div_iff hs).mp h
    field_simp [hz, hp]
    simpa only [mul_comm z (Real.pi:ℂ)] using hh.symm
  have hgn : ‖Complex.Gamma (1-z)‖ ≤ 8/5 := by
    have hre : (1-z).re = 1-z.re := by simp
    apply (complex_gamma_norm_le (by rw [hre]; dsimp [z]; linarith)
      (by rw [hre]; dsimp [z]; linarith)).trans
    apply (div_le_iff₀ (by rw [hre]; dsimp [z]; linarith)).2
    rw [hre]; dsimp [z]; linarith
  have hsn : ‖Complex.sin (Real.pi*z)‖ ≤ 9 := by
    apply (complex_sin_norm_le_exp _).trans
    apply (Real.exp_le_exp.mpr ?_).trans exp_two_le_nine
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hn' : ‖z‖ ≤ 3/8 := hn
    nlinarith [Real.pi_lt_four, norm_nonneg z]
  change ‖(Complex.Gamma z)⁻¹‖ ≤ 8
  rw [he, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  apply (div_le_iff₀ Real.pi_pos).2
  have hprod := mul_le_mul hgn hsn (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 8/5)
  nlinarith [Real.two_le_pi]

end
end CarryReadoutBounds
