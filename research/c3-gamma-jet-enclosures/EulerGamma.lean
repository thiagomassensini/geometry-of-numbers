import GammaBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Quantitative evaluation of the ORIGINAL Euler Gamma factor.
No native moments, theta representation, zeros, or Gram signs enter here. -/
namespace CarryC3Gamma
open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def expHead (N : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, (-(x:ℂ))^k/(k.factorial:ℂ)

def gammaHeadIntegral (N : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in 0..T, expHead N x*(x:ℂ)^(z-1)

theorem exp_head_error (N : ℕ) (T x : ℝ) (hx : 0 ≤ x) (hxT : x ≤ T)
    (hN : T/(N+1:ℕ) ≤ 1/2) :
    ‖(Real.exp (-x):ℂ)-expHead N x‖ ≤ 2*T^N/(N.factorial:ℝ) := by
  have hn : ‖(-(x:ℂ))‖ = x := by simp [abs_of_nonneg hx]
  have h := Complex.exp_bound' (x:=-(x:ℂ)) (n:=N) (by
    rw [hn]; exact (div_le_div_of_nonneg_right hxT (by positivity)).trans hN)
  rw [hn] at h
  have he : (Real.exp (-x):ℂ) = Complex.exp (-(x:ℂ)) := by simp
  rw [he,expHead]
  apply h.trans
  calc
    x^N/(N.factorial:ℝ)*2 ≤ T^N/(N.factorial:ℝ)*2 := by gcongr
    _ = 2*T^N/(N.factorial:ℝ) := by ring

theorem gamma_tail_bound (T : ℝ) (hT : 1 ≤ T) (z : ℂ)
    (hz1 : z.re ≤ 1) :
    ‖∫ x : ℝ in Ioi T, (Real.exp (-x):ℂ)*(x:ℂ)^(z-1)‖ ≤ Real.exp (-T) := by
  rw [← integral_exp_neg_Ioi T]
  apply MeasureTheory.norm_integral_le_of_norm_le (integrableOn_exp_neg_Ioi T)
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with x hx
  have hx1 : 1 ≤ x := hT.trans hx.le
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x)]
  have hp : x^((z-1).re) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hx1
    simp only [Complex.sub_re,Complex.one_re]
    linarith
  simpa using mul_le_mul_of_nonneg_left hp (Real.exp_pos (-x)).le

theorem gamma_compact_error (N : ℕ) (T : ℝ) (hT : 1 ≤ T)
    (hN : T/(N+1:ℕ) ≤ 1/2) (z : ℂ) (hz : 0 < z.re) (hz1 : z.re ≤ 1) :
    ‖(∫ x : ℝ in 0..T, (Real.exp (-x):ℂ)*(x:ℂ)^(z-1))-
      gammaHeadIntegral N T z‖ ≤ 2*T^(N+1)/((N.factorial:ℝ)*z.re) := by
  have hT0 : 0 ≤ T := by linarith
  have hi : IntervalIntegrable (fun x : ℝ => (Real.exp (-x):ℂ)*(x:ℂ)^(z-1)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0]
    exact (Complex.GammaIntegral_convergent hz).mono_set Ioc_subset_Ioi_self
  have hp : IntervalIntegrable (fun x : ℝ => expHead N x*(x:ℂ)^(z-1)) volume 0 T := by
    apply IntervalIntegrable.continuousOn_mul
      (intervalIntegral.intervalIntegrable_cpow' (by simp only [Complex.sub_re,Complex.one_re]; linarith))
    unfold expHead
    fun_prop
  rw [gammaHeadIntegral,← intervalIntegral.integral_sub hi hp]
  let C : ℝ := 2*T^N/(N.factorial:ℝ)
  have hb : ‖∫ x : ℝ in 0..T,
      (Real.exp (-x):ℂ)*(x:ℂ)^(z-1)-expHead N x*(x:ℂ)^(z-1)‖ ≤
      ∫ x : ℝ in 0..T, C*x^(z.re-1) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT0
    · filter_upwards with x hx
      rw [← sub_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      simpa only [Complex.sub_re,Complex.one_re] using
        mul_le_mul_of_nonneg_right (exp_head_error N T x hx.1.le hx.2 hN)
          (Real.rpow_nonneg hx.1.le _)
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C
  apply hb.trans
  rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith))]
  have hz0 : z.re ≠ 0 := hz.ne'
  rw [sub_add_cancel,Real.zero_rpow hz0,sub_zero]
  have he : T^z.re ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT hz1
  have hc : 0 ≤ C := by dsimp [C]; positivity
  calc
    C*(T^z.re/z.re) ≤ C*(T/z.re) := by gcongr
    _ = 2*T^(N+1)/((N.factorial:ℝ)*z.re) := by dsimp [C]; rw [pow_succ]; ring

theorem gamma_integral_approx_error (N : ℕ) (T : ℝ) (hT : 1 ≤ T)
    (hN : T/(N+1:ℕ) ≤ 1/2) (z : ℂ) (hz : 0 < z.re) (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma z-gammaHeadIntegral N T z‖ ≤
      2*T^(N+1)/((N.factorial:ℝ)*z.re)+Real.exp (-T) := by
  have hT0 : 0 ≤ T := by linarith
  have hf := Complex.GammaIntegral_convergent hz
  have he : Complex.Gamma z =
      (∫ x : ℝ in 0..T, (Real.exp (-x):ℂ)*(x:ℂ)^(z-1))+
      ∫ x : ℝ in Ioi T, (Real.exp (-x):ℂ)*(x:ℂ)^(z-1) := by
    rw [Complex.Gamma_eq_integral hz,Complex.GammaIntegral,
      intervalIntegral.integral_of_le hT0]
    rw [← setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hT0))]
    rw [Ioc_union_Ioi_eq_Ioi hT0]
  rw [he]
  have hid : (∫ x : ℝ in 0..T, (Real.exp (-x):ℂ)*(x:ℂ)^(z-1))+
      (∫ x : ℝ in Ioi T, (Real.exp (-x):ℂ)*(x:ℂ)^(z-1))-gammaHeadIntegral N T z =
      ((∫ x : ℝ in 0..T, (Real.exp (-x):ℂ)*(x:ℂ)^(z-1))-gammaHeadIntegral N T z)+
      ∫ x : ℝ in Ioi T, (Real.exp (-x):ℂ)*(x:ℂ)^(z-1) := by ring
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    (gamma_compact_error N T hT hN z hz hz1) (gamma_tail_bound T hT z hz1))

end
end CarryC3Gamma
