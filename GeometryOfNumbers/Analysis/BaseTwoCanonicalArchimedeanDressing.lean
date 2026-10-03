import GeometryOfNumbers.Analysis.BaseTwoCanonicalCameraDressing
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! Explicit archimedean comparison dressing, applied after exact synthesis.
No identification with a zeta/xi function is used. The normalization and
height parameter reproduce the historical formula directly. -/

noncomputable section
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- Classical explicit polynomial/exponential/Gamma dressing. -/
def canonicalArchimedeanCompletionComplex (w : ℂ) : ℂ :=
  let s := baseTwoDressingParameter w
  (1/2:ℂ)*s*(s-1)*
    Complex.exp (-(s/2)*(Real.log Real.pi:ℂ))*Complex.Gamma (s/2)

def canonicalArchimedeanCompletion (t : ℝ) : ℂ :=
  canonicalArchimedeanCompletionComplex (t:ℂ)

theorem canonicalArchimedeanCompletion_formula (t : ℝ) :
    canonicalArchimedeanCompletion t =
      let s : ℂ := 1/2 + Complex.I*(t:ℂ)
      (1/2:ℂ)*s*(s-1)*Complex.exp (-(s/2)*(Real.log Real.pi:ℂ))*Complex.Gamma (s/2) := rfl

/-- In a quarter ball around any real time, the Gamma argument has positive real part. -/
theorem canonicalArchimedeanCompletionComplex_differentiableOn_ball (t : ℝ) :
    DifferentiableOn ℂ canonicalArchimedeanCompletionComplex (Metric.ball (t:ℂ) (1/4:ℝ)) := by
  have hs : Differentiable ℂ baseTwoDressingParameter := by
    unfold baseTwoDressingParameter
    fun_prop
  intro w hw
  have him : w.im < (1/4:ℝ) := by
    have h := Complex.im_le_norm (w-(t:ℂ))
    have hb := hw
    simp only [Metric.mem_ball, dist_eq_norm] at hb
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith
  have hre : 0 < (baseTwoDressingParameter w / 2).re := by
    norm_num [baseTwoDressingParameter, Complex.div_re, Complex.mul_re]
    linarith
  have hgamma : DifferentiableAt ℂ (fun z => Complex.Gamma (baseTwoDressingParameter z/2)) w := by
    apply (Complex.differentiableAt_Gamma _ ?_).comp w (hs.div_const 2).differentiableAt
    intro m hm
    have h := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at h
    have hmpos : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hpoly : Differentiable ℂ (fun z => (1/2:ℂ)*baseTwoDressingParameter z*(baseTwoDressingParameter z-1)) :=
    ((differentiable_const _).mul hs).mul (hs.sub (differentiable_const _))
  have hexp : Differentiable ℂ (fun z => Complex.exp (-(baseTwoDressingParameter z/2)*(Real.log Real.pi:ℂ))) :=
    (((hs.div_const 2).neg).mul (differentiable_const _)).cexp
  exact ((hpoly.differentiableAt.mul hexp.differentiableAt).mul hgamma).differentiableWithinAt

theorem canonicalArchimedeanCompletion_analyticAt (t : ℝ) :
    AnalyticAt ℝ canonicalArchimedeanCompletion t := by
  have h := (canonicalArchimedeanCompletionComplex_differentiableOn_ball t).analyticAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  exact (h.restrictScalars (𝕜:=ℝ)).comp (Complex.ofRealCLM.analyticAt t)

theorem canonicalArchimedeanCompletion_contDiff : ContDiff ℝ ⊤ canonicalArchimedeanCompletion := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (canonicalArchimedeanCompletion_analyticAt t).contDiffAt

/-- The center constant is explicitly real and strictly negative. -/
theorem canonicalArchimedeanCompletion_zero :
    canonicalArchimedeanCompletion 0 =
      ((-(1/8:ℝ)*Real.exp (-(Real.log Real.pi)/4)*Real.Gamma (1/4:ℝ):ℝ):ℂ) := by
  unfold canonicalArchimedeanCompletion canonicalArchimedeanCompletionComplex baseTwoDressingParameter
  norm_num only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [show (1/4:ℂ) = ((1/4:ℝ):ℂ) by norm_num, Complex.Gamma_ofReal]
  have he : -( (1/4:ℝ):ℂ)*(Real.log Real.pi:ℂ) = ((-(Real.log Real.pi)/4:ℝ):ℂ) := by
    push_cast
    ring
  rw [he, ← Complex.ofReal_exp]
  push_cast
  ring

theorem canonicalArchimedeanCompletion_zero_re_neg :
    (canonicalArchimedeanCompletion 0).re < 0 := by
  rw [canonicalArchimedeanCompletion_zero, Complex.ofReal_re]
  have hg := Real.Gamma_pos_of_pos (s:=1/4) (by norm_num)
  have he := Real.exp_pos (-(Real.log Real.pi)/4)
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) he) hg

theorem canonicalArchimedeanCompletion_zero_ne_zero :
    canonicalArchimedeanCompletion 0 ≠ 0 := by
  intro h
  have hn := canonicalArchimedeanCompletion_zero_re_neg
  rw [h] at hn
  norm_num at hn

def baseTwoCanonicalCompletionSeries : PowerSeries ℂ :=
  PowerSeries.mk (fun r => (r.factorial:ℂ)⁻¹ * iteratedDeriv r canonicalArchimedeanCompletion 0)

@[simp] theorem baseTwoCanonicalCompletionSeries_coeff (r : ℕ) :
    PowerSeries.coeff r baseTwoCanonicalCompletionSeries =
      (r.factorial:ℂ)⁻¹ * iteratedDeriv r canonicalArchimedeanCompletion 0 :=
  PowerSeries.coeff_mk _ _

@[simp] theorem baseTwoCanonicalCompletionSeries_constantCoeff :
    PowerSeries.constantCoeff baseTwoCanonicalCompletionSeries = canonicalArchimedeanCompletion 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, baseTwoCanonicalCompletionSeries_coeff]
  simp

theorem baseTwoCanonicalCompletionSeries_constantCoeff_ne_zero :
    PowerSeries.constantCoeff baseTwoCanonicalCompletionSeries ≠ 0 := by
  rw [baseTwoCanonicalCompletionSeries_constantCoeff]
  exact canonicalArchimedeanCompletion_zero_ne_zero

end GeometryOfNumbers.Analysis.BaseTwoCompletion
