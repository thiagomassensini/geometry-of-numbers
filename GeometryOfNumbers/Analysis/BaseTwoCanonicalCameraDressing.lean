import GeometryOfNumbers.Analysis.BaseTwoCompletedSignalRegularity

/-! Concrete downstream camera dressing. The material signal has already
been synthesized. This factor does not define depth, amplitude or completion.
Historical formula: c2Factor(s)=(1+2^(-s))*(1-2^(1-s)), s=1/2+it. -/

noncomputable section
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- Complex extension of the real-height variable, with the native negative phase convention. -/
def baseTwoDressingParameter (w : ℂ) : ℂ := 1/2 + Complex.I*w

/-- Exact base-two camera denominator, downstream of synthesis. -/
def baseTwoCanonicalCameraFactorComplex (w : ℂ) : ℂ :=
  (1 + (2 : ℂ)^(-baseTwoDressingParameter w)) *
    (1 - (2 : ℂ)^(1-baseTwoDressingParameter w))

def baseTwoCanonicalCameraFactor (t : ℝ) : ℂ :=
  baseTwoCanonicalCameraFactorComplex (t : ℂ)

theorem baseTwoCanonicalCameraFactor_formula (t : ℝ) :
    baseTwoCanonicalCameraFactor t =
      (1+(2:ℂ)^(-(1/2+(t:ℂ)*Complex.I))) *
      (1-(2:ℂ)^(1-(1/2+(t:ℂ)*Complex.I))) := by
  simp only [baseTwoCanonicalCameraFactor, baseTwoCanonicalCameraFactorComplex,
    baseTwoDressingParameter, mul_comm Complex.I]

theorem baseTwoCanonicalCameraFactorComplex_differentiable :
    Differentiable ℂ baseTwoCanonicalCameraFactorComplex := by
  have hs : Differentiable ℂ baseTwoDressingParameter := by
    unfold baseTwoDressingParameter
    fun_prop
  exact (differentiable_const 1 |>.add (hs.neg.const_cpow (Or.inl (by norm_num)))).mul
    ((differentiable_const 1).sub
      (((differentiable_const 1).sub hs).const_cpow (Or.inl (by norm_num))))

theorem baseTwoCanonicalCameraFactor_analyticAt (t : ℝ) :
    AnalyticAt ℝ baseTwoCanonicalCameraFactor t := by
  have h := (baseTwoCanonicalCameraFactorComplex_differentiable.analyticAt (t:ℂ)).restrictScalars (𝕜:=ℝ)
  exact h.comp (Complex.ofRealCLM.analyticAt t)

theorem baseTwoCanonicalCameraFactor_contDiff : ContDiff ℝ ⊤ baseTwoCanonicalCameraFactor := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (baseTwoCanonicalCameraFactor_analyticAt t).contDiffAt

/-- Nonvanishing on the whole real-height line, from unequal moduli, not zeros of another function. -/
theorem baseTwoCanonicalCameraFactor_ne_zero (t : ℝ) :
    baseTwoCanonicalCameraFactor t ≠ 0 := by
  have hn : ‖(2:ℂ)^(-baseTwoDressingParameter (t:ℂ))‖ < 1 := by
    rw [show (2:ℂ)=(2:ℝ) from rfl, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    norm_num [baseTwoDressingParameter, Complex.mul_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hp : 1 < ‖(2:ℂ)^(1-baseTwoDressingParameter (t:ℂ))‖ := by
    rw [show (2:ℂ)=(2:ℝ) from rfl, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    norm_num [baseTwoDressingParameter, Complex.mul_re]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  apply mul_ne_zero
  · intro h
    have he : (2:ℂ)^(-baseTwoDressingParameter (t:ℂ)) = -1 := by linear_combination h
    rw [he] at hn
    norm_num at hn
  · intro h
    have he : (2:ℂ)^(1-baseTwoDressingParameter (t:ℂ)) = 1 := by linear_combination -h
    rw [he] at hp
    norm_num at hp

/-- Exact center value of the camera denominator. -/
theorem baseTwoCanonicalCameraFactor_zero :
    baseTwoCanonicalCameraFactor 0 = -(((2:ℝ)^(-1/2:ℝ) : ℝ):ℂ) := by
  have hq : (2:ℝ)^(-1/2:ℝ) * (2:ℝ)^(-1/2:ℝ) = (1/2:ℝ) := by
    rw [← Real.rpow_add (by norm_num), show (-1/2:ℝ)+(-1/2) = -1 by ring]
    norm_num
  have hp : (2:ℝ)^(1/2:ℝ) = 2*(2:ℝ)^(-1/2:ℝ) := by
    rw [show (1/2:ℝ)=1+(-1/2) by ring, Real.rpow_add (by norm_num)]
    simp
  have he : (1+(2:ℝ)^(-1/2:ℝ))*(1-(2:ℝ)^(1/2:ℝ)) = -(2:ℝ)^(-1/2:ℝ) := by
    rw [hp]
    nlinarith
  unfold baseTwoCanonicalCameraFactor baseTwoCanonicalCameraFactorComplex baseTwoDressingParameter
  norm_num only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [show -(1/2:ℂ) = ((-1/2:ℝ):ℂ) by norm_num,
    show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
    show (2:ℂ)=((2:ℝ):ℂ) by norm_num,
    ← Complex.ofReal_cpow (by norm_num), ← Complex.ofReal_cpow (by norm_num)]
  convert congrArg Complex.ofReal he using 1 <;> push_cast <;> norm_num

/-- Normalized Taylor coefficients, with the existing factorial convention. -/
def baseTwoCanonicalCameraFactorSeries : PowerSeries ℂ :=
  PowerSeries.mk (fun r => (r.factorial:ℂ)⁻¹ * iteratedDeriv r baseTwoCanonicalCameraFactor 0)

@[simp] theorem baseTwoCanonicalCameraFactorSeries_coeff (r : ℕ) :
    PowerSeries.coeff r baseTwoCanonicalCameraFactorSeries =
      (r.factorial:ℂ)⁻¹ * iteratedDeriv r baseTwoCanonicalCameraFactor 0 :=
  PowerSeries.coeff_mk _ _

@[simp] theorem baseTwoCanonicalCameraFactorSeries_constantCoeff :
    PowerSeries.constantCoeff baseTwoCanonicalCameraFactorSeries = baseTwoCanonicalCameraFactor 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, baseTwoCanonicalCameraFactorSeries_coeff]
  simp

theorem baseTwoCanonicalCameraFactorSeries_constantCoeff_ne_zero :
    PowerSeries.constantCoeff baseTwoCanonicalCameraFactorSeries ≠ 0 := by
  rw [baseTwoCanonicalCameraFactorSeries_constantCoeff]
  exact baseTwoCanonicalCameraFactor_ne_zero 0

end GeometryOfNumbers.Analysis.BaseTwoCompletion
