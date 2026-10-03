import GeometryOfNumbers.Analysis.BaseTwoSynthesizedClockCompletion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Regularity is proved for the already-synthesized signal. The complex
extension below agrees exactly with its real-time samples and is used only
for a local uniform bound on complete cells, not as a second clock. -/

noncomputable section
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GeometryOfNumbers.Analysis.FiniteClockJets

/-- Analytic extension of the existing material exponent. -/
def baseTwoComplexMaterialExponent (w : ℂ) : ℂ := -1 / 2 - w * Complex.I

def baseTwoComplexCenterCell (w : ℂ) (k : ℕ) : ℂ :=
  (baseTwoLeftLeg k : ℂ) ^ baseTwoComplexMaterialExponent w -
    2 * (baseTwoCenter k : ℂ) ^ baseTwoComplexMaterialExponent w +
    (baseTwoRightLeg k : ℂ) ^ baseTwoComplexMaterialExponent w

def baseTwoComplexCompleteSignal (w : ℂ) : ℂ :=
  1 + ∑' k : ℕ, baseTwoComplexCenterCell w k

theorem baseTwoComplexCenterCell_ofReal (t : ℝ) (k : ℕ) :
    baseTwoComplexCenterCell (t : ℂ) k = baseTwoCriticalCenterCell t k := by
  unfold baseTwoComplexCenterCell baseTwoCriticalCenterCell
  rw [criticalMaterialSample_eq_cpow t (by simp; omega),
    criticalMaterialSample_eq_cpow t (by simp),
    criticalMaterialSample_eq_cpow t (by simp)]
  rfl

theorem baseTwoComplexCompleteSignal_ofReal (t : ℝ) :
    baseTwoComplexCompleteSignal (t : ℂ) = baseTwoCriticalCompleteSignal t := by
  simp only [baseTwoComplexCompleteSignal, baseTwoCriticalCompleteSignal,
    criticalMaterialSample_one, baseTwoComplexCenterCell_ofReal]

private theorem complexExponent_differentiable : Differentiable ℂ baseTwoComplexMaterialExponent := by
  unfold baseTwoComplexMaterialExponent
  fun_prop

private theorem complexCell_differentiable (k : ℕ) :
    Differentiable ℂ (fun w => baseTwoComplexCenterCell w k) := by
  have hl : (baseTwoLeftLeg k : ℂ) ≠ 0 := by
    exact_mod_cast (show baseTwoLeftLeg k ≠ 0 by simp; omega)
  have hc : (baseTwoCenter k : ℂ) ≠ 0 := by
    exact_mod_cast (show baseTwoCenter k ≠ 0 by simp)
  have hr : (baseTwoRightLeg k : ℂ) ≠ 0 := by
    exact_mod_cast (show baseTwoRightLeg k ≠ 0 by simp)
  exact ((complexExponent_differentiable.const_cpow (Or.inl hl)).sub
    ((complexExponent_differentiable.const_cpow (Or.inl hc)).const_mul 2)).add
      (complexExponent_differentiable.const_cpow (Or.inl hr))

/-- Uniform whole-cell majorant in a quarter-radius ball around every real time. -/
theorem baseTwoComplexCenterCell_norm_le (t : ℝ) (k : ℕ) (w : ℂ)
    (hw : w ∈ Metric.ball (t : ℂ) (1/4 : ℝ)) :
    ‖baseTwoComplexCenterCell w k‖ ≤
      ((|t|+2)*(|t|+3)) * ((k+1 : ℕ) : ℝ)^(-9/4 : ℝ) := by
  let z := baseTwoComplexMaterialExponent w
  let a : ℝ := (baseTwoLeftLeg k : ℕ)
  have hdist : ‖w - (t : ℂ)‖ < (1/4 : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hwNorm : ‖w‖ ≤ |t|+1 := by
    have h := norm_add_le (w-(t:ℂ)) (t:ℂ)
    rw [sub_add_cancel] at h
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hwIm : w.im ≤ (1/4 : ℝ) := by
    have h := Complex.im_le_norm (w-(t:ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith
  have hzRe : z.re ≤ (-1/4 : ℝ) := by
    norm_num [z, baseTwoComplexMaterialExponent, Complex.mul_re] at *
    linarith
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzRe; norm_num at hzRe
  have hz1 : z-1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  have hzNorm : ‖z‖ ≤ |t|+2 := by
    have h := norm_sub_le (-1/2 : ℂ) (w*Complex.I)
    norm_num [norm_mul, Complex.norm_I] at h
    dsimp [z, baseTwoComplexMaterialExponent]
    linarith
  have hz1Norm : ‖z-1‖ ≤ |t|+3 := by
    have h := norm_sub_le z (1:ℂ)
    norm_num at h
    linarith
  have hC : ‖z*(z-1)‖ ≤ (|t|+2)*(|t|+3) := by
    rw [norm_mul]
    exact mul_le_mul hzNorm hz1Norm (norm_nonneg _) (by positivity)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (show 0 < baseTwoLeftLeg k by simp; omega)
  have hka : ((k+1 : ℕ) : ℝ) ≤ a := by
    dsimp [a]
    have h : k+1 ≤ baseTwoLeftLeg k := by simp; omega
    exact_mod_cast h
  have hfun : baseTwoComplexCenterCell w k =
      ((a+2 : ℝ) : ℂ)^z - 2*((a+1 : ℝ) : ℂ)^z + (a:ℂ)^z := by
    have hc : baseTwoCenter k = baseTwoLeftLeg k+1 := by simp; omega
    have hr : baseTwoRightLeg k = baseTwoLeftLeg k+2 := by simp; omega
    simp only [baseTwoComplexCenterCell, hc, hr, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat, a, z, Complex.ofReal_natCast,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hb : ∀ x ∈ Set.Icc a (a+2),
      ‖z*(z-1)*(x:ℂ)^(z-2)‖ ≤ (|t|+2)*(|t|+3)*((k+1:ℕ):ℝ)^(-9/4:ℝ) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hx1 : 1 ≤ x := by
      have hk : (1:ℝ) ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_pos k)
      exact hk.trans (hka.trans hx.1)
    have he : (z-2).re ≤ (-9/4:ℝ) := by
      norm_num [Complex.sub_re]
      linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hp : x^((z-2).re) ≤ ((k+1:ℕ):ℝ)^(-9/4:ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hx1 he).trans
        (Real.rpow_le_rpow_of_nonpos (by positivity) (hka.trans hx.1) (by norm_num))
    exact mul_le_mul hC hp (Real.rpow_nonneg hxpos.le _) (by positivity)
  rw [hfun]
  exact baseTwoSecondDifference_norm_le
    (fun x => (x:ℂ)^z) (fun x => z*(x:ℂ)^(z-1))
    (fun x => z*(z-1)*(x:ℂ)^(z-2)) a _
    (fun x hx => hasDerivAt_ofReal_cpow_const
      (ne_of_gt (lt_of_lt_of_le ha hx.1)) hz)
    (by
      intro x hx
      have h := (hasDerivAt_ofReal_cpow_const (r:=z-1)
        (ne_of_gt (lt_of_lt_of_le ha hx.1)) hz1).const_mul z
      simpa only [show z-1-1=z-2 by ring, mul_assoc] using h)
    hb

theorem baseTwoComplexCompleteSignal_differentiableOn_ball (t : ℝ) :
    DifferentiableOn ℂ baseTwoComplexCompleteSignal (Metric.ball (t:ℂ) (1/4:ℝ)) := by
  have hp : Summable (fun k : ℕ => ((k+1:ℕ):ℝ)^(-9/4:ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num))
  have h := Complex.differentiableOn_tsum_of_summable_norm (hp.mul_left ((|t|+2)*(|t|+3)))
    (fun k => (complexCell_differentiable k).differentiableOn) Metric.isOpen_ball
    (fun k w hw => baseTwoComplexCenterCell_norm_le t k w hw)
  exact (differentiableOn_const (1:ℂ)).add h

theorem baseTwoCriticalCompleteSignal_contDiff : ContDiff ℝ ⊤ baseTwoCriticalCompleteSignal := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hC : ContDiffAt ℂ ⊤ baseTwoComplexCompleteSignal (t:ℂ) :=
    ((baseTwoComplexCompleteSignal_differentiableOn_ball t).contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have hR := (hC.restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  have he : baseTwoComplexCompleteSignal ∘ Complex.ofReal = baseTwoCriticalCompleteSignal :=
    funext baseTwoComplexCompleteSignal_ofReal
  simpa only [Complex.ofRealCLM_apply, he] using hR

/-- Local analyticity of the already-synthesized real-time signal. -/
theorem baseTwoCriticalCompleteSignal_analyticAt (t : ℝ) :
    AnalyticAt ℝ baseTwoCriticalCompleteSignal t := by
  have hC : AnalyticAt ℂ baseTwoComplexCompleteSignal (t : ℂ) :=
    (baseTwoComplexCompleteSignal_differentiableOn_ball t).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have hR := (hC.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have he : baseTwoComplexCompleteSignal ∘ Complex.ofReal = baseTwoCriticalCompleteSignal :=
    funext baseTwoComplexCompleteSignal_ofReal
  simpa only [Complex.ofRealCLM_apply, he] using hR

/-- The finite geometric head is smooth with the existing material clock. -/
theorem baseTwoFiniteHead_contDiff (M : ℕ) : ContDiff ℝ ⊤ (baseTwoFiniteHead M) := by
  have hs : ∀ n : ℕ, ContDiff ℝ ⊤ (fun t => criticalMaterialSample t n) := by
    intro n
    have hcast : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
    unfold criticalMaterialSample
    simp only [Complex.ofReal_mul]
    exact contDiff_const.mul (Complex.contDiff_exp.comp
      ((hcast.mul contDiff_const).mul contDiff_const).neg)
  have hc : ∀ k : ℕ, ContDiff ℝ ⊤ (fun t => baseTwoCriticalCenterCell t k) := by
    intro k
    exact ((hs (baseTwoLeftLeg k)).sub (contDiff_const.mul (hs (baseTwoCenter k)))).add
      (hs (baseTwoRightLeg k))
  exact (hs 1).add (ContDiff.sum (fun k _ => hc k))

/-- The geometric tail is the difference of smooth synthesized signal and head. -/
theorem baseTwoCriticalCompleteTail_contDiff (M : ℕ) :
    ContDiff ℝ ⊤ (baseTwoCriticalCompleteTail M) := by
  have he : baseTwoCriticalCompleteTail M =
      baseTwoCriticalCompleteSignal - baseTwoFiniteHead M := by
    funext t
    exact eq_sub_iff_add_eq.mpr (by
      simpa [add_comm] using baseTwoFiniteHead_add_completeTail M t)
  rw [he]
  exact baseTwoCriticalCompleteSignal_contDiff.sub (baseTwoFiniteHead_contDiff M)

/-- Genuine normalized Taylor jet of the already-defined whole-cell tail.
The proof rewrites a difference of smooth functions; it does not differentiate a tsum. -/
theorem baseTwoSynthesizedTailCoefficient_eq_normalizedTailJet (M r : ℕ) :
    baseTwoSynthesizedTailCoefficient M r =
      (r.factorial : ℂ)⁻¹ * iteratedDeriv r (baseTwoCriticalCompleteTail M) 0 := by
  have he : baseTwoCriticalCompleteTail M =
      baseTwoCriticalCompleteSignal - baseTwoFiniteHead M := by
    funext t
    exact eq_sub_iff_add_eq.mpr (by
      simpa [add_comm] using baseTwoFiniteHead_add_completeTail M t)
  rw [baseTwoSynthesizedTailCoefficient_eq_jetResidual, he,
    iteratedDeriv_sub
      ((baseTwoCriticalCompleteSignal_contDiff.of_le (by simp)).contDiffAt)
      (((baseTwoFiniteHead_contDiff M).of_le (by simp)).contDiffAt)]

end GeometryOfNumbers.Analysis.BaseTwoCompletion
