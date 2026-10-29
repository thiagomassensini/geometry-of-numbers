import RadialReconstruction
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

namespace CarryBoundaryReconstruction
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- The full analytic remainder is retained; L has no sign hypothesis. -/
def quadraticExtension (L C : ℝ) (R : ℂ → ℂ) (h : ℝ) : ℝ :=
  L+C*h^2+h^3*(R (h:ℂ)).re

theorem quadratic_extension_derivative (L C : ℝ) (R : ℂ → ℂ) (h : ℝ)
    (hR : AnalyticAt ℂ R (h:ℂ)) :
    HasDerivAt (quadraticExtension L C R)
      (h*(2*C+3*h*(R (h:ℂ)).re+h^2*(deriv R (h:ℂ)).re)) h := by
  have hr := hR.differentiableAt.hasDerivAt.real_of_complex
  have hd := (hasDerivAt_const h L).add
    (((hasDerivAt_id h).pow 2).const_mul C) |>.add
      (((hasDerivAt_id h).pow 3).mul hr)
  convert hd using 1
  all_goals try rfl
  all_goals (simp [Pi.pow_apply]; ring)

/-- Positive second correction orients ALL sufficiently small radial steps,
not merely the difference from the limiting value. -/
theorem quadratic_extension_strictMono (L C : ℝ) (R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 0) (hC : 0<C) :
    ∃ ε : ℝ, 0<ε ∧ StrictMonoOn (quadraticExtension L C R) (Set.Ioo 0 ε) := by
  let v : ℝ → ℝ := fun h => 2*C+3*h*(R (h:ℂ)).re+h^2*(deriv R (h:ℂ)).re
  have hc : ContinuousAt v 0 := by
    have hr := Complex.continuous_re.continuousAt.comp
      (hR.continuousAt.comp (f := fun h : ℝ => (h:ℂ)) Complex.continuous_ofReal.continuousAt)
    have hdr := Complex.continuous_re.continuousAt.comp
      (hR.deriv.continuousAt.comp (f := fun h : ℝ => (h:ℂ)) Complex.continuous_ofReal.continuousAt)
    exact ((continuousAt_const.add ((continuousAt_const.mul continuousAt_id).mul hr)).add
      ((continuousAt_id.pow 2).mul hdr))
  have hv : 0<v 0 := by simpa [v] using (mul_pos (by norm_num : (0:ℝ)<2) hC)
  have ha : ∀ᶠ h : ℝ in nhds 0, AnalyticAt ℂ R (h:ℂ) :=
    Complex.continuous_ofReal.continuousAt.tendsto.eventually hR.eventually_analyticAt
  have hvp : ∀ᶠ h : ℝ in nhds 0, 0<v h :=
    Filter.Tendsto.eventually_lt tendsto_const_nhds hc.tendsto hv
  have he := ha.and hvp
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε,hε,?_⟩
  have hp (h : ℝ) (hh : h∈Set.Ioo 0 ε) : AnalyticAt ℂ R (h:ℂ) ∧ 0<v h := by
    apply hball
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hh.1] using hh.2
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 ε)
  · intro h hh
    exact (quadratic_extension_derivative L C R h (hp h hh).1).continuousAt.continuousWithinAt
  · intro h hh
    rw [interior_Ioo] at hh
    rw [(quadratic_extension_derivative L C R h (hp h hh).1).deriv]
    exact mul_pos hh.1 (hp h hh).2

theorem quadratic_extension_tendsto (L C : ℝ) (R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 0) :
    Tendsto (quadraticExtension L C R) (nhds 0) (nhds L) := by
  have hr := Complex.continuous_re.continuousAt.comp
    (hR.continuousAt.comp (f := fun h : ℝ => (h:ℂ)) Complex.continuous_ofReal.continuousAt)
  have hc : ContinuousAt (quadraticExtension L C R) 0 := by
    exact (continuousAt_const.add (continuousAt_const.mul (continuousAt_id.pow 2))).add
      ((continuousAt_id.pow 3).mul hr)
  simpa [quadraticExtension] using hc.tendsto

end
end CarryBoundaryReconstruction
