import MellinTail

namespace CarryCameraTail
open CarryMaterialTheta CarrySelfAdjointOperator CPFormal.Analytic.Cp
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

/-- A common bound for literal camera sums. It gives the logarithmic Mellin
jet as an actual convergent integral. The constant is an analytic majorant,
not a modification of the source or of its metric. -/
theorem bounded_heat_mellin_hasDerivAt (f : ℝ → ℂ) (n : ℕ) (hn : 0 < n)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hbound : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ C*heat n x)
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => Real.log x • f x) (s/2) ∧
      HasDerivAt (fun z : ℂ => mellin f (z/2))
        ((1/2 : ℂ)*mellin (fun x : ℝ => Real.log x • f x) (s/2)) s := by
  let a : ℝ := Real.pi*(n : ℝ)^2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : IntegrableOn (fun x : ℝ => C*heat n x) (Ioi 0) := by
    have heq : (fun x : ℝ => C*heat n x) =
        (fun x : ℝ => C*Real.exp (-a*x)) := by
      funext x
      simp only [heat, a, neg_mul, mul_assoc]
    rw [heq]
    exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).const_mul C
  have hlocal : LocallyIntegrableOn f (Ioi 0) := by
    apply IntegrableOn.locallyIntegrableOn
    refine Integrable.mono' hb hf ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbound x hx
  have htop : f =O[atTop] (fun x : ℝ => Real.exp (-a*x)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa only [Real.norm_eq_abs, Real.abs_exp, heat, a, neg_mul, mul_assoc] using hbound x hx
  have hbot : f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x^(-(0 : ℝ))) := by
    apply IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hle : heat n x ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (sq_nonneg _)) hx.le
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using
      (hbound x hx).trans (mul_le_of_le_one_right hC hle)
  have hm := mellin_hasDerivAt_of_isBigO_rpow hlocal
    (htop.trans (isLittleO_exp_neg_mul_rpow_atTop ha (-((s/2).re+1))).isBigO)
    (show (s/2).re < (s/2).re+1 by linarith) hbot
    (show 0 < (s/2).re by simpa using half_pos hs)
  refine ⟨hm.1, ?_⟩
  have hd := hm.2.comp s ((hasDerivAt_id s).div_const 2)
  have hfun : (mellin f ∘ fun z : ℂ => id z / 2) =
      (fun z : ℂ => mellin f (z/2)) := rfl
  have hcoef : mellin (fun x : ℝ => Real.log x • f x) (s/2) * (1/2) =
      (1/2 : ℂ)*mellin (fun x : ℝ => Real.log x • f x) (s/2) := by ring
  rw [hfun, hcoef] at hd
  exact hd

theorem tail_log_mellin_hasDerivAt (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => Real.log x • cameraHeatTail M x) (s/2) ∧
      HasDerivAt (fun z : ℂ => mellin (cameraHeatTail M) (z/2))
        ((1/2 : ℂ)*mellin (fun x : ℝ => Real.log x • cameraHeatTail M x) (s/2)) s := by
  refine bounded_heat_mellin_hasDerivAt (cameraHeatTail M) (3*M+2) (by omega)
    1 zero_le_one (camera_tail_measurable M) ?_ hs
  intro x hx
  simpa only [one_mul] using camera_tail_norm_le M hx

/-- Independent analytic differentiation of the actual Mellin integral.
This uses the original native tail derivative, not a target moment. -/
theorem tail_native_mellin_hasDerivAt (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z : ℂ => mellin (cameraHeatTail M) (z/2))
      (deriv Complex.Gammaℝ s * realCpBracketCutoffTail 3 M s -
        Complex.Gammaℝ s * canonicalC3LogJetCutoffTail M s) s := by
  have h := (gammaR_differentiableAt hs).hasDerivAt.mul
    (hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail M (by
      change -1 < s.re
      linarith))
  have heq : (fun z : ℂ => mellin (cameraHeatTail M) (z/2)) =ᶠ[𝓝 s]
      (fun z : ℂ => Complex.Gammaℝ z * realCpBracketCutoffTail 3 M z) := by
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)] with z hz
    exact camera_tail_mellin M hz
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

/-- The logarithmic tail contains the Gamma derivative. Omitting this term
would identify two different channels. Both sides are original quantities. -/
theorem camera_tail_log_mellin (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℝ s * canonicalC3LogJetCutoffTail M s =
      deriv Complex.Gammaℝ s * realCpBracketCutoffTail 3 M s -
        (1/2 : ℂ)*mellin (fun x : ℝ => Real.log x • cameraHeatTail M x) (s/2) := by
  have h := (tail_log_mellin_hasDerivAt M hs).2.unique (tail_native_mellin_hasDerivAt M hs)
  linear_combination h

/-- The Mellin-side value/negative-derivative pair is formed from the same
omitted camera source. No tail coordinate is supplied by inverse fitting. -/
def heatTailTrace (M : ℕ) (s : ℂ) : ℂ × ℂ :=
  (mellin (cameraHeatTail M) (s/2),
    -(1/2 : ℂ)*mellin (fun x : ℝ => Real.log x • cameraHeatTail M x) (s/2))

theorem heat_tail_trace_calibration (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    heatTailTrace M s = gammaDress s
      (realCpBracketCutoffTail 3 M s, canonicalC3LogJetCutoffTail M s) := by
  apply Prod.ext
  · exact camera_tail_mellin M hs
  · change -(1/2 : ℂ)*mellin (fun x : ℝ => Real.log x • cameraHeatTail M x) (s/2) =
      Complex.Gammaℝ s*canonicalC3LogJetCutoffTail M s -
      deriv Complex.Gammaℝ s*realCpBracketCutoffTail 3 M s
    rw [camera_tail_log_mellin M hs]
    ring

theorem original_stored_tail_trace (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    heatTailTrace M s = gammaDress s
      ((canonicalC3BracketTfvdCompletionState M s).valueTail,
       (canonicalC3BracketTfvdCompletionState M s).logJetTail) :=
  heat_tail_trace_calibration M hs

end
end CarryCameraTail
