import NativeCompletion

/-! Literal native consecutive edges, retaining their value and log jet.
The source is specified before Mellin and contains no moment sequence. -/
namespace CarryFourLeg
open CarryCameraTail CarryMaterialTheta CarrySelfAdjointOperator CPFormal.Analytic.Cp
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

def heatEdge (n : ℕ) (x : ℝ) : ℂ := heatSample (n+2) x - heatSample (n+1) x

theorem heat_edge_continuous (n : ℕ) : Continuous (heatEdge n) := by
  unfold heatEdge heatSample
  fun_prop

theorem heat_edge_norm_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖heatEdge n x‖ ≤ heat (n+1) x := by
  have h := heat_antitone hx.le (show n+1 ≤ n+2 by omega)
  have heq : heatEdge n x = ((heat (n+2) x - heat (n+1) x : ℝ) : ℂ) := by
    simp only [heatEdge, heatSample, heat, Complex.ofReal_sub]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  have hp : 0 < heat (n+2) x := Real.exp_pos _
  linarith

theorem heat_edge_mellin (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    mellin (heatEdge n) (s/2) = Complex.Gammaℝ s * positiveDirichletGradient s n := by
  change mellin (fun x => heatSample (n+2) x - heatSample (n+1) x) (s/2) = _
  rw [heat_difference_mellin _ _ (by omega) (by omega) hs]
  simp only [positiveDirichletGradient, natDirichletTerm, dirichletTerm,
    NativeCarrySpectralWeyl.Camera.dirichletValue]
  push_cast
  rfl

theorem native_gradient_hasDerivAt (n : ℕ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => positiveDirichletGradient z n)
      (-positiveLogDirichletGradient s n) s := by
  have h := (hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm (n+2) (by omega) s).sub
    (hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm (n+1) (by omega) s)
  have hfun : ((fun z : ℂ => natDirichletTerm z (n+2)) -
      (fun z : ℂ => natDirichletTerm z (n+1))) =
      (fun z : ℂ => positiveDirichletGradient z n) := rfl
  have hd : -natLogDirichletTerm s (n+2) - -natLogDirichletTerm s (n+1) =
      -positiveLogDirichletGradient s n := by
    rw [positiveLogDirichletGradient, positiveLogDirichletValue_eq_natLogDirichletTerm,
      positiveLogDirichletValue_eq_natLogDirichletTerm]
    ring
  rw [hfun, hd] at h
  exact h

/-- Both components are actual integrals of the same addressed heat edge.
The Gamma derivative is kept before recovering the material log jet. -/
theorem heat_edge_trace_calibration (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    heatTrace (heatEdge n) s = gammaDress s
      (positiveDirichletGradient s n, positiveLogDirichletGradient s n) := by
  have hi := (bounded_heat_mellin_hasDerivAt (heatEdge n) (n+1) (by omega)
    1 zero_le_one (heat_edge_continuous n).aestronglyMeasurable
    (fun _ hx => by simpa only [one_mul] using heat_edge_norm_le n hx) hs).2
  have hn := (gammaR_differentiableAt hs).hasDerivAt.mul (native_gradient_hasDerivAt n s)
  have heq : (fun z : ℂ => mellin (heatEdge n) (z/2)) =ᶠ[𝓝 s]
      (fun z : ℂ => Complex.Gammaℝ z * positiveDirichletGradient z n) := by
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)] with z hz
    exact heat_edge_mellin n hz
  have hcoef := hi.unique (hn.congr_of_eventuallyEq heq)
  apply Prod.ext
  · exact heat_edge_mellin n hs
  · change -(1/2 : ℂ)*mellin (fun x : ℝ => Real.log x • heatEdge n x) (s/2) =
      Complex.Gammaℝ s*positiveLogDirichletGradient s n -
        deriv Complex.Gammaℝ s*positiveDirichletGradient s n
    linear_combination -hcoef

def materialEdgeTrace (n : ℕ) (s : ℂ) : ℂ × ℂ :=
  gammaUndress s (heatTrace (heatEdge n) s)

theorem material_edge_trace_eq (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    materialEdgeTrace n s =
      (positiveDirichletGradient s n, positiveLogDirichletGradient s n) := by
  rw [materialEdgeTrace, heat_edge_trace_calibration n hs, gammaUndress_gammaDress hs]

end
end CarryFourLeg
