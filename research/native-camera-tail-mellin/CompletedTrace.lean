import TailJets

namespace CarryCameraTail
open CarryMaterialTheta CarrySelfAdjointOperator CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary NativeCarrySpectralWeyl.Camera MeasureTheory Set Filter
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option autoImplicit false

def cameraHeatHead (M : ℕ) (x : ℝ) : ℂ :=
  heatSample 1 x + cameraHeatPrefix 0 M x

def heatTrace (f : ℝ → ℂ) (s : ℂ) : ℂ × ℂ :=
  (mellin f (s/2), -(1/2 : ℂ)*mellin (fun x : ℝ => Real.log x • f x) (s/2))

def nativeHeadTrace (M : ℕ) (s : ℂ) : ℂ × ℂ :=
  (finiteBracketedDirichletChart 3 M s, finiteCanonicalLogBracketChart M s)

def nativeTailTrace (M : ℕ) (s : ℂ) : ℂ × ℂ :=
  ((canonicalC3BracketTfvdCompletionState M s).valueTail,
   (canonicalC3BracketTfvdCompletionState M s).logJetTail)

theorem camera_head_norm_le (M : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖cameraHeatHead M x‖ ≤ 2*heat 1 x := by
  have hpre := camera_prefix_norm_le 0 M hx.le
  have hmono := heat_antitone hx.le (show 1 ≤ 2 by omega)
  have hn : ‖heatSample 1 x‖ = heat 1 x := by
    simp only [heatSample, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, heat]
  have htriangle := norm_add_le (heatSample 1 x) (cameraHeatPrefix 0 M x)
  change ‖heatSample 1 x + cameraHeatPrefix 0 M x‖ ≤ _
  rw [hn] at htriangle
  norm_num only at hpre
  linarith

theorem camera_head_continuous (M : ℕ) : Continuous (cameraHeatHead M) := by
  unfold cameraHeatHead
  have h : Continuous (heatSample 1) := by unfold heatSample; fun_prop
  exact h.add (camera_prefix_continuous 0 M)

theorem camera_head_mellin_convergent (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (cameraHeatHead M) (s/2) :=
  (hasMellin_add (heat_mellin_convergent 1 (by omega) hs)
    (camera_prefix_mellin_convergent 0 M hs)).1

theorem camera_head_mellin (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    mellin (cameraHeatHead M) (s/2) =
      Complex.Gammaℝ s * finiteBracketedDirichletChart 3 M s := by
  have hone := finite_address_mellin 1 (fun _ => 1) (fun _ => 1) (by simp) hs
  simp only [Fin.sum_univ_one, one_mul, dirichletValue,
    Nat.cast_one, Complex.one_cpow] at hone
  have h := (hasMellin_add (heat_mellin_convergent 1 (by omega) hs)
    (camera_prefix_mellin_convergent 0 M hs)).2
  change mellin (cameraHeatHead M) (s/2) = _ at h
  rw [hone, camera_prefix_mellin 0 M hs] at h
  rw [h, finiteBracketedDirichletChart, seedSum_three_dirichlet_eq_one]
  simp only [Nat.add_zero]
  ring

theorem camera_head_trace_calibration (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    heatTrace (cameraHeatHead M) s = gammaDress s (nativeHeadTrace M s) := by
  have hderiv := (bounded_heat_mellin_hasDerivAt (cameraHeatHead M) 1 (by omega)
    2 (by norm_num) (camera_head_continuous M).aestronglyMeasurable
    (fun _ hx => camera_head_norm_le M hx) hs).2
  have hn := (gammaR_differentiableAt hs).hasDerivAt.mul
    (hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet M s)
  have heq : (fun z : ℂ => mellin (cameraHeatHead M) (z/2)) =ᶠ[𝓝 s]
      (fun z : ℂ => Complex.Gammaℝ z * finiteBracketedDirichletChart 3 M z) := by
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)] with z hz
    exact camera_head_mellin M hz
  have hcoeff := hderiv.unique (hn.congr_of_eventuallyEq heq)
  apply Prod.ext
  · exact camera_head_mellin M hs
  · change -(1/2 : ℂ)*mellin (fun x : ℝ => Real.log x • cameraHeatHead M x) (s/2) =
      Complex.Gammaℝ s*finiteCanonicalLogBracketChart M s -
        deriv Complex.Gammaℝ s*finiteBracketedDirichletChart 3 M s
    linear_combination -hcoeff

/-- Exact synthesis before pairing. The seed is retained, and the tail
is the omitted part of the same Gaussian camera sequence. -/
theorem camera_heat_head_tail (M : ℕ) {x : ℝ} (hx : 0 < x) :
    cameraHeatHead M x + cameraHeatTail M x =
      heatSample 1 x + cameraHeatTail 0 x := by
  have h := (summable_camera_blocks 0 hx).sum_add_tsum_nat_add M
  simpa only [cameraHeatHead, cameraHeatPrefix, cameraHeatTail, Nat.add_zero,
    add_assoc] using congrArg (fun z : ℂ => heatSample 1 x + z) h

/-- Both stored fields and the finite Green port now have images from their
literal source. This is a simultaneous projection theorem, not an isometry
of every component of the enriched physical transport. -/
theorem original_record_projections_mellin (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (cellwiseMellinPort (M*3) (nativeHeatGreenPort (M*3) s) s,
      (heatTrace (cameraHeatHead M) s, heatTailTrace M s)) =
    (Complex.Gammaℝ s • (canonicalC3BracketTfvdCompletionState M s).greenPort,
      (gammaDress s
        ((canonicalC3BracketTfvdCompletionState M s).transport.valueReadout,
         (canonicalC3BracketTfvdCompletionState M s).transport.logJetReadout),
       gammaDress s (nativeTailTrace M s))) := by
  rw [original_tfvd_green_projection_mellin M hs, camera_head_trace_calibration M hs,
    original_stored_tail_trace M hs]
  rw [(canonicalC3BracketTfvdCompletionState_transport_components M s).1,
    (canonicalC3BracketTfvdCompletionState_transport_components M s).2.1]
  rfl

theorem gammaDress_add (s : ℂ) (p q : ℂ × ℂ) :
    gammaDress s (p+q) = gammaDress s p + gammaDress s q := by
  apply Prod.ext <;> simp [gammaDress] <;> ring

/-- The completed value and negative-derivative trace is assembled only
after the head and tail channels have both been transported. -/
theorem completed_heat_trace_calibration (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    heatTrace (cameraHeatHead M) s + heatTailTrace M s =
      gammaDress s ((canonicalC3BracketTfvdCompletionState M s).valueReadout,
        (canonicalC3BracketTfvdCompletionState M s).logJetReadout) := by
  rw [camera_head_trace_calibration M hs, original_stored_tail_trace M hs,
    ← gammaDress_add]
  unfold CanonicalC3BracketTfvdCompletionState.valueReadout
    CanonicalC3BracketTfvdCompletionState.logJetReadout
  rw [(canonicalC3BracketTfvdCompletionState_transport_components M s).1,
    (canonicalC3BracketTfvdCompletionState_transport_components M s).2.1]
  rfl

/-- Independent parameters and independent cutoffs: all four ordered
head/tail crossings are retained in the original scalar Green form. -/
theorem completed_heat_green_four_crosses (M N : ℕ) {s t : ℂ}
    (hs : 0 < s.re) (ht : 0 < t.re) :
    greenForm (𝕜 := ℂ)
      (heatTrace (cameraHeatHead M) s + heatTailTrace M s)
      (heatTrace (cameraHeatHead N) t + heatTailTrace N t) =
      greenForm (𝕜 := ℂ) (gammaDress s (nativeHeadTrace M s)) (gammaDress t (nativeHeadTrace N t)) +
      greenForm (𝕜 := ℂ) (gammaDress s (nativeHeadTrace M s)) (gammaDress t (nativeTailTrace N t)) +
      greenForm (𝕜 := ℂ) (gammaDress s (nativeTailTrace M s)) (gammaDress t (nativeHeadTrace N t)) +
      greenForm (𝕜 := ℂ) (gammaDress s (nativeTailTrace M s)) (gammaDress t (nativeTailTrace N t)) := by
  rw [camera_head_trace_calibration M hs, camera_head_trace_calibration N ht,
    heat_tail_trace_calibration M hs, heat_tail_trace_calibration N ht]
  simp only [nativeTailTrace, canonicalC3BracketTfvdCompletionState, greenForm, Prod.fst_add, Prod.snd_add,
    inner_add_left, inner_add_right]
  ring

/-- The full Gamma defect survives completion and both independent inputs.
No value-value term is deleted or assigned a favorable sign. -/
theorem completed_heat_green_gamma_defect (M N : ℕ) {s t : ℂ}
    (hs : 0 < s.re) (ht : 0 < t.re) :
    let p := nativeHeadTrace M s + nativeTailTrace M s
    let q := nativeHeadTrace N t + nativeTailTrace N t
    greenForm (𝕜 := ℂ)
      (heatTrace (cameraHeatHead M) s + heatTailTrace M s)
      (heatTrace (cameraHeatHead N) t + heatTailTrace N t) =
      conj (Complex.Gammaℝ s)*Complex.Gammaℝ t * greenForm (𝕜 := ℂ) p q +
        (conj (Complex.Gammaℝ s)*deriv Complex.Gammaℝ t -
          conj (deriv Complex.Gammaℝ s)*Complex.Gammaℝ t)*inner ℂ p.1 q.1 := by
  dsimp only
  rw [camera_head_trace_calibration M hs, camera_head_trace_calibration N ht,
    heat_tail_trace_calibration M hs, heat_tail_trace_calibration N ht,
    ← gammaDress_add, ← gammaDress_add]
  exact gammaDress_green_defect s t _ _

end
end CarryCameraTail
