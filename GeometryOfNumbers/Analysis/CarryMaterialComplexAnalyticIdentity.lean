import GeometryOfNumbers.Analysis.CarryMaterialComplexCauchyPick
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
Real-axis identity principle for a source-first complex C2 material signal.
No target characteristic appears in physical definitions.
-/

namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- Any two analytic scalar complex germs agreeing on all real heights
agree in a complex neighborhood of the center. The proof uses an explicit
sequence of distinct nonzero real heights 1/(n+1), never a synthetic
assumption that the equality already holds in a complex ball. -/
theorem analyticAt_eventuallyEq_of_forall_real
    (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0)
    (hReal : ∀ t : ℝ, f (t : ℂ) = g (t : ℂ)) :
    f =ᶠ[nhds 0] g := by
  apply (hf.frequently_eq_iff_eventually_eq hg).mp
  let a : ℕ → ℂ := fun n => (1 : ℂ) / ((n : ℂ) + 1)
  have haTendsto : Tendsto a atTop (nhds (0 : ℂ)) := by
    simpa only [a] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
  have haNonzero : ∀ n : ℕ, a n ≠ 0 := by
    intro n
    unfold a
    apply div_ne_zero (by norm_num)
    have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    exact_mod_cast Nat.succ_ne_zero n
  have haPunctured : Tendsto a atTop (nhdsWithin (0 : ℂ) {0}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within a haTendsto
      (Filter.Eventually.of_forall (fun n => by simpa using haNonzero n))
  apply haPunctured.frequently
  apply Filter.Frequently.of_forall
  intro n
  simpa only [a, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_one, ← Complex.ofReal_div] using
    hReal ((1 : ℝ) / ((n : ℝ) + 1))

/-- C2 scalar physical readout retains the source-first material return. -/
theorem carryMaterialComplexValueReadout_eq_source (z : ℂ) :
    carryMaterialComplexValueReadout z =
      carryMaterialComplexDressingScalar z * (1 + carryMaterialComplexReturn z) := by
  simp [carryMaterialComplexValueReadout, carryMaterialComplexDressedState,
    baseTwoCompletedBoundaryHilbertReadout_apply,
    carryMaterialComplexState, smul_eq_mul]

/-- The complete C2 physical scalar is holomorphic as a germ at the center
by the old norm-convergent material gradient, not by identification to xi. -/
theorem carryMaterialComplexValueReadout_analyticAt_zero :
    AnalyticAt ℂ carryMaterialComplexValueReadout 0 := by
  have hA : AnalyticAt ℂ canonicalArchimedeanCompletionComplex 0 :=
    (canonicalArchimedeanCompletionComplex_differentiableOn_ball 0).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have hQ : AnalyticAt ℂ baseTwoCanonicalCameraFactorComplex 0 :=
    (baseTwoCanonicalCameraFactorComplex_differentiable).analyticAt 0
  have hQnz : baseTwoCanonicalCameraFactorComplex 0 ≠ 0 :=
    baseTwoCanonicalCameraFactor_ne_zero 0
  have hT : AnalyticAt ℂ carryMaterialComplexReturn 0 :=
    (carryMaterialComplexReturn_differentiableOn_ball 0).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have h : AnalyticAt ℂ
      (fun z => (canonicalArchimedeanCompletionComplex z *
        (baseTwoCanonicalCameraFactorComplex z)⁻¹) *
          (1 + carryMaterialComplexReturn z)) 0 :=
    (hA.mul (hQ.inv hQnz)).mul (analyticAt_const.add hT)
  convert h using 1
  ext z
  rw [carryMaterialComplexValueReadout_eq_source]
  rfl



/-- Strong holomorphicity of the complete DRESSED PHYSICAL MATERIAL VECTOR,
not merely its scalar readout. This also controls the differentiated
companion on a complex neighborhood. -/
theorem carryMaterialComplexDressedState_analyticAt_zero :
    AnalyticAt ℂ carryMaterialComplexDressedState 0 := by
  have hA : AnalyticAt ℂ canonicalArchimedeanCompletionComplex 0 :=
    (canonicalArchimedeanCompletionComplex_differentiableOn_ball 0).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have hQ : AnalyticAt ℂ baseTwoCanonicalCameraFactorComplex 0 :=
    (baseTwoCanonicalCameraFactorComplex_differentiable).analyticAt 0
  have hQnz : baseTwoCanonicalCameraFactorComplex 0 ≠ 0 :=
    baseTwoCanonicalCameraFactor_ne_zero 0
  have hS : AnalyticAt ℂ carryMaterialComplexState 0 :=
    (carryMaterialComplexState_differentiableOn_ball 0).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have h := (hA.mul (hQ.inv hQnz)).smul hS
  convert h using 1
  funext z
  rfl

end
end GeometryOfNumbers.Analysis

#print axioms GeometryOfNumbers.Analysis.analyticAt_eventuallyEq_of_forall_real
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexValueReadout_analyticAt_zero
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexDressedState_analyticAt_zero