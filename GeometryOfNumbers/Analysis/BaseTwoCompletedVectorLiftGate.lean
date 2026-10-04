import GeometryOfNumbers.Analysis.BaseTwoCanonicalDressingMoments
import GeometryOfNumbers.Analysis.GreenParsevalMaterialLogOperator
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Module

/-!
# Scalar dressing on a preexisting vector carrier; the synthesis lift gate

No vector realizing the complete signal is defined here. A supplied vector
function is dressed using the already concrete scalar factors. The readout
residual is exactly the undressed synthesis residual times that scalar.
This does not identify a scalar response with a Hilbert moment first column.
-/
noncomputable section
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GeometryOfNumbers.Analysis.FiniteClockJets

/-- Nonvanishing of the explicit completion on the real parameter line. -/
theorem canonicalArchimedeanCompletion_ne_zero (t : ℝ) :
    canonicalArchimedeanCompletion t ≠ 0 := by
  have hs : (baseTwoDressingParameter (t : ℂ)).re = 1/2 := by
    norm_num [baseTwoDressingParameter, Complex.mul_re]
  have hs0 : baseTwoDressingParameter (t : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hs] at this
    norm_num at this
  have hs1 : baseTwoDressingParameter (t : ℂ) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, hs, Complex.one_re, Complex.zero_re] at this
    norm_num at this
  have hg : Complex.Gamma (baseTwoDressingParameter (t : ℂ)/2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num [Complex.div_re, hs]
  unfold canonicalArchimedeanCompletion canonicalArchimedeanCompletionComplex
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1)
    (Complex.exp_ne_zero _)) hg

/-- Concrete scalar action, downstream of any proposed full vector synthesis. -/
def baseTwoCanonicalDressingScalar (t : ℝ) : ℂ :=
  canonicalArchimedeanCompletion t * (baseTwoCanonicalCameraFactor t)⁻¹

theorem baseTwoCanonicalDressingScalar_ne_zero (t : ℝ) :
    baseTwoCanonicalDressingScalar t ≠ 0 :=
  mul_ne_zero (canonicalArchimedeanCompletion_ne_zero t)
    (inv_ne_zero (baseTwoCanonicalCameraFactor_ne_zero t))

theorem baseTwoCanonicalDressingScalar_analyticAt (t : ℝ) :
    AnalyticAt ℝ baseTwoCanonicalDressingScalar t :=
  (canonicalArchimedeanCompletion_analyticAt t).mul
    ((baseTwoCanonicalCameraFactor_analyticAt t).inv (baseTwoCanonicalCameraFactor_ne_zero t))

theorem baseTwoCanonicalResponse_eq_dressing_mul_signal (t : ℝ) :
    baseTwoCanonicalResponse t =
      baseTwoCanonicalDressingScalar t * baseTwoCriticalCompleteSignal t := by
  unfold baseTwoCanonicalResponse baseTwoCanonicalDressingScalar
  ring

section VectorAction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Acts on the original carrier; it neither chooses a state nor a readout. -/
def baseTwoVectorDressing (t : ℝ) : E →L[ℂ] E :=
  baseTwoCanonicalDressingScalar t • ContinuousLinearMap.id ℂ E

@[simp] theorem baseTwoVectorDressing_apply (t : ℝ) (x : E) :
    baseTwoVectorDressing t x = baseTwoCanonicalDressingScalar t • x := rfl

theorem baseTwoVectorDressing_norm (t : ℝ) (x : E) :
    ‖baseTwoVectorDressing t x‖ = ‖baseTwoCanonicalDressingScalar t‖ * ‖x‖ := by
  rw [baseTwoVectorDressing_apply, norm_smul]

theorem baseTwoVectorDressing_injective (t : ℝ) :
    Function.Injective (baseTwoVectorDressing t : E → E) := by
  intro x y h
  have hi := congrArg (fun z : E => (baseTwoCanonicalDressingScalar t)⁻¹ • z) h
  simpa only [baseTwoVectorDressing_apply, smul_smul,
    inv_mul_cancel₀ (baseTwoCanonicalDressingScalar_ne_zero t), one_smul] using hi

/-- Exact residual identity, not an assumed synthesis certificate. -/
theorem baseTwoVectorDressing_readout_residual (ell : E →ₗ[ℂ] ℂ) (x : E) (t : ℝ) :
    ell (baseTwoVectorDressing t x) - baseTwoCanonicalResponse t =
      baseTwoCanonicalDressingScalar t * (ell x - baseTwoCriticalCompleteSignal t) := by
  rw [baseTwoVectorDressing_apply, map_smul,
    baseTwoCanonicalResponse_eq_dressing_mul_signal, smul_eq_mul, mul_sub]

/-- The dressing introduces no additional linear-readout calibration gate. -/
theorem baseTwoVectorDressing_readout_eq_response_iff (ell : E →ₗ[ℂ] ℂ) (x : E) (t : ℝ) :
    ell (baseTwoVectorDressing t x) = baseTwoCanonicalResponse t ↔
      ell x = baseTwoCriticalCompleteSignal t := by
  rw [← sub_eq_zero, baseTwoVectorDressing_readout_residual,
    mul_eq_zero, or_iff_right (baseTwoCanonicalDressingScalar_ne_zero t), sub_eq_zero]

/-- No existence of the full vector synthesis or its readout is asserted. -/
theorem baseTwoVectorDressing_function_readout_iff (ell : E →ₗ[ℂ] ℂ) (x : ℝ → E) :
    (∀ t, ell (baseTwoVectorDressing t (x t)) = baseTwoCanonicalResponse t) ↔
      (∀ t, ell (x t) = baseTwoCriticalCompleteSignal t) := by
  simp only [baseTwoVectorDressing_readout_eq_response_iff]

/-- The product rule exposes the additional scalar connection term. -/
theorem baseTwoVectorDressing_hasDerivAt (x : ℝ → E) (x' : E) (t : ℝ)
    (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => baseTwoVectorDressing s (x s))
      (baseTwoCanonicalDressingScalar t • x' +
        deriv baseTwoCanonicalDressingScalar t • x t) t := by
  exact ((baseTwoCanonicalDressingScalar_analyticAt t).differentiableAt.hasDerivAt.smul hx)

/-- Total linear clock only; no unbounded-domain premise is suppressed. -/
theorem baseTwoVectorDressing_clock_derivative_residual (L : Module.End ℂ E)
    (x : ℝ → E) (t : ℝ) (hx : HasDerivAt x (-Complex.I • L (x t)) t) :
    deriv (fun s => baseTwoVectorDressing s (x s)) t -
      (-Complex.I • L (baseTwoVectorDressing t (x t))) =
        deriv baseTwoCanonicalDressingScalar t • x t := by
  rw [(baseTwoVectorDressing_hasDerivAt x _ t hx).deriv,
    baseTwoVectorDressing_apply, map_smul]
  module

/-- Keeping the same clock requires this exact extra term to vanish. -/
theorem baseTwoVectorDressing_same_clock_iff (L : Module.End ℂ E)
    (x : ℝ → E) (t : ℝ) (hx : HasDerivAt x (-Complex.I • L (x t)) t) :
    deriv (fun s => baseTwoVectorDressing s (x s)) t =
      -Complex.I • L (baseTwoVectorDressing t (x t)) ↔
        deriv baseTwoCanonicalDressingScalar t • x t = 0 := by
  rw [← sub_eq_zero, baseTwoVectorDressing_clock_derivative_residual L x t hx]
end VectorAction

/-- Uses the existing Green carrier, without defining a completed Green state. -/
abbrev baseTwoGreenVectorDressing (t : ℝ) :
    GreenFrame.Concrete.State →L[ℂ] GreenFrame.Concrete.State := baseTwoVectorDressing t

/-- Actual finite vector readout still needs the exact omitted whole-cell tail. -/
theorem baseTwoDressedFiniteOrbit_add_tail (M : ℕ) (t : ℝ) :
    finiteHeadReadout (historicalCameraWeights 2 M)
      (baseTwoVectorDressing t
        (finiteMaterialOrbit (historicalHeadDimension 2 M) t
          (historicalInitialState (historicalHeadDimension 2 M)))) +
      baseTwoCanonicalDressingScalar t * baseTwoCriticalCompleteTail M t =
        baseTwoCanonicalResponse t := by
  rw [baseTwoVectorDressing_apply, map_smul, smul_eq_mul,
    ← mul_add, baseTwoHistoricalReadout_add_completeTail,
    baseTwoCanonicalResponse_eq_dressing_mul_signal]

/-- Dressing commutes with the existing complex-linear Parseval map.
This preserves a missing synthesis/readout calibration; it does not supply it. -/
theorem baseTwoVectorDressing_parseval (t : ℝ) (x : GreenFrame.Concrete.State) :
    GreenParsevalMaterialLog.greenParsevalAnalysis (baseTwoGreenVectorDressing t x) =
      baseTwoVectorDressing t (GreenParsevalMaterialLog.greenParsevalAnalysis x) := by
  simp only [baseTwoGreenVectorDressing, baseTwoVectorDressing_apply, map_smul]

end GeometryOfNumbers.Analysis.BaseTwoCompletion
