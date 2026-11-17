import GeometryOfNumbers.Analysis.CarryMaterialComplexCauchySource
import GeometryOfNumbers.Analysis.CarryMaterialNormalizedResponse
import Mathlib.Tactic

/-!
# Completed physical source and its true complex derivative

No target xi or Pick kernel appears in the definitions. The completed source
is the old C2 material profile dressed by exactly the old camera/Archimedean
factor, now at complex height. Its boundary companion is the derivative of
the FULL Hilbert vector, before any scalar readout.
-/

namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open scoped InnerProductSpace ComplexConjugate

noncomputable section
set_option autoImplicit false

def carryMaterialComplexDressingScalar (z : ℂ) : ℂ :=
  canonicalArchimedeanCompletionComplex z *
    (baseTwoCanonicalCameraFactorComplex z)⁻¹

/-- Unchanged material seed, edges and return, dressed on the whole Hilbert
carrier; no moment fit or completion inferred from scalar readouts. -/
def carryMaterialComplexDressedState (z : ℂ) : MaterialCarrier :=
  carryMaterialComplexDressingScalar z • carryMaterialComplexState z

/-- Genuine full-vector derivative is taken before projecting to a scalar. -/
def carryMaterialComplexCompanion (z : ℂ) : MaterialCarrier :=
  -deriv carryMaterialComplexDressedState z

def carryMaterialComplexValueReadout (z : ℂ) : ℂ :=
  baseTwoCompletedBoundaryHilbertReadout (carryMaterialComplexDressedState z)

def carryMaterialComplexCompanionReadout (z : ℂ) : ℂ :=
  baseTwoCompletedBoundaryHilbertReadout (carryMaterialComplexCompanion z)

/-- Completed physical projective value/companion, not a target kernel. -/
def carryMaterialComplexCompanionValuePair (z : ℂ) :
    MaterialCarrier × MaterialCarrier :=
  (carryMaterialComplexCompanion z,
    (2 : ℂ) • carryMaterialComplexDressedState z)

theorem carryMaterialComplexDressingScalar_ofReal (t : ℝ) :
    carryMaterialComplexDressingScalar (t : ℂ) =
      baseTwoCanonicalDressingScalar t := rfl

theorem carryMaterialComplexDressedState_ofReal (t : ℝ) :
    carryMaterialComplexDressedState (t : ℂ) =
      baseTwoVectorDressing t (baseTwoCompletedBoundaryHilbertState t) := by
  rw [carryMaterialComplexDressedState, carryMaterialComplexDressingScalar_ofReal,
    carryMaterialComplexState_ofReal]
  rfl

theorem carryMaterialComplexValueReadout_ofReal (t : ℝ) :
    carryMaterialComplexValueReadout (t : ℂ) =
      baseTwoCanonicalResponse t := by
  rw [carryMaterialComplexValueReadout, carryMaterialComplexDressedState_ofReal]
  exact carryMaterial_dressed_completed_readout t

theorem carryMaterialComplexDressingScalar_differentiableAt_ofReal (t : ℝ) :
    DifferentiableAt ℂ carryMaterialComplexDressingScalar (t : ℂ) := by
  have hA : DifferentiableAt ℂ canonicalArchimedeanCompletionComplex (t : ℂ) :=
    (canonicalArchimedeanCompletionComplex_differentiableOn_ball t).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have hQ : DifferentiableAt ℂ baseTwoCanonicalCameraFactorComplex (t : ℂ) :=
    baseTwoCanonicalCameraFactorComplex_differentiable (t : ℂ)
  have hQne : baseTwoCanonicalCameraFactorComplex (t : ℂ) ≠ 0 :=
    baseTwoCanonicalCameraFactor_ne_zero t
  exact hA.mul (hQ.inv hQne)

theorem carryMaterialComplexDressedState_differentiableAt_ofReal (t : ℝ) :
    DifferentiableAt ℂ carryMaterialComplexDressedState (t : ℂ) := by
  exact (carryMaterialComplexDressingScalar_differentiableAt_ofReal t).smul
    (carryMaterialComplexState_differentiableAt_ofReal t)

/-- The complex derivative restricts exactly to the old real-time clock
companion, not merely to the same scalar boundary. -/
theorem carryMaterialComplexCompanion_ofReal (t : ℝ) :
    carryMaterialComplexCompanion (t : ℂ) =
      carryMaterialDressedCompanion t
        ⟨baseTwoCompletedBoundaryHilbertState t,
          baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩ := by
  have hcomplex : HasDerivAt carryMaterialComplexDressedState
      (deriv carryMaterialComplexDressedState (t : ℂ)) (t : ℂ) :=
    (carryMaterialComplexDressedState_differentiableAt_ofReal t).hasDerivAt
  have hreal0 := (hcomplex.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    t Complex.ofRealCLM.hasDerivAt
  have heq : (fun x : ℝ => carryMaterialComplexDressedState (x : ℂ)) =
      (fun x : ℝ =>
         baseTwoVectorDressing x (baseTwoCompletedBoundaryHilbertState x)) := by
    funext x
    exact carryMaterialComplexDressedState_ofReal x
  change HasDerivAt (fun x : ℝ =>
      carryMaterialComplexDressedState (x : ℂ)) _ t at hreal0
  rw [heq] at hreal0
  have hd := hreal0.unique (carryMaterialDressedSource_hasDerivAt t)
  unfold carryMaterialComplexCompanion
  change (1 : ℂ) • deriv carryMaterialComplexDressedState (t : ℂ) = _ at hd
  have h := congrArg Neg.neg hd
  simpa only [one_smul, neg_neg] using h

theorem carryMaterialComplexCompanionValuePair_ofReal (t : ℝ) :
    carryMaterialComplexCompanionValuePair (t : ℂ) =
      carryMaterialCompanionValuePair t := by
  simp [carryMaterialComplexCompanionValuePair, carryMaterialCompanionValuePair,
    carryMaterialComplexCompanion_ofReal, carryMaterialComplexDressedState_ofReal]

/-- The companion readout remains -F' wherever the vector has a complex
derivative, by boundedness of the ORIGINAL readout. -/
theorem carryMaterialComplexCompanionReadout_eq_neg_deriv (z : ℂ)
    (hz : DifferentiableAt ℂ carryMaterialComplexDressedState z) :
    carryMaterialComplexCompanionReadout z =
      -deriv carryMaterialComplexValueReadout z := by
  have hcomp := baseTwoCompletedBoundaryHilbertReadout.hasFDerivAt.comp_hasDerivAt
    z hz.hasDerivAt
  have hd : deriv carryMaterialComplexValueReadout z =
      baseTwoCompletedBoundaryHilbertReadout (deriv carryMaterialComplexDressedState z) := by
    exact hcomp.deriv
  change baseTwoCompletedBoundaryHilbertReadout
      (-deriv carryMaterialComplexDressedState z) =
        -deriv carryMaterialComplexValueReadout z
  rw [map_neg, hd]

end
end GeometryOfNumbers.Analysis

#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexCompanion_ofReal
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexCompanionReadout_eq_neg_deriv
