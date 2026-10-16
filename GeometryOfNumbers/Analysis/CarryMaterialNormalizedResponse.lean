import GeometryOfNumbers.Analysis.CarryMaterialCentralCalibration
import GeometryOfNumbers.Analysis.CompletedBoundaryTransportedClock

/-! The material response is read only after constructing the full dressed
companion on the EXISTING clock graph domain. The seed, gradient and global
return remain in the carrier. The quotient below is a nonlinear readout, not
an isometry or a replacement metric. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Minus the derivative of the dressed source, constructed before readout.
The clock is used only on its proved graph domain. -/
def carryMaterialDressedCompanion (t : ℝ) :
    completedBoundaryTransportedClock.domain →ₗ[ℂ] BaseTwoCompletedBoundaryHilbertCarrier :=
  -(baseTwoCanonicalDressingScalar t • (-Complex.I • completedBoundaryTransportedClock.toFun) +
    deriv baseTwoCanonicalDressingScalar t • completedBoundaryTransportedClock.domain.subtype)

theorem carryMaterialDressedCompanion_apply (t : ℝ)
    (y : completedBoundaryTransportedClock.domain) :
    carryMaterialDressedCompanion t y =
      -(baseTwoCanonicalDressingScalar t • (-Complex.I • completedBoundaryTransportedClock y) +
        deriv baseTwoCanonicalDressingScalar t • y.val) := rfl

theorem carryMaterialDressedSource_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u => baseTwoVectorDressing u (baseTwoCompletedBoundaryHilbertState u))
      (-carryMaterialDressedCompanion t
        ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩) t := by
  simpa only [carryMaterialDressedCompanion_apply, neg_neg] using
    baseTwoVectorDressing_hasDerivAt baseTwoCompletedBoundaryHilbertState _ t
      (completedBoundaryState_hasDerivAt_clock t)

/-- The actual clock output readout is its global clocked cell return. -/
theorem carryMaterialClock_readout (y : completedBoundaryTransportedClock.domain) :
    baseTwoCompletedBoundaryHilbertReadout (completedBoundaryTransportedClock y) =
      baseTwoCompletedBoundaryClockReturn y.val := by
  rw [baseTwoCompletedBoundaryHilbertReadout_apply, completedBoundaryTransportedClock_seed,
    completedBoundaryTransportedClock_boundary, zero_add]

theorem carryMaterialDressedCompanion_readout (t : ℝ)
    (y : completedBoundaryTransportedClock.domain) :
    baseTwoCompletedBoundaryHilbertReadout (carryMaterialDressedCompanion t y) =
      Complex.I * baseTwoCanonicalDressingScalar t * baseTwoCompletedBoundaryClockReturn y.val -
        deriv baseTwoCanonicalDressingScalar t * baseTwoCompletedBoundaryHilbertReadout y.val := by
  simp only [carryMaterialDressedCompanion_apply, map_neg, map_add, map_smul,
    smul_eq_mul, carryMaterialClock_readout]
  ring

theorem carryMaterialDressedReadout_hasDerivAt (t : ℝ) :
    HasDerivAt baseTwoCanonicalResponse
      (-baseTwoCompletedBoundaryHilbertReadout (carryMaterialDressedCompanion t
        ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩)) t := by
  have h := (baseTwoCompletedBoundaryHilbertReadout.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (carryMaterialDressedSource_hasDerivAt t)
  have he : (fun u => baseTwoCompletedBoundaryHilbertReadout
      (baseTwoVectorDressing u (baseTwoCompletedBoundaryHilbertState u))) = baseTwoCanonicalResponse := by
    funext u
    exact carryMaterial_dressed_completed_readout u
  change HasDerivAt (fun u => baseTwoCompletedBoundaryHilbertReadout
      (baseTwoVectorDressing u (baseTwoCompletedBoundaryHilbertState u)))
      (baseTwoCompletedBoundaryHilbertReadout (-carryMaterialDressedCompanion t
        ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩)) t at h
  simpa only [he, map_neg] using h

theorem carryMaterialDressedCompanion_source_readout (t : ℝ) :
    baseTwoCompletedBoundaryHilbertReadout (carryMaterialDressedCompanion t
      ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩) =
      -deriv baseTwoCanonicalResponse t := by
  rw [(carryMaterialDressedReadout_hasDerivAt t).deriv, neg_neg]

/-- A typed readout of the value/companion of the same graph-domain input.
Linearity of the companion does not imply linearity of this quotient. -/
def carryMaterialResponseReadout (t : ℝ) (y : completedBoundaryTransportedClock.domain) : ℂ :=
  baseTwoCompletedBoundaryHilbertReadout (carryMaterialDressedCompanion t y) /
    (2 * baseTwoCompletedBoundaryHilbertReadout (baseTwoVectorDressing t y.val))

def carryMaterialNormalizedResponse (t : ℝ) : ℂ :=
  carryMaterialResponseReadout t
    ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩

theorem carryMaterialNormalizedResponse_eq (t : ℝ) :
    carryMaterialNormalizedResponse t =
      -deriv baseTwoCanonicalResponse t / (2 * baseTwoCanonicalResponse t) := by
  rw [carryMaterialNormalizedResponse, carryMaterialResponseReadout,
    carryMaterialDressedCompanion_source_readout, carryMaterial_dressed_completed_readout]

theorem carryMaterialNormalizedResponse_connection (t : ℝ)
    (hs : baseTwoCriticalCompleteSignal t ≠ 0) :
    carryMaterialNormalizedResponse t =
      Complex.I * baseTwoCompletedBoundaryClockReturn (baseTwoCompletedBoundaryHilbertState t) /
        (2 * baseTwoCriticalCompleteSignal t) -
      deriv baseTwoCanonicalDressingScalar t / (2 * baseTwoCanonicalDressingScalar t) := by
  rw [carryMaterialNormalizedResponse, carryMaterialResponseReadout,
    carryMaterialDressedCompanion_readout, baseTwoCompletedBoundaryHilbertReadout_eq_signal,
    carryMaterial_dressed_completed_readout, baseTwoCanonicalResponse_eq_dressing_mul_signal]
  have hd := baseTwoCanonicalDressingScalar_ne_zero t
  field_simp

/-- Removable divided response on the REAL parameter; its value at zero is
its real-parameter derivative, not an assumed holomorphic jet of the state. -/
def carryMaterialResponseAxis : ℝ → ℂ := dslope carryMaterialNormalizedResponse 0

def carryMaterialResponseScale : ℝ := (carryMaterialResponseAxis 0).re

def carryMaterialPositiveFeature (t : ℝ) : ℂ :=
  carryMaterialResponseAxis t / (Real.sqrt carryMaterialResponseScale : ℂ)

end
end GeometryOfNumbers.Analysis
