import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# An explicit quadratic plane and abstract angular rotation

Energy is the coordinate polynomial `x² + y²`, not a norm supplied by a
normed-space instance. Positive angles use the usual orientation sending
`(1,0)` to `(cos theta, sin theta)`. The angle is a free geometric parameter;
no law selecting it, or other interpretation of it, is introduced here.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

abbrev RealPlaneState := ℝ × ℝ

def realPlaneEnergy (state : RealPlaneState) : ℝ :=
  state.1 ^ 2 + state.2 ^ 2

def rotateRealPlane (theta : ℝ) (state : RealPlaneState) : RealPlaneState :=
  (state.1 * Real.cos theta - state.2 * Real.sin theta,
    state.1 * Real.sin theta + state.2 * Real.cos theta)

theorem rotateRealPlane_energy (theta : ℝ) (state : RealPlaneState) :
    realPlaneEnergy (rotateRealPlane theta state) = realPlaneEnergy state := by
  calc
    realPlaneEnergy (rotateRealPlane theta state) =
        (state.1 ^ 2 + state.2 ^ 2) *
          (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by
      unfold realPlaneEnergy rotateRealPlane
      ring
    _ = realPlaneEnergy state := by
      rw [Real.sin_sq_add_cos_sq, mul_one]
      rfl

theorem rotateRealPlane_zero (state : RealPlaneState) :
    rotateRealPlane 0 state = state := by
  apply Prod.ext <;> simp [rotateRealPlane]

theorem rotateRealPlane_add (theta phi : ℝ) (state : RealPlaneState) :
    rotateRealPlane (theta + phi) state =
      rotateRealPlane theta (rotateRealPlane phi state) := by
  apply Prod.ext <;> simp only [rotateRealPlane, Real.cos_add, Real.sin_add] <;> ring

end

end GeometryOfNumbers.Analysis
