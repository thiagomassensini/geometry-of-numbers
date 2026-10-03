import GeometryOfNumbers.Analysis.CenterLegForm

/-!
# Phase canary on the existing local form

This file defines neither a synthesized phase nor a new synthesis. The existing
local form has a rotation orbit. Independently supplied channel angles need not
belong to the common rotation orbit of their zero-angle configuration. R2 scalar
synthesis has no plane-valued phase interface, so these facts do not identify
a post-synthesis evolution.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

theorem rotateRealPlane_neg_comp (theta : ℝ) (v : RealPlaneState) :
    rotateRealPlane (-theta) (rotateRealPlane theta v) = v := by
  rw [← rotateRealPlane_add, neg_add_cancel, rotateRealPlane_zero]

theorem rotateRealPlane_eq_zero_iff (theta : ℝ) (v : RealPlaneState) :
    rotateRealPlane theta v = (0, 0) ↔ v = (0, 0) := by
  constructor
  · intro h
    have hi := rotateRealPlane_neg_comp theta v
    rw [h] at hi
    simpa [rotateRealPlane] using hi.symm
  · intro h
    simp [h, rotateRealPlane]

/-- An orbit identity for the preexisting local vector readout, for every q. -/
theorem centerLegForm_eq_rotate_zero (q theta : ℝ) (v : RealPlaneState) :
    centerLegForm q theta v = rotateRealPlane theta (centerLegForm q 0 v) := by
  rw [centerLegForm_eq_closed, centerLegForm_eq_closed, rotateRealPlane_zero]
  apply Prod.ext <;> simp only [scaleRealPlane, rotateRealPlane] <;> ring

theorem centerLegForm_zero_iff_zero_angle (q theta : ℝ) (v : RealPlaneState) :
    centerLegForm q theta v = (0, 0) ↔ centerLegForm q 0 v = (0, 0) := by
  rw [centerLegForm_eq_rotate_zero]
  exact rotateRealPlane_eq_zero_iff theta _

/-- Two allowed local channels with identical radial data and seeds, but angles
0 and pi, cannot be obtained by a common rotation of their zero-angle states.
This concerns resolved vectors, not their sum of quadratic energies. -/
theorem centerLegForm_independent_angles_not_common_rotation :
    ¬ ∃ theta : ℝ,
      centerLegForm 2 0 (2, 0) = rotateRealPlane theta (centerLegForm 2 0 (2, 0)) ∧
      centerLegForm 2 Real.pi (2, 0) =
        rotateRealPlane theta (centerLegForm 2 0 (2, 0)) := by
  rintro ⟨theta, hzero, hpi⟩
  have hx := congrArg Prod.fst (hzero.trans hpi.symm)
  norm_num [centerLegForm_eq_closed, scaleRealPlane, rotateRealPlane] at hx

end

end GeometryOfNumbers.Analysis
