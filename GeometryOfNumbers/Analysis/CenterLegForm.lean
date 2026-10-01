import GeometryOfNumbers.Analysis.QuadraticCenteredBracket

/-!
# A coordinate center-leg form on the existing real plane

All three positions share the same freely rotated state. The vector readout
is constructed from these positions before deriving either factorization or
energy. Scaling is coordinate multiplication, and energy remains `x² + y²`.
Angular independence follows from the existing rotation-energy theorem.
The reciprocal factorization requires a nonzero radial parameter; its zero
criterion also requires a state with positive energy. No parameter is selected.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

def scaleRealPlane (a : ℝ) (v : RealPlaneState) : RealPlaneState :=
  (a * v.1, a * v.2)

/-- The existing scalar readout, applied to each coordinate. -/
def realPlaneCenteredReadout (left center right : RealPlaneState) : RealPlaneState :=
  (realCenteredReadout left.1 center.1 right.1,
    realCenteredReadout left.2 center.2 right.2)

def centerLegFormLeftLeg (q theta : ℝ) (v : RealPlaneState) : RealPlaneState :=
  scaleRealPlane q (rotateRealPlane theta v)

def centerLegFormRightLeg (q theta : ℝ) (v : RealPlaneState) : RealPlaneState :=
  scaleRealPlane (reciprocalReflection q) (rotateRealPlane theta v)

/-- The center is the same rotated state used by both constructed legs. -/
def centerLegForm (q theta : ℝ) (v : RealPlaneState) : RealPlaneState :=
  realPlaneCenteredReadout (centerLegFormLeftLeg q theta v)
    (rotateRealPlane theta v) (centerLegFormRightLeg q theta v)

theorem centerLegForm_eq_closed (q theta : ℝ) (v : RealPlaneState) :
    centerLegForm q theta v = scaleRealPlane (q + q⁻¹ - 2) (rotateRealPlane theta v) := by
  apply Prod.ext <;>
    simp only [centerLegForm, realPlaneCenteredReadout, centerLegFormLeftLeg,
      centerLegFormRightLeg, scaleRealPlane, realCenteredReadout, reciprocalReflection] <;>
    ring

theorem centerLegForm_eq_factor (q theta : ℝ) (v : RealPlaneState) (hq : q ≠ 0) :
    centerLegForm q theta v =
      scaleRealPlane ((q - 1) ^ 2 / q) (rotateRealPlane theta v) := by
  have hfactor : q + q⁻¹ - 2 = (q - 1) ^ 2 / q := by
    simpa only [one_mul, div_eq_mul_inv] using
      (quadraticCenteredBracket_eq_closed 1 q).symm.trans
        (quadraticCenteredBracket_eq_factor 1 q hq)
  rw [centerLegForm_eq_closed, hfactor]

theorem scaleRealPlane_energy (a : ℝ) (v : RealPlaneState) :
    realPlaneEnergy (scaleRealPlane a v) = a ^ 2 * realPlaneEnergy v := by
  unfold realPlaneEnergy scaleRealPlane
  ring

theorem centerLegForm_energy_eq_closed (q theta : ℝ) (v : RealPlaneState) :
    realPlaneEnergy (centerLegForm q theta v) =
      (q + q⁻¹ - 2) ^ 2 * realPlaneEnergy v := by
  rw [centerLegForm_eq_closed, scaleRealPlane_energy, rotateRealPlane_energy]

theorem centerLegForm_energy_eq_factor (q theta : ℝ) (v : RealPlaneState) (hq : q ≠ 0) :
    realPlaneEnergy (centerLegForm q theta v) =
      ((q - 1) ^ 2 / q) ^ 2 * realPlaneEnergy v := by
  rw [centerLegForm_eq_factor q theta v hq, scaleRealPlane_energy, rotateRealPlane_energy]

theorem centerLegForm_energy_eq_fourth (q theta : ℝ) (v : RealPlaneState) (hq : q ≠ 0) :
    realPlaneEnergy (centerLegForm q theta v) =
      ((q - 1) ^ 4 / q ^ 2) * realPlaneEnergy v := by
  rw [centerLegForm_energy_eq_factor q theta v hq, div_pow, ← pow_mul]

/-- Angular independence even holds for the total-inverse readout at zero;
the quotient factorization above deliberately excludes that parameter. -/
theorem centerLegForm_energy_angle_independent (q theta₁ theta₂ : ℝ) (v : RealPlaneState) :
    realPlaneEnergy (centerLegForm q theta₁ v) =
      realPlaneEnergy (centerLegForm q theta₂ v) := by
  rw [centerLegForm_energy_eq_closed, centerLegForm_energy_eq_closed]

theorem centerLegForm_energy_zero_iff (q theta : ℝ) (v : RealPlaneState)
    (hq : 0 < q) (hv : 0 < realPlaneEnergy v) :
    realPlaneEnergy (centerLegForm q theta v) = 0 ↔ q = 1 := by
  rw [centerLegForm_energy_eq_factor q theta v (ne_of_gt hq)]
  constructor
  · intro hz
    have hsquare := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hv)
    have hquotient := sq_eq_zero_iff.mp hsquare
    have hnumerator := (div_eq_zero_iff.mp hquotient).resolve_right (ne_of_gt hq)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hnumerator)
  · intro h
    simp [h]

/-- Seed specialization: the common rotation is exactly the existing depth state. -/
theorem centerLegForm_criticalSeed_eq_factor (b k : Nat) (hb : 0 < b)
    (q theta : ℝ) (hq : q ≠ 0) :
    centerLegForm q theta (realCriticalDepthSeed b k hb) =
      scaleRealPlane ((q - 1) ^ 2 / q) (realCriticalDepthState b k hb theta) :=
  centerLegForm_eq_factor q theta _ hq

theorem centerLegForm_criticalSeed_energy_eq_amplitude_sq (b k : Nat) (hb : 0 < b)
    (q theta : ℝ) (hq : q ≠ 0) :
    realPlaneEnergy (centerLegForm q theta (realCriticalDepthSeed b k hb)) =
      ((q - 1) ^ 4 / q ^ 2) * realCriticalAmplitude b k hb ^ 2 := by
  rw [centerLegForm_energy_eq_fourth q theta _ hq,
    realCriticalDepthSeed_energy_eq_amplitude_sq]

theorem centerLegForm_criticalSeed_energy_eq_mass (b k : Nat) (hb : 0 < b)
    (q theta : ℝ) (hq : q ≠ 0) :
    realPlaneEnergy (centerLegForm q theta (realCriticalDepthSeed b k hb)) =
      ((q - 1) ^ 4 / q ^ 2) * realDepthMass b k hb := by
  rw [centerLegForm_criticalSeed_energy_eq_amplitude_sq b k hb q theta hq,
    realCriticalAmplitude_sq_eq_realDepthMass]

end

end GeometryOfNumbers.Analysis
