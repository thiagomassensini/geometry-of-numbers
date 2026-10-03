import GeometryOfNumbers.Analysis.RealCarryTfvd
import GeometryOfNumbers.Analysis.CenterLegForm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Exact real dynamics of a growing C2 fiber

Reference: C2FiberDepthLogTransport, carry-self-adjoint-operator,
cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa. Only its coordinate/log identities
are rewritten here. The real amplitude, rotation and residual-depth relation
are preexisting local objects. No historical source or operator is imported.

m is fixed core, k is vertical depth, and epsilon is a signed material offset.
Odd core gives exact intrinsic center depth; without oddness k is a supported
level. Physical logarithmic states require positive core and material point.
The algebraic family also covers offsets other than the C2 legs ±1.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

def c2FiberPoint (m : ℕ) (epsilon : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * m + epsilon

theorem c2FiberPoint_centered (m k : ℕ) (epsilon : ℝ) :
    c2FiberPoint m epsilon k - epsilon = (2 : ℝ) ^ k * m := by
  simp [c2FiberPoint]

theorem c2FiberPoint_center_eq_nat (m k : ℕ) :
    c2FiberPoint m 0 k = ((2 ^ k * m : ℕ) : ℝ) := by
  simp [c2FiberPoint]

theorem c2FiberPoint_succ (m k : ℕ) (epsilon : ℝ) :
    c2FiberPoint m epsilon (k + 1) = 2 * c2FiberPoint m epsilon k - epsilon := by
  simp only [c2FiberPoint, pow_succ]
  ring

theorem c2FiberCenter_hasCarryDepthAtLeast (m k : ℕ) :
    Geometry.HasCarryDepthAtLeast 2 (2 ^ k * m) k := by
  rw [Geometry.hasCarryDepthAtLeast_iff_dvd_pow 2 _ _ (by decide)]
  exact dvd_mul_right _ _

theorem c2FiberCenter_not_hasCarryDepthAtLeast_succ (m k : ℕ) (hm : Odd m) :
    ¬ Geometry.HasCarryDepthAtLeast 2 (2 ^ k * m) (k + 1) := by
  rw [Geometry.hasCarryDepthAtLeast_iff_dvd_pow 2 _ _ (by decide), pow_succ,
    Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ k)]
  rintro ⟨z, hz⟩
  rcases hm with ⟨r, hr⟩
  omega

theorem c2FiberPoint_center_pos (m k : ℕ) (hm : 0 < m) :
    0 < c2FiberPoint m 0 k := by
  simp only [c2FiberPoint, add_zero]
  positivity

theorem c2FiberPoint_right_pos (m k : ℕ) (hm : 0 < m) :
    0 < c2FiberPoint m 1 k := by
  unfold c2FiberPoint
  positivity

theorem c2FiberPoint_left_pos (m k : ℕ) (hm : 0 < m) (hk : 1 ≤ k) :
    0 < c2FiberPoint m (-1) k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hprod : (1 : ℝ) ≤ (2 : ℝ) ^ r * m := by
    exact_mod_cast (Nat.succ_le_iff.mpr (by positivity : 0 < 2 ^ r * m))
  simp only [c2FiberPoint, pow_succ]
  nlinarith

theorem c2FiberPoint_centered_log (m k : ℕ) (hm : 0 < m) (epsilon : ℝ) :
    Real.log (c2FiberPoint m epsilon k - epsilon) =
      (k : ℝ) * Real.log 2 + Real.log m := by
  rw [c2FiberPoint_centered, Real.log_mul (by positivity) (by positivity),
    Real.log_pow]

theorem c2FiberPoint_centered_log_increment
    (m k : ℕ) (hm : 0 < m) (epsilon : ℝ) :
    Real.log (c2FiberPoint m epsilon (k + 1) - epsilon) -
      Real.log (c2FiberPoint m epsilon k - epsilon) = Real.log 2 := by
  rw [c2FiberPoint_centered_log m (k + 1) hm, c2FiberPoint_centered_log m k hm]
  push_cast
  ring

def c2FiberLogDefect (m : ℕ) (epsilon : ℝ) (k : ℕ) : ℝ :=
  Real.log (1 + epsilon / ((2 : ℝ) ^ k * m))

theorem c2FiberLogDefect_center (m k : ℕ) :
    c2FiberLogDefect m 0 k = 0 := by
  simp [c2FiberLogDefect]

theorem c2FiberPoint_log_center_defect (m k : ℕ) (hm : 0 < m)
    (epsilon : ℝ) (hx : 0 < c2FiberPoint m epsilon k) :
    Real.log (c2FiberPoint m epsilon k) -
      Real.log (c2FiberPoint m epsilon k - epsilon) = c2FiberLogDefect m epsilon k := by
  rw [c2FiberPoint_centered, ← Real.log_div hx.ne' (by positivity)]
  unfold c2FiberLogDefect
  congr 1
  unfold c2FiberPoint
  field_simp

theorem c2FiberPoint_log_eq_depth_core_defect (m k : ℕ) (hm : 0 < m)
    (epsilon : ℝ) (hx : 0 < c2FiberPoint m epsilon k) :
    Real.log (c2FiberPoint m epsilon k) =
      (k : ℝ) * Real.log 2 + Real.log m + c2FiberLogDefect m epsilon k := by
  have h := c2FiberPoint_log_center_defect m k hm epsilon hx
  rw [c2FiberPoint_centered_log m k hm] at h
  linarith

theorem c2FiberPoint_log_increment_defect (m k : ℕ) (hm : 0 < m)
    (epsilon : ℝ) (hx : 0 < c2FiberPoint m epsilon k)
    (hy : 0 < c2FiberPoint m epsilon (k + 1)) :
    Real.log (c2FiberPoint m epsilon (k + 1)) - Real.log (c2FiberPoint m epsilon k) =
      Real.log 2 + c2FiberLogDefect m epsilon (k + 1) - c2FiberLogDefect m epsilon k := by
  rw [c2FiberPoint_log_eq_depth_core_defect m (k + 1) hm epsilon hy,
    c2FiberPoint_log_eq_depth_core_defect m k hm epsilon hx]
  push_cast
  ring

theorem c2FiberLogDefect_right_pos (m k : ℕ) (hm : 0 < m) :
    0 < c2FiberLogDefect m 1 k := by
  apply Real.log_pos
  have hp : 0 < (1 : ℝ) / ((2 : ℝ) ^ k * m) := by positivity
  linarith

/-- An exact example preventing replacement of the leg log increment by log 2. -/
theorem c2FiberPoint_right_log_increment_lt :
    Real.log (c2FiberPoint 1 1 3) - Real.log (c2FiberPoint 1 1 2) < Real.log 2 := by
  norm_num [c2FiberPoint]
  rw [← Real.log_div (by norm_num : (9 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
  apply Real.log_lt_log <;> norm_num

/-- The depth fixes amplitude; the positive fiber point fixes the phase clock. -/
def c2FiberRealState (m : ℕ) (epsilon t : ℝ) (k : ℕ)
    (_hm : 0 < m) (_hx : 0 < c2FiberPoint m epsilon k) : RealPlaneState :=
  realCriticalDepthState 2 k (by decide) (-t * Real.log (c2FiberPoint m epsilon k))

theorem c2FiberRealState_energy (m : ℕ) (epsilon t : ℝ) (k : ℕ)
    (hm : 0 < m) (hx : 0 < c2FiberPoint m epsilon k) :
    realPlaneEnergy (c2FiberRealState m epsilon t k hm hx) = realDepthMass 2 k (by decide) :=
  realCriticalDepthState_energy 2 k _ _

private theorem rotate_scale (theta a : ℝ) (v : RealPlaneState) :
    rotateRealPlane theta (scaleRealPlane a v) = scaleRealPlane a (rotateRealPlane theta v) := by
  apply Prod.ext <;> simp only [rotateRealPlane, scaleRealPlane] <;> ring

private theorem criticalState_succ_angle (k : ℕ) (theta omega : ℝ) :
    realCriticalDepthState 2 (k + 1) (by decide) (omega + theta) =
      scaleRealPlane (criticalVerticalAmplitudeRatio 2 (by decide))
        (rotateRealPlane omega (realCriticalDepthState 2 k (by decide) theta)) := by
  have hs : realCriticalDepthSeed 2 (k + 1) (by decide) =
      scaleRealPlane (criticalVerticalAmplitudeRatio 2 (by decide))
        (realCriticalDepthSeed 2 k (by decide)) := by
    apply Prod.ext
    · simp only [realCriticalDepthSeed, scaleRealPlane, realCriticalAmplitude_succ_verticalRatio]
      ring
    · simp [realCriticalDepthSeed, scaleRealPlane]
  unfold realCriticalDepthState
  rw [hs, rotate_scale, rotateRealPlane_add]

theorem c2FiberRealState_succ_eq_logIncrement (m : ℕ) (epsilon t : ℝ) (k : ℕ)
    (hm : 0 < m) (hx : 0 < c2FiberPoint m epsilon k)
    (hy : 0 < c2FiberPoint m epsilon (k + 1)) :
    c2FiberRealState m epsilon t (k + 1) hm hy =
      scaleRealPlane (criticalVerticalAmplitudeRatio 2 (by decide))
        (rotateRealPlane (-t * (Real.log (c2FiberPoint m epsilon (k + 1)) -
          Real.log (c2FiberPoint m epsilon k))) (c2FiberRealState m epsilon t k hm hx)) := by
  have ha : -t * Real.log (c2FiberPoint m epsilon (k + 1)) =
      -t * (Real.log (c2FiberPoint m epsilon (k + 1)) -
        Real.log (c2FiberPoint m epsilon k)) + -t * Real.log (c2FiberPoint m epsilon k) := by
    ring
  unfold c2FiberRealState
  rw [ha]
  exact criticalState_succ_angle _ _ _

def c2CenterFiberStep (t : ℝ) (v : RealPlaneState) : RealPlaneState :=
  scaleRealPlane (criticalVerticalAmplitudeRatio 2 (by decide))
    (rotateRealPlane (-t * Real.log 2) v)

theorem c2CenterFiberRealState_succ_eq_fixedStep (m : ℕ) (t : ℝ) (k : ℕ) (hm : 0 < m) :
    c2FiberRealState m 0 t (k + 1) hm (c2FiberPoint_center_pos m (k + 1) hm) =
      c2CenterFiberStep t (c2FiberRealState m 0 t k hm (c2FiberPoint_center_pos m k hm)) := by
  have hc : Real.log (c2FiberPoint m 0 (k + 1)) - Real.log (c2FiberPoint m 0 k) =
      Real.log 2 := by
    simpa using c2FiberPoint_centered_log_increment m k hm 0
  simpa [c2CenterFiberStep, hc] using c2FiberRealState_succ_eq_logIncrement m 0 t k hm
    (c2FiberPoint_center_pos m k hm) (c2FiberPoint_center_pos m (k + 1) hm)

theorem c2CenterFiberRealState_eq_iterate_step (m : ℕ) (t : ℝ) (hm : 0 < m) (k : ℕ) :
    c2FiberRealState m 0 t k hm (c2FiberPoint_center_pos m k hm) =
      (c2CenterFiberStep t)^[k]
        (c2FiberRealState m 0 t 0 hm (c2FiberPoint_center_pos m 0 hm)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [c2CenterFiberRealState_succ_eq_fixedStep, ih, Function.iterate_succ_apply']

theorem c2CenterFiber_phase_factorization (m k : ℕ) (hm : 0 < m) (t : ℝ) (v : RealPlaneState) :
    rotateRealPlane (-t * Real.log (c2FiberPoint m 0 k)) v =
      rotateRealPlane (-t * (k : ℝ) * Real.log 2) (rotateRealPlane (-t * Real.log m) v) := by
  have hc : Real.log (c2FiberPoint m 0 k) = (k : ℝ) * Real.log 2 + Real.log m := by
    simpa using c2FiberPoint_centered_log m k hm 0
  rw [hc]
  have ha : -t * ((k : ℝ) * Real.log 2 + Real.log m) =
      -t * (k : ℝ) * Real.log 2 + -t * Real.log m := by ring
  rw [ha, rotateRealPlane_add]

theorem c2LegFiberRealState_succ_eq_correctedStep (m : ℕ) (epsilon t : ℝ) (k : ℕ)
    (hm : 0 < m) (hx : 0 < c2FiberPoint m epsilon k)
    (hy : 0 < c2FiberPoint m epsilon (k + 1)) :
    c2FiberRealState m epsilon t (k + 1) hm hy =
      scaleRealPlane (criticalVerticalAmplitudeRatio 2 (by decide))
        (rotateRealPlane (-t * (Real.log 2 + c2FiberLogDefect m epsilon (k + 1) -
          c2FiberLogDefect m epsilon k)) (c2FiberRealState m epsilon t k hm hx)) := by
  rw [c2FiberRealState_succ_eq_logIncrement m epsilon t k hm hx hy,
    c2FiberPoint_log_increment_defect m k hm epsilon hx hy]

/-- "add_logDefect" means composition of rotations, not addition of states. -/
theorem c2LegFiberRealState_succ_eq_fixedStep_add_logDefect
    (m : ℕ) (epsilon t : ℝ) (k : ℕ) (hm : 0 < m)
    (hx : 0 < c2FiberPoint m epsilon k) (hy : 0 < c2FiberPoint m epsilon (k + 1)) :
    c2FiberRealState m epsilon t (k + 1) hm hy =
      rotateRealPlane (-t * (c2FiberLogDefect m epsilon (k + 1) - c2FiberLogDefect m epsilon k))
        (c2CenterFiberStep t (c2FiberRealState m epsilon t k hm hx)) := by
  rw [c2LegFiberRealState_succ_eq_correctedStep m epsilon t k hm hx hy,
    c2CenterFiberStep, rotate_scale,
    ← rotateRealPlane_add]
  congr 2
  ring

end

end GeometryOfNumbers.Analysis
