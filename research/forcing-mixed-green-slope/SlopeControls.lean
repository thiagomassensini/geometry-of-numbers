import ForcingSlope

/-! Synthetic logical controls, NOT statements about the sign of the
canonical source. Matching a positive first jet cannot supply a Gram. -/
namespace CarryMixedGreen
open Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def controlResponse (C t : ℝ) : ℝ := C*t-t^3
def controlLoewner (C t u : ℝ) : ℝ := C-(t^2+t*u+u^2)

theorem control_regular (C t u : ℝ) (hne : u ≠ t) :
    (controlResponse C u-controlResponse C t)/(u-t) = controlLoewner C t u := by
  unfold controlResponse controlLoewner
  field_simp
  ring

theorem control_response_derivative (C t : ℝ) :
    HasDerivAt (controlResponse C) (C-3*t^2) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hc : Continuous (fun u : ℝ => controlLoewner C t u) := by
    unfold controlLoewner
    fun_prop
  have he : controlLoewner C t t = C-3*t^2 := by unfold controlLoewner; ring
  have h := (hc.tendsto t).mono_left (nhdsWithin_le_nhds (s := ({t}ᶜ : Set ℝ)))
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [slope_def_field]
  exact (control_regular C t u (by simpa using hu)).symm

theorem control_same_native_first_jet :
    controlResponse (2*‖GeometryOfNumbers.Analysis.carryMaterialClockCentralForcing‖^2) 0 = 0 ∧
    HasDerivAt (controlResponse (2*‖GeometryOfNumbers.Analysis.carryMaterialClockCentralForcing‖^2))
      (2*‖GeometryOfNumbers.Analysis.carryMaterialClockCentralForcing‖^2) 0 := by
  constructor
  · simp [controlResponse]
  · simpa using control_response_derivative
      (2*‖GeometryOfNumbers.Analysis.carryMaterialClockCentralForcing‖^2) 0

/-- Both diagonal slopes may be positive and the polarized form negative. -/
theorem control_quadratic (C s : ℝ) :
    controlLoewner C 0 0 - controlLoewner C 0 s - controlLoewner C s 0 +
      controlLoewner C s s = -s^2 := by
  unfold controlLoewner
  ring

theorem control_negative_direction (C s : ℝ) (hs : s ≠ 0) :
    controlLoewner C 0 0 - controlLoewner C 0 s - controlLoewner C s 0 +
      controlLoewner C s s < 0 := by
  rw [control_quadratic]
  exact neg_neg_of_pos (sq_pos_of_ne_zero hs)

theorem control_positive_diagonals (C s : ℝ) (hC : 0 < C) (hs : 3*s^2 < C) :
    0 < controlLoewner C 0 0 ∧ 0 < controlLoewner C s s := by
  constructor
  · simpa only [controlLoewner, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, sub_zero] using hC
  · dsimp only [controlLoewner]
    nlinarith [sq_nonneg s]

end
end CarryMixedGreen
