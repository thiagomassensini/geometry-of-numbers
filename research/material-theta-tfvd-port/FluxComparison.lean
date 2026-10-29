import CameraCompletion

/-! Exact two-input kernels of the two RETAINED Green projections. Material
logarithm and derivative in u are not silently identified. The Gamma and
completion terms have not been added to either of these raw modal kernels. -/
namespace CarryMaterialTheta
open NativeCarrySpectralWeyl.Boundary
noncomputable section
set_option autoImplicit false

theorem material_log_green_modes (n m : ℕ) (a d : ℂ) (u : ℝ) :
    greenForm (𝕜 := ℂ) (logPort (materialThetaMode n a u))
      (logPort (materialThetaMode m d u)) =
      (starRingEnd ℂ a)*d *
        (((Real.log (n : ℝ)-Real.log (m : ℝ))*addressMode n u*addressMode m u : ℝ) : ℂ) := by
  simp only [greenForm, logPort, materialThetaMode, RCLike.inner_apply',
    Complex.ofReal_mul, Complex.ofReal_sub, map_mul, Complex.conj_ofReal]
  ring

theorem theta_derivative_green_modes (n m : ℕ) (a d : ℂ) (u : ℝ) :
    greenForm (𝕜 := ℂ) (derivativePort (materialThetaMode n a u))
      (derivativePort (materialThetaMode m d u)) =
      (starRingEnd ℂ a)*d *
        ((2*Real.pi*((m : ℝ)^2-(n : ℝ)^2)*Real.exp (2*u)*
          addressMode n u*addressMode m u : ℝ) : ℂ) := by
  simp only [greenForm, derivativePort, materialThetaMode, addressModeFirst,
    RCLike.inner_apply', Complex.ofReal_mul, Complex.ofReal_sub,
    map_mul, map_sub, Complex.conj_ofReal]
  push_cast
  ring

/-- Same original modes, same existing Green form, opposite signs in the
first nontrivial off-diagonal test. Completion may not be omitted in an
attempt to identify these two channels. -/
theorem raw_modal_fluxes_have_opposite_sign (u : ℝ) :
    (greenForm (𝕜 := ℂ) (logPort (materialThetaMode 1 1 u))
      (logPort (materialThetaMode 2 1 u))).re < 0 ∧
    0 < (greenForm (𝕜 := ℂ) (derivativePort (materialThetaMode 1 1 u))
      (derivativePort (materialThetaMode 2 1 u))).re := by
  rw [material_log_green_modes, theta_derivative_green_modes]
  norm_num only [map_one, one_mul, Nat.cast_one, Nat.cast_ofNat, Real.log_one,
    zero_sub, Complex.ofReal_re, one_pow]
  constructor
  · exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.log_pos (by norm_num)))
        (addressMode_pos 1 u)) (addressMode_pos 2 u)
  · have h1 := addressMode_pos 1 u
    have h2 := addressMode_pos 2 u
    positivity

/-- A nonzero addressed state can have zero self Green flux. It is not a
null state, and the Green flux alone is not its positive Hilbert norm. -/
theorem nonzero_mode_with_zero_self_green (n : ℕ) (u : ℝ) :
    materialThetaMode n 1 u ≠ 0 ∧
      greenForm (𝕜 := ℂ) (logPort (materialThetaMode n 1 u))
        (logPort (materialThetaMode n 1 u)) = 0 := by
  constructor
  · intro h
    have hv := congrArg Prod.fst h
    simp only [materialThetaMode, one_mul, Prod.fst_zero] at hv
    exact (Complex.ofReal_ne_zero.mpr (addressMode_pos n u).ne') hv
  · rw [material_log_green_modes]
    simp

end
end CarryMaterialTheta
