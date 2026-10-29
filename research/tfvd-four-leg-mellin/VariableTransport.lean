import GradientMellin
import GeometryOfNumbers.Analysis.C2FiberRealDynamics
import GeometryOfNumbers.Analysis.MaterialLogTfvdCanary

/-! A read-only diagnostic of the existing TFVD operators. The rotated
sequences are required to belong to the original L2 carrier; this does not
assume an encoder from the physical source or identify C2 with C3. -/
namespace CarryFourLeg
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.RealCarry
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem bracket_variable_rotation_defect
    (eta : ℝ) (theta : ℕ → ℝ) (x₁ x₂ y₁ y₂ : CarryVerticalL2)
    (hy : ∀ k, (y₁ k, y₂ k) = rotateRealPlane (theta k) (x₁ k, x₂ k)) (k : ℕ) :
    (carryWeightedVerticalCenteredBracket eta y₁ (k+1),
     carryWeightedVerticalCenteredBracket eta y₂ (k+1)) -
      rotateRealPlane (theta (k+1))
        (carryWeightedVerticalCenteredBracket eta x₁ (k+1),
         carryWeightedVerticalCenteredBracket eta x₂ (k+1)) =
    eta⁻¹ • (rotateRealPlane (theta (k+2)) (x₁ (k+2), x₂ (k+2)) -
      rotateRealPlane (theta (k+1)) (x₁ (k+2), x₂ (k+2))) +
    eta • (rotateRealPlane (theta k) (x₁ k, x₂ k) -
      rotateRealPlane (theta (k+1)) (x₁ k, x₂ k)) := by
  have h₁ (j : ℕ) : y₁ j = Real.cos (theta j)*x₁ j - Real.sin (theta j)*x₂ j := by
    simpa only [rotateRealPlane, mul_comm] using congrArg Prod.fst (hy j)
  have h₂ (j : ℕ) : y₂ j = Real.sin (theta j)*x₁ j + Real.cos (theta j)*x₂ j := by
    simpa only [rotateRealPlane, mul_comm] using congrArg Prod.snd (hy j)
  apply Prod.ext <;>
    simp only [carryWeightedVerticalCenteredBracket_succ, rotateRealPlane,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, h₁, h₂] <;> ring

theorem trace_variable_rotation_defect
    (eta : ℝ) (theta : ℕ → ℝ) (x₁ x₂ y₁ y₂ : CarryVerticalL2)
    (hy : ∀ k, (y₁ k, y₂ k) = rotateRealPlane (theta k) (x₁ k, x₂ k)) :
    ((carryWeightedVerticalTrace eta y₁).2, (carryWeightedVerticalTrace eta y₂).2) -
      rotateRealPlane (theta 0)
        ((carryWeightedVerticalTrace eta x₁).2, (carryWeightedVerticalTrace eta x₂).2) =
      eta⁻¹ • (rotateRealPlane (theta 1) (x₁ 1, x₂ 1) -
        rotateRealPlane (theta 0) (x₁ 1, x₂ 1)) := by
  have h₁ (j : ℕ) : y₁ j = Real.cos (theta j)*x₁ j - Real.sin (theta j)*x₂ j := by
    simpa only [rotateRealPlane, mul_comm] using congrArg Prod.fst (hy j)
  have h₂ (j : ℕ) : y₂ j = Real.sin (theta j)*x₁ j + Real.cos (theta j)*x₂ j := by
    simpa only [rotateRealPlane, mul_comm] using congrArg Prod.snd (hy j)
  apply Prod.ext <;>
    simp only [carryWeightedVerticalTrace_apply, rotateRealPlane,
      Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, h₁, h₂] <;> ring

/-- Amplitude and phase can both vary: this identity uses the existing
complex scalar TFVD, without assuming that multiplication commutes with it. -/
theorem scalar_bracket_multiplier_defect {q : ℂ} (hq : q ≠ 0)
    (a x : ℕ → ℂ) (k : ℕ) :
    CPFormal.Analytic.Cp.carryWeightedScalarSecondDifference q (fun j => a j*x j) k -
      a (k+1)*CPFormal.Analytic.Cp.carryWeightedScalarSecondDifference q x k =
      q⁻¹*(a (k+2)-a (k+1))*x (k+2) + q*(a k-a (k+1))*x k := by
  rw [CPFormal.Analytic.Cp.carryWeightedScalarSecondDifference_eq hq, CPFormal.Analytic.Cp.carryWeightedScalarSecondDifference_eq hq]
  ring

theorem scalar_trace_multiplier_defect (q : ℂ) (a x : ℕ → ℂ) :
    CPFormal.Analytic.Cp.carryWeightedScalarFirstDifference q (fun j => a j*x j) 0 -
      a 0*CPFormal.Analytic.Cp.carryWeightedScalarFirstDifference q x 0 =
      q⁻¹*(a 1-a 0)*x 1 := by
  simp only [CPFormal.Analytic.Cp.carryWeightedScalarFirstDifference, Nat.zero_add]
  ring

/-- Exact TFVD synthesis with BOTH the multiplier interior correction and
the corrected initial slope. No input term is removed after transport. -/
theorem multiplier_tfvd_reconstruction {q : ℂ} (hq : q ≠ 0)
    (a x : ℕ → ℂ) (n : ℕ) :
    a n*x n = q^n*(a 0*x 0 + (n : ℂ)*
      (a 0*CPFormal.Analytic.Cp.carryWeightedScalarFirstDifference q x 0 + q⁻¹*(a 1-a 0)*x 1)) +
      ∑ j ∈ Finset.range n, ((n-1-j : ℕ) : ℂ)*q^(n-1-j)*
        (a (j+1)*CPFormal.Analytic.Cp.carryWeightedScalarSecondDifference q x j +
          (q⁻¹*(a (j+2)-a (j+1))*x (j+2) + q*(a j-a (j+1))*x j)) := by
  have hslope := scalar_trace_multiplier_defect q a x
  have hcurv (j : ℕ) := scalar_bracket_multiplier_defect hq a x j
  have h := CPFormal.Analytic.Cp.carryWeightedScalarReconstruction hq (fun j => a j*x j) n
  have hd : CPFormal.Analytic.Cp.carryWeightedScalarFirstDifference q (fun j => a j*x j) 0 =
      a 0*CPFormal.Analytic.Cp.carryWeightedScalarFirstDifference q x 0 + q⁻¹*(a 1-a 0)*x 1 := by
    linear_combination hslope
  have hb (j : ℕ) : CPFormal.Analytic.Cp.carryWeightedScalarSecondDifference q (fun l => a l*x l) j =
      a (j+1)*CPFormal.Analytic.Cp.carryWeightedScalarSecondDifference q x j +
        (q⁻¹*(a (j+2)-a (j+1))*x (j+2) + q*(a j-a (j+1))*x j) := by
    linear_combination hcurv j
  simpa only [CPFormal.Analytic.Cp.carryWeightedScalarGreenSum, hd, hb] using h

/-- Exact material wave on the C2 points. The depth change includes the
leg's amplitude correction as well as its phase correction. -/
theorem c2_material_wave_step (m : ℕ) (epsilon : ℝ) (s : ℂ) (k : ℕ)
    (hm : 0 < m) (hx : 0 < c2FiberPoint m epsilon k)
    (hy : 0 < c2FiberPoint m epsilon (k+1)) :
    (c2FiberPoint m epsilon (k+1) : ℂ)^(-s) = (2 : ℂ)^(-s) *
      Complex.exp (-s*((c2FiberLogDefect m epsilon (k+1) -
        c2FiberLogDefect m epsilon k : ℝ) : ℂ)) * (c2FiberPoint m epsilon k : ℂ)^(-s) := by
  have hl := c2FiberPoint_log_increment_defect m k hm epsilon hx hy
  have hlc : (Real.log (c2FiberPoint m epsilon (k+1)) : ℂ) =
      (Real.log 2 : ℂ) +
        ((c2FiberLogDefect m epsilon (k+1) - c2FiberLogDefect m epsilon k : ℝ) : ℂ) +
        (Real.log (c2FiberPoint m epsilon k) : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hl
    push_cast at h ⊢
    linear_combination h
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'),
    Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hy.le, ← Complex.ofReal_log hx.le]
  have htwo : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    simp
  rw [htwo, hlc, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem c2_material_correction_norm (m k : ℕ) (epsilon : ℝ) (s : ℂ) :
    ‖Complex.exp (-s*((c2FiberLogDefect m epsilon (k+1) -
        c2FiberLogDefect m epsilon k : ℝ) : ℂ))‖ =
      Real.exp (-s.re*(c2FiberLogDefect m epsilon (k+1) - c2FiberLogDefect m epsilon k)) := by
  simp [Complex.norm_exp, Complex.mul_re]

/-- Vanishing phase value at t=0 does not make its first jet vanish.
This keeps the scope of the zero-time obstruction precise. -/
theorem c2_phase_correction_hasDerivAt (m k : ℕ) (epsilon t : ℝ) :
    HasDerivAt (fun u : ℝ => -u*(c2FiberLogDefect m epsilon (k+1) -
        c2FiberLogDefect m epsilon k))
      (-(c2FiberLogDefect m epsilon (k+1) - c2FiberLogDefect m epsilon k)) t := by
  exact (((hasDerivAt_id t).neg).mul_const _).congr_deriv (by ring)

/-- The original depth amplitude is retained. This is the explicit factor
needed to compare it with amplitude at the actual material leg address. -/
theorem c2_material_amplitude_factor (m k : ℕ) (epsilon : ℝ)
    (hm : 0 < m) (hx : 0 < c2FiberPoint m epsilon k) :
    (c2FiberPoint m epsilon k)^(-(1 : ℝ)/2) =
      realCriticalAmplitude 2 k (by decide) * (m : ℝ)^(-(1 : ℝ)/2) *
        Real.exp (-c2FiberLogDefect m epsilon k/2) := by
  rw [realCriticalAmplitude_eq_rpow]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by exact_mod_cast hm),
    c2FiberPoint_log_eq_depth_core_defect m k hm epsilon hx,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end
end CarryFourLeg
