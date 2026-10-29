import CubicNumerator

namespace CarryCubicTfvd
open CarrySelfAdjointOperator NativeCauchyPorts NativeLaguerre
open CarryNativeTfvd CarryCriticalTfvd CarryCurvatureGreen CarryLinearTfvd CarryStencilBoundary
open CarryCommutatorControl
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- Only an alias of the old mixed sectorKernel, with its original metric. -/
def cubicKernel (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (c d : ℕ →₀ ℂ) : ℂ :=
  sectorKernel true eta h0 h1 (monomialWeight 3) c d

theorem cubic_kernel_original (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (c d : ℕ →₀ ℂ) :
    cubicKernel eta h0 h1 c d = inner ℂ (physicalCauchySynthesis c)
      (physicalGreenOperator eta h0.le h1
        (physicalCauchySynthesis (completionCommutator eta (monomialWeight 3) d))) := by
  rfl

/-- Full complex pairing for TWO independent inputs. The cubic trace is mixed
with the whole left source before any diagonal or real readout. -/
theorem cubic_green_polarized (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (c d : ℕ →₀ ℂ) :
    cubicKernel eta h0 h1 c d =
      inner ℂ (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))
        (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis (coefficientWeight cubicForwardWeight d))) -
      inner ℂ (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))
        (physicalGreenResolvent eta h0.le h1 (cubicTrace d)) -
      (eta : ℂ)^2 * inner ℂ
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalCauchySynthesis c)))
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance
          (physicalCauchySynthesis (coefficientWeight cubicBackwardWeight d)))) := by
  rw [cubic_kernel_original, green_inner_right_numerator eta h0 h1, cubic_physical_numerator]
  simp only [map_sub, map_smul, inner_sub_right, inner_smul_right]
  rw [double_advance_pairing eta h0 h1]
  have he : (eta : ℂ)≠0 := Complex.ofReal_ne_zero.mpr h0.ne'
  field_simp [he]

theorem cubic_green_diagonal (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (c : ℕ →₀ ℂ) :
    (cubicKernel eta h0 h1 c c).re =
      (inner ℂ (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))
        (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis (coefficientWeight cubicForwardWeight c)))).re -
      (inner ℂ (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))
        (physicalGreenResolvent eta h0.le h1 (cubicTrace c))).re -
      eta^2*(inner ℂ
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalCauchySynthesis c)))
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance
          (physicalCauchySynthesis (coefficientWeight cubicBackwardWeight c))))).re := by
  rw [cubic_green_polarized eta h0 h1]
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two, Complex.mul_re]
  have hIm (r : ℝ) : ((r : ℂ)^2).im=0 := by simp [pow_two, Complex.mul_im]
  simp [Complex.sub_re, Complex.mul_re, hRe, hIm]

/-- The original seed is a strict negative test for the cubic coefficient.
This does not assert a sign for the completed nonlinear balance. -/
theorem cubic_seed_negative (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (cubicKernel eta h0 h1 (Finsupp.single 0 1) (Finsupp.single 0 1)).re < 0 := by
  have hs : completionCommutator eta (monomialWeight 3) (Finsupp.single 0 1)=
      Finsupp.single 1 (-7*(eta : ℂ)) := by
    ext j
    rcases j with _ | _ | j
    all_goals simp [completion_commutator_zero, cubic_commutator_succ,
      cubicForwardWeight, cubicBackwardWeight] <;> ring
  rw [cubic_kernel_original, hs]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single, one_smul,
    map_smul, inner_smul_right]
  have hp := green_seed_cross_re_pos eta h0 h1
  norm_num [Complex.mul_re] at hp ⊢
  nlinarith

end
end CarryCubicTfvd
