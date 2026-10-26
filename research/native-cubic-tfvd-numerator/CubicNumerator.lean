import Stencil
import NativeCoefficient

namespace CarryCubicTfvd
open CarrySelfAdjointOperator NativeCauchyPorts NativeLaguerre
open CarryNativeTfvd CarryCriticalTfvd CarryCurvatureGreen CarryLinearTfvd CarryStencilBoundary
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- Literal first difference of the old cubic response weight, at address j. -/
def cubicForwardWeight (j : ℕ) : ℂ := 3*(j : ℂ)^2+3*(j : ℂ)+1

/-- The other ordered first difference of the SAME cubic response weight. -/
def cubicBackwardWeight (j : ℕ) : ℂ := 3*(j : ℂ)^2+9*(j : ℂ)+7

def cubicTrace (c : ℕ →₀ ℂ) : PhysicalSpace :=
  c 0 • completedNativeChiralCauchyFeature 0 +
    (7*c 1) • completedNativeChiralCauchyFeature 1

theorem cubic_commutator_succ (eta : ℝ) (c : ℕ →₀ ℂ) (j : ℕ) :
    completionCommutator eta (monomialWeight 3) c (j+1) =
      (eta : ℂ)⁻¹*cubicForwardWeight (j+2)*c (j+2) -
        (eta : ℂ)*cubicBackwardWeight j*c j := by
  rw [completion_commutator_succ]
  simp only [monomialWeight, cubicForwardWeight, cubicBackwardWeight,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- The exact coefficient numerator, with both independent original traces.
No source is changed, and no domain of an infinite differential operator is assumed. -/
theorem cubic_shift_numerator (eta : ℝ) (c : ℕ →₀ ℂ) :
    coefficientShift (completionCommutator eta (monomialWeight 3) c) =
      (eta : ℂ)⁻¹ • (coefficientWeight cubicForwardWeight c -
        Finsupp.single 0 (c 0)-Finsupp.single 1 (7*c 1)) -
      (eta : ℂ) • coefficientShift (coefficientShift (coefficientWeight cubicBackwardWeight c)) := by
  ext j
  rcases j with _ | _ | j
  all_goals simp [coefficientShift_zero, coefficientShift_succ,
    completion_commutator_zero, cubic_commutator_succ, coefficient_weight_apply,
    cubicForwardWeight, cubicBackwardWeight, Nat.add_assoc] <;> ring_nf <;> simp

/-- Physical numerator in the ORIGINAL carrier, without inverting M. -/
theorem cubic_physical_numerator (eta : ℝ) (c : ℕ →₀ ℂ) :
    physicalRadialAdvance
      (physicalCauchySynthesis (completionCommutator eta (monomialWeight 3) c)) =
      (eta : ℂ)⁻¹ • (physicalCauchySynthesis (coefficientWeight cubicForwardWeight c)-cubicTrace c) -
      (eta : ℂ) • physicalRadialAdvance (physicalRadialAdvance
        (physicalCauchySynthesis (coefficientWeight cubicBackwardWeight c))) := by
  rw [← synthesis_shift, cubic_shift_numerator]
  simp only [map_sub, map_smul, synthesis_shift]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single, cubicTrace]
  module

end
end CarryCubicTfvd
