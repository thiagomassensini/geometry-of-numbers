import FiniteTraces
import CurvatureKernel

namespace CarryLinearTfvd
open CarrySelfAdjointOperator NativeCauchyPorts NativeLaguerre
open CarryNativeTfvd CarryCriticalTfvd CarryCurvatureGreen
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- The original Cauchy synthesis intertwines the literal coefficient shift
with the bounded physical multiplier. This does not assert an isometry. -/
theorem synthesis_shift (c : ℕ →₀ ℂ) :
    physicalCauchySynthesis (coefficientShift c) =
      physicalRadialAdvance (physicalCauchySynthesis c) := by
  change Finsupp.linearCombination ℂ completedNativeChiralCauchyFeature
    (Finsupp.mapDomain Nat.succ c) = _
  rw [Finsupp.linearCombination_mapDomain]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_apply,
    Finsupp.sum, Function.comp_apply, map_sum, map_smul,
    physicalRadialAdvance_feature]

/-- Literal two-trace readout in the original physical carrier. -/
def physicalTrace (c : ℕ →₀ ℂ) : PhysicalSpace :=
  (c 0) • completedNativeChiralCauchyFeature 0 +
    (c 1) • completedNativeChiralCauchyFeature 1

/-- The obligation isolated by PR97, for arbitrary finite support. The equality
is a numerator identity; the unbounded inverse of M is never introduced. -/
theorem physical_linear_numerator (eta : ℝ) (c : ℕ →₀ ℂ) :
    physicalRadialAdvance
      (physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) c)) =
      (eta : ℂ)⁻¹ • (physicalCauchySynthesis c-physicalTrace c) -
        (eta : ℂ) • physicalRadialAdvance
          (physicalRadialAdvance (physicalCauchySynthesis c)) := by
  rw [← synthesis_shift, linear_commutator_shift_numerator]
  simp only [map_sub, map_smul, synthesis_shift]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single, physicalTrace]
  module

/-- The physical bulk formula retains the center correction inherited from
the original TFVD reconstruction, with the same coefficients. -/
theorem physical_linear_tfvd_numerator (eta : ℝ) (c : ℕ →₀ ℂ) :
    physicalRadialAdvance
      (physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) c)) =
      physicalRadialAdvance (physicalCauchySynthesis (finiteTfvdBulk eta c)) +
        (2 : ℂ) • physicalRadialAdvance (physicalCauchySynthesis c) -
        (2*(eta : ℂ)) • physicalRadialAdvance
          (physicalRadialAdvance (physicalCauchySynthesis c)) -
        (2*c 0) • completedNativeChiralCauchyFeature 1 := by
  rw [← synthesis_shift, linear_commutator_tfvd_numerator]
  simp only [map_sub, map_add, map_smul, synthesis_shift]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single]

end
end CarryLinearTfvd
