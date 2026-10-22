import FirstJet

namespace CarryRadialConservative
open CarrySelfAdjointOperator ChiralReturn CarryCriticalRelative CarryConservativeIntertwiner
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
local notation "h₀" => canonicalCompletedNativeLogDerivativeMoment 0

/-- The inherited theta bound is used only to orient this already identified coefficient. -/
theorem first_even_mixed_cross_eventually_pos :
    ∀ᶠ k : ℕ in atTop, 0<2*(inner ℂ
      (conservativeSynthesis k 2 (jetCoefficients 1 k firstEvenBoundary))
      (nativeDefect k 2 (jetCoefficients 1 k firstEvenBoundary))).re := by
  apply first_even_mixed_cross_tendsto.eventually (eventually_gt_nhds _)
  have h := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith


theorem native_symbol_defect_tangent_ne (j : ℕ) :
    4*((j:ℂ)+1)*((h₀:ℂ)-1)≠0 := by
  apply mul_ne_zero
  · apply mul_ne_zero (by norm_num)
    exact_mod_cast (show (j:ℝ)+1≠0 by positivity)
  · have h := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
    have hh : h₀-1≠0 := by linarith
    exact_mod_cast hh

/-- Even with k retained, this inherited conservative family differs from the actual quotient. -/
theorem native_symbol_eventually_ne (j : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)≠
        (radialSymbol k j:ℂ) := by
  have h := (native_symbol_defect_tangent j).eventually_ne (native_symbol_defect_tangent_ne j)
  filter_upwards [h] with k hk he
  apply hk
  rw [he,sub_self,mul_zero]

end
end CarryRadialConservative
