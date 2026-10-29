import NativeCriticalGrid

namespace CarryCriticalGrid
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000

/-- A RATIONAL DIAGNOSTIC response on the actual k=31 mesh. It is not the
canonical native response and is never substituted into a native theorem. -/
def diagnosticSamples (j : Fin 4) : ℂ :=
  (1+squaredNode (1/1024:ℂ) j)^(-2:ℤ)

theorem diagnostic_samples_positive_real (j : Fin 4) :
    (diagnosticSamples j).im=0 ∧ 0<(diagnosticSamples j).re := by
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl | rfl
  all_goals norm_num [diagnosticSamples,squaredNode]

/-- The first THREE alternating curvature signs all hold. -/
theorem diagnostic_three_curvature_signs :
    (gridFirst (1/1024) diagnosticSamples).re<0 ∧
    0<(gridSecond (1/1024) diagnosticSamples).re ∧
    (gridThird (1/1024) diagnosticSamples).re<0 := by
  norm_num [gridFirst,gridSecond,gridThird,gridSecondRight,diagnosticSamples,squaredNode]

/-- Even all THREE entries of the induced real symmetric 2x2 form are positive. -/
theorem diagnostic_positive_entries :
    0<(-gridFirst (1/1024) diagnosticSamples).re ∧
    0<(gridSecond (1/1024) diagnosticSamples+28*(1/1024)*gridThird (1/1024) diagnosticSamples).re ∧
    0<(-gridThird (1/1024) diagnosticSamples).re := by
  norm_num [gridFirst,gridSecond,gridThird,gridSecondRight,diagnosticSamples,squaredNode]

/-- Nevertheless the ORIGINAL trial coefficient pattern gives a negative form.
This is a diagnostic of a proposed scalar sign principle, not of canonical h. -/
theorem diagnostic_critical_negative :
    (gridBalance (1/1024) (3/2) (3/2) diagnosticSamples).re=
      -(12349553402974306304/62570745502766028125:ℝ) := by
  rw [critical_grid_curvatures _ (by norm_num)]
  norm_num [gridFirst,gridSecond,gridThird,gridSecondRight,diagnosticSamples,squaredNode]

/-- Concrete no-go: scalar positivity/curvature orientations do not control
mixed critical directions, even on a genuine original radial squared grid. -/
theorem no_sign_from_three_curvatures :
    ¬ (∀ f : Fin 4 → ℂ, (∀ j, (f j).im=0 ∧ 0<(f j).re) →
      (gridFirst (squaredScale 31) f).re<0 →
      0<(gridSecond (squaredScale 31) f).re →
      (gridThird (squaredScale 31) f).re<0 →
      0<(gridSecond (squaredScale 31) f+28*squaredScale 31*gridThird (squaredScale 31) f).re →
      0≤(gridBalance (squaredScale 31) (3/2) (3/2) f).re) := by
  intro hh
  have hs : squaredScale 31=(1/1024:ℂ) := by norm_num [squaredScale]
  rw [hs] at hh
  have hp := hh diagnosticSamples diagnostic_samples_positive_real
    diagnostic_three_curvature_signs.1 diagnostic_three_curvature_signs.2.1
    diagnostic_three_curvature_signs.2.2 diagnostic_positive_entries.2.1
  rw [diagnostic_critical_negative] at hp
  norm_num at hp

end
end CarryCriticalGrid
