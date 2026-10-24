import RadialRefinement

/-! Vectorial native completion before taking any scalar balance. -/
namespace CarryRadialRefinement
open CarryPhysicalTrace CarryCompletedTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CPFormal.Analytic.Cp
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- All six original fields, without a discarded channel. -/
def originalFields (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : Fin 6 → PhysicalCauchySpace :=
  ![physicalSourceValue k c r,physicalSourceCompanion k c r,
    physicalNativeCompanion k c r,physicalCompletionCompanion k c r,
    physicalOriginalIncident k c r,physicalOriginalReturned k c r]

theorem six_fields_common_isometry (m k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ) (a b : Fin 6) :
    inner ℂ (powerIsometry m (originalFields k c r a))
      (powerIsometry m (originalFields l d s b)) =
    inner ℂ (originalFields k c r a) (originalFields l d s b) :=
  power_isometry_inner m _ _

theorem original_source_legs_refined (m k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hs : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hp : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    powerIsometry m (physicalSourceCompanion k c r) =
      powerIsometry m (physicalNativeCompanion k c r)+powerIsometry m (physicalCompletionCompanion k c r) ∧
    powerIsometry m (physicalOriginalIncident k c r) =
      powerIsometry m (physicalNativeCompanion k c r)+powerIsometry m (physicalCompletionCompanion k c r)+
        Complex.I • powerIsometry m (physicalSourceValue k c r) ∧
    powerIsometry m (physicalOriginalReturned k c r) =
      powerIsometry m (physicalNativeCompanion k c r)+powerIsometry m (physicalCompletionCompanion k c r)-
        Complex.I • powerIsometry m (physicalSourceValue k c r) := by
  have h := GammaMaterialSewing.nativeCoupledCompletion_originalSource_legs k c r hs hp
  have hc : physicalSourceCompanion k c r = physicalNativeCompanion k c r+physicalCompletionCompanion k c r :=
    Subtype.ext h.1
  have hi : physicalOriginalIncident k c r = physicalNativeCompanion k c r+
      physicalCompletionCompanion k c r+Complex.I • physicalSourceValue k c r := Subtype.ext h.2.1
  have hr : physicalOriginalReturned k c r = physicalNativeCompanion k c r+
      physicalCompletionCompanion k c r-Complex.I • physicalSourceValue k c r := Subtype.ext h.2.2
  simp only [hc,hi,hr,map_add,map_sub,map_smul,and_self]

/-- Different refinements on the two arguments preserve the WHOLE vector
completion identity, then produce the four ordered Green/completion crosses. -/
theorem refined_complete_balance (m n k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ)
    (hs : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hp : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (ht : ∀ j : Fin M, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint l j) ∈ genuineCriticalStrip)
    (hq : ∀ j : Fin M, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint l j) ≠ 0) :
    inner ℂ (powerIsometry m (physicalOriginalIncident k c r)) (powerIsometry n (physicalOriginalIncident l d s)) -
      inner ℂ (powerIsometry m (physicalOriginalReturned k c r)) (powerIsometry n (physicalOriginalReturned l d s)) =
    -2*Complex.I*(
      inner ℂ (powerIsometry m (physicalSourceValue k c r)) (powerIsometry n (physicalNativeCompanion l d s))+
      inner ℂ (powerIsometry m (physicalSourceValue k c r)) (powerIsometry n (physicalCompletionCompanion l d s))-
      inner ℂ (powerIsometry m (physicalNativeCompanion k c r)) (powerIsometry n (physicalSourceValue l d s))-
      inner ℂ (powerIsometry m (physicalCompletionCompanion k c r)) (powerIsometry n (physicalSourceValue l d s))) := by
  have h1 := original_source_legs_refined m k c r hs hp
  have h2 := original_source_legs_refined n l d s ht hq
  rw [h1.2.1,h1.2.2,h2.2.1,h2.2.2]
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    _root_.inner_smul_left (𝕜 := ℂ) (E := PhysicalCauchySpace),
    _root_.inner_smul_right (𝕜 := ℂ) (E := PhysicalCauchySpace),Complex.conj_I]
  ring

/-- The exact Laguerre head/tail identity is retained after independent
refinements; the residual is never silently sent to zero. -/
theorem refined_head_tail (R m n : ℕ) (x y : PhysicalCauchySpace) :
    inner ℂ (powerIsometry m x) (powerIsometry n y) =
      inner ℂ (laguerreHead R (cauchyLaguerreIsometry (powerIsometry m x)))
        (laguerreHead R (cauchyLaguerreIsometry (powerIsometry n y)))+
      inner ℂ (physicalCauchyShift (R+1) (powerIsometry m x))
        (physicalCauchyShift (R+1) (powerIsometry n y)) :=
  physicalCauchy_head_tail_inner R _ _

end
end CarryRadialRefinement
