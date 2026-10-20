import CriticalOrientation

namespace CarryCriticalMixed
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCriticalRelative Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The entire old nonlinear companion remainder, in its original metric. -/
def secondNonlinearReadout (a : ℝ) (k : ℕ) : ℝ :=
  let d := radialCompletedValueCoefficients k (nativeSourceChiralJetInput 2 k (secondEvenJet a))
  4*(inner ℂ (radialIncidentSynthesis k 4 d) (radialCompletedRemainderSynthesis k 4 d)).re

theorem second_value_sum (a : ℝ) (k : ℕ)
    (hF : ∀ r : Fin 4, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin 4, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    (∑ r : Fin 4, radialCompletedValueCoefficients k
      (nativeSourceChiralJetInput 2 k (secondEvenJet a)) r) =
      (Real.sqrt 2 : ℂ)⁻¹*(a:ℂ) := by
  rw [valueCoefficients_eq_stencil 2 k _ hF hP, second_stencil_exact]
  simp only [secondStencil, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem eulerScale_eq_sourceCoefficient (k : ℕ) :
    radialCompletedEulerScale k = sourceCoefficient 0/((k:ℝ)+1) := by
  have hc := nativeSourceOddBoundaryCoefficient_integral_formulas
  dsimp only at hc
  change radialCompletedEulerScale k = nativeSourceOddBoundaryCoefficient 0/((k:ℝ)+1)
  rw [radialCompletedEulerScale_eq_sourceIntegralRatio, hc.1]

/-- All growth cancels in the first Euler contribution, exactly at finite k. -/
theorem second_euler_exact (a : ℝ) (k : ℕ)
    (hF : ∀ r : Fin 4, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin 4, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    secondBalance a k = sourceCoefficient 0*a^2+secondNonlinearReadout a k := by
  rw [secondBalance, storage_one_eq_euler_boundary_add_remainder k 4 _ hF hP,
    second_value_sum a k hF hP, eulerScale_eq_sourceCoefficient]
  change 2*((k:ℝ)+1)*(sourceCoefficient 0/((k:ℝ)+1))*
      Complex.normSq ((Real.sqrt 2:ℂ)⁻¹*(a:ℂ)) + secondNonlinearReadout a k = _
  have hs : Complex.normSq ((Real.sqrt 2:ℂ)⁻¹) = (1:ℝ)/2 := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [Complex.normSq_mul, hs, Complex.normSq_ofReal]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem second_nonlinear_tendsto (a : ℝ) :
    Tendsto (secondNonlinearReadout a) atTop
      (nhds (2*sourceCoefficient 1*a+sourceCoefficient 2)) := by
  have ht := (second_balance_tendsto a).sub_const (sourceCoefficient 0*a^2)
  have he : balanceConstant a-sourceCoefficient 0*a^2 =
      2*sourceCoefficient 1*a+sourceCoefficient 2 := by unfold balanceConstant; ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk
  rw [second_euler_exact a k (fun r => (hk r).2.1) (fun r => (hk r).2.2)]
  ring

/-- New strict orientation of the actual nonlinear source remainder, derived
from theta bounds rather than assumed positivity of the next Hankel section. -/
theorem second_critical_nonlinear_eventually_pos :
    ∀ᶠ k : ℕ in atTop, 0 < secondNonlinearReadout secondCriticalParameter k := by
  have ht := second_nonlinear_tendsto secondCriticalParameter
  have he : 2*sourceCoefficient 1*secondCriticalParameter+sourceCoefficient 2 =
      2*(h 0*h 2-2*(h 1)^2)/h 0 := by
    unfold secondCriticalParameter
    simp_rw [sourceCoefficient_eq_canonical]
    field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
    ring
  rw [he] at ht
  have hp : 0 < 2*(h 0*h 2-2*(h 1)^2)/h 0 :=
    div_pos (mul_pos (by norm_num) source_nonlinear_margin_pos)
      canonicalCompletedNativeLogDerivativeMoment_zero_pos
  exact (tendsto_order.mp ht).1 0 hp

end
end CarryCriticalMixed
