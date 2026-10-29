import FamilyCurve
import ScaledStep

namespace CarrySummableRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem family_curve_zero (S : Finset ℕ) (c : ℕ → ℝ) :
    familyCurve S c 0=oddCanonicalForm S c := by
  simp [familyCurve, effectivePairCurve, oddCanonicalForm]

theorem family_energy_tendsto (S : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun k => fullEnergy k (finiteOddJetSource S c k)) atTop (𝓝 (oddCanonicalForm S c)) := by
  have hc := (family_curve_differentiable S c 0 (by simp)).continuousAt.tendsto
  have ht := hc.comp CarryBoundaryReconstruction.radial_step_tendsto
  rw [family_curve_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (oddGridCutoff S)] with k hk
  exact (family_curve_grid S c k (odd_grid_cutoff_regular S k hk)).symm

theorem family_increment_budget (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ)
    (hk : oddGridCutoff S ≤ k) :
    |fullEnergy k (finiteOddJetSource S c k)-fullEnergy (k+1) (finiteOddJetSource S c (k+1))| ≤
      familyConstant S c*((radialFourSourceStep k)^2-(radialFourSourceStep (k+1))^2) := by
  have hreg := odd_grid_cutoff_regular S k hk
  have hreg' := odd_grid_cutoff_regular S (k+1) (by omega)
  rw [family_curve_grid S c k hreg, family_curve_grid S c (k+1) hreg']
  have hstep : radialFourSourceStep k ≤ 1 := by
    have h := (inv_le_inv₀ (show (0:ℝ)<(k:ℝ)+1 by positivity) (show (0:ℝ)<1 by norm_num)).mpr
      (show (1:ℝ) ≤ (k:ℝ)+1 by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    simpa [radialFourSourceStep] using h
  have hregular (t : ℝ) (ht : t ∈ Set.Icc (radialFourSourceStep (k+1)) (radialFourSourceStep k)) :
      0<t ∧ (oddGridSize S:ℝ)*|t| < 1/4 := by
    have hp : 0<t := lt_of_lt_of_le (radial_step_positive (k+1)) ht.1
    have hb := mul_le_mul_of_nonneg_left ht.2 (show (0:ℝ) ≤ oddGridSize S by positivity)
    rw [abs_of_pos (radial_step_positive k)] at hreg
    refine ⟨hp,?_⟩
    rw [abs_of_pos hp]
    exact lt_of_le_of_lt hb hreg
  apply squared_step_scaled (familyCurve S c) _ _ (familyConstant S c) (radial_step_decreasing k).le
  · intro t ht
    exact family_curve_differentiable S c t (hregular t ht).2
  · intro t ht
    exact family_curve_derivative_bound S c t (hregular t ht).1.le (ht.2.trans hstep) (hregular t ht).2

/-- Explicit summable increment budget for every finite fixed native odd
family, with all crossings and both physical legs retained. -/
theorem finite_odd_energy_absolute_tail (S : Finset ℕ) (c : ℕ → ℝ) (K : ℕ)
    (hK : oddGridCutoff S ≤ K) :
    HasSum (fun j => fullEnergy (K+j) (finiteOddJetSource S c (K+j))-
      fullEnergy (K+j+1) (finiteOddJetSource S c (K+j+1)))
      (fullEnergy K (finiteOddJetSource S c K)-oddCanonicalForm S c) ∧
    Summable (fun j => |fullEnergy (K+j) (finiteOddJetSource S c (K+j))-
      fullEnergy (K+j+1) (finiteOddJetSource S c (K+j+1))|) ∧
    (∑' j, |fullEnergy (K+j) (finiteOddJetSource S c (K+j))-
      fullEnergy (K+j+1) (finiteOddJetSource S c (K+j+1))|) ≤
      familyConstant S c*(radialFourSourceStep K)^2 := by
  apply radial_budget_hasSum _ _ (familyConstant S c) (family_energy_tendsto S c) K
  intro j
  exact family_increment_budget S c (K+j) (by omega)

theorem family_budget_tendsto_zero (S : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun K : ℕ => familyConstant S c*(radialFourSourceStep K)^2) atTop (𝓝 0) := by
  simpa using (CarryBoundaryReconstruction.radial_step_tendsto.pow 2).const_mul (familyConstant S c)

end
end CarrySummableRadial
