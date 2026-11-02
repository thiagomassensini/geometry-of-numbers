import PairCurve
import SquaredStepBudget

namespace CarrySummableRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def familyCurve (S : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ r ∈ S, ∑ s ∈ S, c r*c s*(effectivePairCurve r s (t:ℂ)).re

def familyConstant (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ r ∈ S, ∑ s ∈ S, |c r*c s| *pairConstant r s

theorem family_constant_nonneg (S : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ familyConstant S c := by
  unfold familyConstant
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (abs_nonneg _) (pair_constant_nonneg r s)

theorem family_curve_grid (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ)
    (hk : (oddGridSize S:ℝ)*|radialFourSourceStep k| < 1/4) :
    fullEnergy k (finiteOddJetSource S c k)=familyCurve S c (radialFourSourceStep k) := by
  rw [finite_odd_energy_pairing_at_regular S c k hk]
  unfold familyCurve
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [normalized_odd_pair_effective_at_regular S r s k hr hs hk]
  simp [effectivePairCurve,pairCorrection,pairTail,radialStep,radialFourSourceStep, mul_assoc]

/-- Every sampled argument of every retained ordered cross fits the same
explicit source disc. -/
theorem family_pair_disc (S : Finset ℕ) (r s : ℕ) (hr : r ∈ S) (hs : s ∈ S)
    (t : ℝ) (ht : (oddGridSize S:ℝ)*|t| < 1/4) :
    ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*(t:ℂ)‖ ≤ 1/4 := by
  have hr' : r ≤ S.sup id := Finset.le_sup (f:=id) hr
  have hs' : s ≤ S.sup id := Finset.le_sup (f:=id) hs
  have hm : 2*max r s+2 ≤ oddGridSize S := by unfold oddGridSize; omega
  intro j hj
  have hh := finite_grid_radius (oddGridSize S) t ht ⟨j,by omega⟩
  have hh' : ‖((j+1:ℕ):ℂ)*(t:ℂ)‖ < 1/4 := by
    simpa [CarryMovingRadial.point, norm_mul, mul_assoc] using hh
  exact hh'.le

theorem family_curve_differentiable (S : Finset ℕ) (c : ℕ → ℝ) (t : ℝ)
    (ht : (oddGridSize S:ℝ)*|t| < 1/4) : DifferentiableAt ℝ (familyCurve S c) t := by
  unfold familyCurve
  apply DifferentiableAt.fun_sum
  intro r hr
  apply DifferentiableAt.fun_sum
  intro s hs
  have hdisc := family_pair_disc S r s hr hs t ht
  have hz : ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*(t:ℂ)‖ < 1 := by
    intro j hj; have := hdisc j hj; linarith
  exact (pair_curve_hasDerivAt r s (t:ℂ) hz).real_of_complex.differentiableAt.const_mul _

theorem family_curve_derivative_bound (S : Finset ℕ) (c : ℕ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hdisc : (oddGridSize S:ℝ)*|t| < 1/4) :
    |deriv (familyCurve S c) t| ≤ 2*familyConstant S c*t := by
  have hd (r s : ℕ) (hr : r ∈ S) (hs : s ∈ S) :
      DifferentiableAt ℝ (fun x : ℝ => (effectivePairCurve r s (x:ℂ)).re) t := by
    have hz := family_pair_disc S r s hr hs t hdisc
    apply (pair_curve_hasDerivAt r s (t:ℂ) (fun j hj => lt_of_le_of_lt (hz j hj) (by norm_num))).real_of_complex.differentiableAt
  have hfd : HasDerivAt (familyCurve S c)
      (∑ r ∈ S, ∑ s ∈ S, c r*c s*deriv (fun x : ℝ => (effectivePairCurve r s (x:ℂ)).re) t) t := by
    unfold familyCurve
    apply HasDerivAt.fun_sum
    intro r hr
    apply HasDerivAt.fun_sum
    intro s hs
    exact (hd r s hr hs).hasDerivAt.const_mul _
  rw [hfd.deriv]
  calc
    _ ≤ ∑ r ∈ S, ∑ s ∈ S, |c r*c s*deriv (fun x : ℝ => (effectivePairCurve r s (x:ℂ)).re) t| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun r hr => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ r ∈ S, ∑ s ∈ S, |c r*c s| *(2*pairConstant r s*t) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (pair_curve_derivative_bound r s t ht ht1 (family_pair_disc S r s hr hs t hdisc)) (abs_nonneg _)
    _ = _ := by
      unfold familyConstant
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      ring

end
end CarrySummableRadial
