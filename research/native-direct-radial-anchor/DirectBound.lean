import FamilyCurve

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial NativeLaguerre Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- A bound on a SINGLE physical pair at the given scale. It comes from
its exact complete synthesis and the analytic remainder, not a boundary limit. -/
theorem pair_value_error (r s : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t≤1)
    (hz : ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*(t:ℂ)‖ < 1) :
    |(effectivePairCurve r s (t:ℂ)).re-h (r+s+1)| ≤ t^2*pairConstant r s := by
  have hb := odd_pair_effective_tail_bound (r+s+3) r s (t:ℂ) hz
  have hmoment : ‖(h (r+s+2):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact (source_coefficient_bound (r+s+2)).trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hcorr : ‖pairCorrection r s‖ ≤ ‖spatialCorrection (2*r+1) (2*s+1)‖ := by
    unfold pairCorrection
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmoment
      (norm_nonneg (spatialCorrection (2*r+1) (2*s+1)))
  have hreal : (effectivePairCurve r s (t:ℂ)).re-h (r+s+1) =
      (-((t:ℂ)^2)*pairCorrection r s+(t:ℂ)^4*pairTail r s (t:ℂ)).re := by
    simp [effectivePairCurve,Complex.sub_re,Complex.add_re]
    ring
  rw [hreal]
  apply (Complex.abs_re_le_norm _).trans
  have hs : ‖-((t:ℂ)^2)*pairCorrection r s+(t:ℂ)^4*pairTail r s (t:ℂ)‖ ≤
      t^2*‖pairCorrection r s‖+t^4*‖pairTail r s (t:ℂ)‖ := by
    have he := norm_add_le (-((t:ℂ)^2)*pairCorrection r s) ((t:ℂ)^4*pairTail r s (t:ℂ))
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,norm_neg] at he
    simpa only [neg_mul] using he
  apply hs.trans
  have hW : 0 ≤ oddFilterBudget r s (2*(r+s+3)+1)+oddFilterBudget s r (2*(r+s+3)+1) :=
    add_nonneg (odd_filter_budget_nonneg _ _ _) (odd_filter_budget_nonneg _ _ _)
  have hV : 0 ≤ oddFilterBudget r s (2*(r+s+3)+2)+oddFilterBudget s r (2*(r+s+3)+2) :=
    add_nonneg (odd_filter_budget_nonneg _ _ _) (odd_filter_budget_nonneg _ _ _)
  have hc := mul_le_mul_of_nonneg_left hcorr (sq_nonneg t)
  have hr := mul_le_mul_of_nonneg_left hb (show 0≤t^4 by positivity)
  have hp : t^4 ≤ t^2 := by nlinarith [sq_nonneg (t^2-t),sq_nonneg t,sq_nonneg (1-t^2)]
  have hw := mul_le_mul_of_nonneg_left hp hW
  dsimp only [pairTail] at *
  unfold pairConstant
  nlinarith

/-- Direct single-scale enclosure of the FULL original physical energy;
the old-new, new-old and all same-sector crossings are retained. -/
theorem finite_energy_direct_error (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ)
    (hcut : oddGridCutoff S ≤ k) :
    |fullEnergy k (finiteOddJetSource S c k)-oddCanonicalForm S c| ≤
      (radialFourSourceStep k)^2*familyConstant S c := by
  have hk := odd_grid_cutoff_regular S k hcut
  have hpos := radial_step_positive k
  have hstep : radialFourSourceStep k ≤ 1 := by
    have h := (inv_le_inv₀ (show (0:ℝ)<(k:ℝ)+1 by positivity) (show (0:ℝ)<1 by norm_num)).mpr
      (show (1:ℝ)≤(k:ℝ)+1 by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    simpa [radialFourSourceStep] using h
  rw [family_curve_grid S c k hk]
  unfold familyCurve oddCanonicalForm
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ S, ∑ s ∈ S, |c r*c s*((effectivePairCurve r s (radialFourSourceStep k:ℂ)).re-h (r+s+1))| := by
      simp only [mul_sub]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun r _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ r ∈ S, ∑ s ∈ S, |c r*c s| *((radialFourSourceStep k)^2*pairConstant r s) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply pair_value_error r s _ hpos.le hstep
      intro j hj
      exact lt_of_le_of_lt (family_pair_disc S r s hr hs _ hk j hj) (by norm_num)
    _ = _ := by
      unfold familyConstant
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring

end
end CarryDirectAnchor
