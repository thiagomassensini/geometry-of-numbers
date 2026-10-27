import FiniteImaginaryLaw
import MixedRegression

namespace CarryMixedImaginary
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Exact low-order spatial checks, without moments or fitted coefficients. -/
theorem mixed_weights_low_order :
    mixedOrderWeight 0 0=2 ∧ mixedOrderWeight 0 1=9 ∧
    mixedOrderWeight 1 0= -3 ∧ mixedOrderWeight 1 1=4 := by
  norm_num [mixedOrderWeight]

theorem mixed_weight_ne_zero (r s : ℕ) : mixedOrderWeight r s≠0 := by
  rcases le_or_gt r s with he | he
  · exact (mixed_weight_pos he).ne'
  · exact (mixed_weight_neg he).ne

/-- A universal nonnegative spatial weight is already refuted in low order.
This does NOT refute positivity of the signed source or the Hankel forms. -/
theorem not_all_mixed_weights_nonnegative : ¬ ∀ r s : ℕ, 0 ≤ mixedOrderWeight r s := by
  intro he
  have hh := he 1 0
  norm_num [mixedOrderWeight] at hh

/-- Recovery of the previously certified first pair from the arbitrary-order law. -/
theorem first_mixed_from_all_order :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*firstMixedPair k) atTop
      (nhds (2*Complex.I*(h 1:ℂ))) := by
  have he := finite_mixed_scaled_tendsto {0} {0} (fun _ => 1) (fun _ => 1)
  simpa [mixedPair, finiteJetSource, finiteOddJetSource, firstMixedPair,
    imaginaryCoefficient, mixedOrderWeight, mul_assoc, mul_left_comm] using he

/-- Literal individual radial jets, without replacing the original source. -/
theorem mixed_jet_scaled_tendsto (r s : ℕ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*signedPair k
      (radialJetCoefficients k (2*r)) (radialJetCoefficients k (2*s+1))) atTop
      (nhds (Complex.I*(mixedOrderWeight r s:ℂ)*(h (r+s+1):ℂ))) := by
  have he := finite_mixed_scaled_tendsto {r} {s} (fun _ => 1) (fun _ => 1)
  simpa [mixedPair, finiteJetSource, finiteOddJetSource, imaginaryCoefficient, mul_assoc] using he

/-- The coefficient is a difference of TWO original shifted-moment pairings.
This is an algebraic identity, not a positive norm or a new metric. -/
theorem imaginary_coefficient_two_ordered_terms (S T : Finset ℕ) (c d : ℕ → ℝ) :
    imaginaryCoefficient S T c d=
      (∑ r ∈ S, ∑ s ∈ T, c r*(d s*((2*(s:ℝ)+2)*(2*(s:ℝ)+3)/2))*h (r+s+1))-
      (∑ r ∈ S, ∑ s ∈ T, (c r*((2*(r:ℝ)+1)*(2*(r:ℝ)+2)/2))*d s*h (r+s+1)) := by
  unfold imaginaryCoefficient mixedOrderWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Eventual complex orthogonality would erase the coefficient, not merely
its real readout. No nonvanishing of canonical moments is assumed. -/
theorem mixed_orthogonality_forces_coefficient_zero (S T : Finset ℕ) (c d : ℕ → ℝ)
    (hz : ∀ᶠ k : ℕ in atTop, mixedPair S T c d k=0) :
    imaginaryCoefficient S T c d=0 := by
  have hzero : Tendsto (fun k : ℕ => ((k:ℂ)+1)*mixedPair S T c d k) atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hz] with k hk
    simp [hk]
  have he := tendsto_nhds_unique (finite_mixed_scaled_tendsto S T c d) hzero
  have hh := (mul_eq_zero.mp he).resolve_left Complex.I_ne_zero
  exact_mod_cast hh

end
end CarryMixedImaginary
