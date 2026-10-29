import MixedRayLeading
import MixedPairing

namespace CarryMixedImaginary
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- All independent pairs of original finite radial jets, including both orders. -/
theorem finite_mixed_kernel_pairing (S T : Finset ℕ) (c d : ℕ → ℝ) (k : ℕ) :
    ((k:ℂ)+1)^2*
      (kernel (responseSamples (radialStep k)) (finiteJetSource S c k) (finiteOddJetSource T d k)-
       kernel (responseSamples (radialStep k)) (finiteOddJetSource T d k) (finiteJetSource S c k))=
      ∑ r ∈ S, ∑ s ∈ T, (c r:ℂ)*(d s:ℂ)*normalizedMixedRay r s k := by
  rw [finite_source_profile, finite_odd_source_profile, kernel_sum_inputs, kernel_sum_inputs]
  rw [Finset.sum_comm (s:=T) (t:=S)]
  simp only [kernel_scale_inputs, map_mul, map_pow, map_add, map_one, map_natCast, Complex.conj_ofReal]
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  have he := mixed_profile_phase (responseSamples (radialStep k)) r s
  unfold normalizedMixedRay
  rw [show 2*(r+s+1)+1=2*r+(2*s+1)+2 by omega, pow_add, pow_add]
  linear_combination (c r:ℂ)*(d s:ℂ)*((k:ℂ)+1)^2*
    ((k:ℂ)+1)^(2*r)*((k:ℂ)+1)^(2*s+1)*he

/-- Exact eventual finite-source bridge, AFTER complete complex synthesis. -/
theorem finite_mixed_pairing (S T : Finset ℕ) (c d : ℕ → ℝ) :
    ∀ᶠ k : ℕ in atTop, ((k:ℂ)+1)*mixedPair S T c d k=
      ∑ r ∈ S, ∑ s ∈ T, (c r:ℂ)*(d s:ℂ)*normalizedMixedRay r s k := by
  filter_upwards [mixed_pair_exact S T c d] with k hk
  rw [hk, ← mul_assoc, ← pow_two, finite_mixed_kernel_pairing]

/-- Literal original shifted-moment bilinear coefficient with spatial weights. -/
def imaginaryCoefficient (S T : Finset ℕ) (c d : ℕ → ℝ) : ℝ :=
  ∑ r ∈ S, ∑ s ∈ T, c r*d s*mixedOrderWeight r s*h (r+s+1)

/-- Main all-order law for two independent finite inputs of the SAME source. -/
theorem finite_mixed_scaled_tendsto (S T : Finset ℕ) (c d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*mixedPair S T c d k) atTop
      (nhds (Complex.I*(imaginaryCoefficient S T c d:ℂ))) := by
  have hlim := tendsto_finsetSum S (fun r _ => tendsto_finsetSum T (fun s _ =>
    (tendsto_const_nhds (x:=(c r:ℂ)*(d s:ℂ))).mul (normalized_mixed_tendsto r s)))
  have he : (∑ r ∈ S, ∑ s ∈ T, (c r:ℂ)*(d s:ℂ)*
      (Complex.I*mixedSlope r s*(h (r+s+1):ℂ)))=
      Complex.I*(imaginaryCoefficient S T c d:ℂ) := by
    unfold imaginaryCoefficient
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [mixed_slope_eq_weight]
    ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [finite_mixed_pairing S T c d] with k hk
  exact hk.symm

/-- Final imaginary readout only after the full complex limit has been proved. -/
theorem finite_mixed_imaginary_tendsto (S T : Finset ℕ) (c d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)*(mixedPair S T c d k).im) atTop
      (nhds (imaginaryCoefficient S T c d)) := by
  have he := Complex.continuous_im.continuousAt.tendsto.comp
    (finite_mixed_scaled_tendsto S T c d)
  simpa [Function.comp_def, Complex.mul_im] using he

/-- Complete complex Green/boundary/remainder recomposition, with both
ordered correction terms retained literally. -/
def mixedGreenPair (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S T : Finset ℕ) (c d : ℕ → ℝ) (k : ℕ) : ℂ :=
  canonicalCompletedNativeProjectiveChiralForm
    (completedSourceParts eta h0 h1 k (finiteJetSource S c k) 0+
      completedSourceParts eta h0 h1 k (finiteJetSource S c k) 1)
    (completedSourceParts eta h0 h1 k (finiteOddJetSource T d k) 0+
      completedSourceParts eta h0 h1 k (finiteOddJetSource T d k) 1)+
  (canonicalCompletedNativeProjectiveChiralForm
    (completedSourceParts eta h0 h1 k (finiteJetSource S c k) 2)
    (physicalCompletedFiniteSource k (finiteOddJetSource T d k))+
   canonicalCompletedNativeProjectiveChiralForm
    (physicalCompletedFiniteSource k (finiteJetSource S c k))
    (completedSourceParts eta h0 h1 k (finiteOddJetSource T d k) 2))

theorem finite_mixed_green_scaled_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (S T : Finset ℕ) (c d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*mixedGreenPair eta h0 h1 S T c d k) atTop
      (nhds (Complex.I*(imaginaryCoefficient S T c d:ℂ))) := by
  apply (finite_mixed_scaled_tendsto S T c d).congr'
  filter_upwards [mixed_pair_green_recomposition eta h0 h1 S T c d] with k hk
  exact congrArg (fun z : ℂ => ((k:ℂ)+1)*z) hk

end
end CarryMixedImaginary
