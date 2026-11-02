import AllOrderTail
import OddFiniteEnergy

namespace CarrySummableRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryAllOrderTail
open CarryMovingRadial NativeLaguerre CarryCommutatorControl
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The precise finite address cutoff required by the original odd stencils. -/
def oddGridSize (S : Finset ℕ) : ℕ := 2*S.sup id+2

theorem odd_grid_size_pos (S : Finset ℕ) : 0 < oddGridSize S := by
  unfold oddGridSize
  omega

/-- Concrete cutoff: all source addresses lie strictly inside the certified
quarter disc at every grid index at least this large. -/
def oddGridCutoff (S : Finset ℕ) : ℕ := 4*oddGridSize S

theorem odd_grid_cutoff_regular (S : Finset ℕ) (k : ℕ) (hk : oddGridCutoff S ≤ k) :
    (oddGridSize S : ℝ) * |radialFourSourceStep k| < 1/4 := by
  have hn : (0:ℝ) < oddGridSize S := by exact_mod_cast odd_grid_size_pos S
  have hk' : 4*(oddGridSize S : ℝ) ≤ k := by
    exact_mod_cast hk
  have hp : (0:ℝ) < (k:ℝ)+1 := by positivity
  rw [abs_of_nonneg (by unfold radialFourSourceStep; positivity)]
  unfold radialFourSourceStep
  rw [mul_inv_lt_iff₀ hp]
  linarith

/-- At every explicit regular step, the full original two-leg energy is the
sum of both ordered original pairings, with every cross term preserved. -/
theorem finite_odd_energy_pairing_at_regular (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ)
    (hk : (oddGridSize S : ℝ) * |radialFourSourceStep k| < 1/4) :
    fullEnergy k (finiteOddJetSource S c k)=
      ∑ r ∈ S, ∑ s ∈ S, c r*c s*(normalizedOddPair r s k).re := by
  let N := oddGridSize S
  have hc : (finiteOddJetSource S c k).support ⊆ Finset.range N := by
    exact finite_odd_source_support S c k
  have hF (j : Fin N) : completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 := by
    rw [← point_at_grid]
    exact (finite_radial_regular N (radialFourSourceStep k) hk j).1
  have hP (j : Fin N) : completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 := by
    rw [← point_at_grid]
    exact (finite_radial_regular N (radialFourSourceStep k) hk j).2
  have hd (j : ℕ) (hj : j<N) := radial_weight_difference k j (hF ⟨j,hj⟩) (hP ⟨j,hj⟩)
  have he := full_response_flux k (finiteOddJetSource S c k) hc hF hd
  have hw : responseWeight k=(fun j => Complex.I*responseSamples (radialStep k) j) := by
    funext j
    exact response_radial_readout k j
  rw [hw] at he
  change fullEnergy k (finiteOddJetSource S c k)=
    2*((k:ℝ)+1)*(kernel (fun j => Complex.I*responseSamples (radialStep k) j)
      (finiteOddJetSource S c k) (finiteOddJetSource S c k)).im at he
  rw [kernel_scale] at he
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at he
  have hp := congrArg Complex.re (finite_odd_source_pairing S c k)
  simp [Complex.mul_re, Complex.mul_im] at hp
  rw [he]
  linear_combination hp

theorem finite_odd_energy_pairing_at_cutoff (S : Finset ℕ) (c : ℕ → ℝ) (k : ℕ)
    (hk : oddGridCutoff S ≤ k) :
    fullEnergy k (finiteOddJetSource S c k)=
      ∑ r ∈ S, ∑ s ∈ S, c r*c s*(normalizedOddPair r s k).re :=
  finite_odd_energy_pairing_at_regular S c k (odd_grid_cutoff_regular S k hk)

end
end CarrySummableRadial
