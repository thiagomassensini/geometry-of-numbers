import OddPhysicalTwelve
import CarrySelfAdjointOperator.ProjectiveValveCarryEnergyFrontier

namespace CarrySixthOdd
open CarryThetaPattern CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCorrectedGreenPorts CarryReturnCompatibility
open GeometryOfNumbers.Analysis Filter CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem twelve_boundary_margin : ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin 12 → ℂ,
    ε*‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy 12 x :=
  (nativeSourceFiniteBoundaryEnergy_pos_iff_margin 12).mp twelve_boundary_positive

/-- Both signed physical Jordan channels remain present before contraction
is independently supplied. Inputs are arbitrary and independent. -/
theorem twelve_jordan_signed_pairing (k : ℕ) (x y : RadialIncidentSpan k 12) :
    inner ℂ (radialReturnJordanPositivePort k 12 x) (radialReturnJordanPositivePort k 12 y) -
      inner ℂ (radialReturnJordanNegativePort k 12 x) (radialReturnJordanNegativePort k 12 y) =
        inner ℂ x y-inner ℂ (radialReturnTransfer k 12 x) (radialReturnTransfer k 12 y) :=
  radialReturnJordanPorts_pairing k 12 x y

theorem twelve_jordan_ports_eventually : ∀ᶠ k : ℕ in atTop,
    radialReturnJordanPositivePort k 12 = radialReturnEnergyPort k 12 ∧
      radialReturnJordanNegativePort k 12 = 0 := by
  filter_upwards [twelve_return_eventually_contractive] with k hk
  exact ⟨radialReturnJordanPositivePort_eq_energyPort k 12 hk,
    radialReturnJordanNegativePort_eq_zero k 12 hk⟩

/-- Complete geometric comparison, with its original signed four-channel
discrepancy, specialized to twelve independently synthesized source inputs.
No sign or vanishing of the discrepancy is assumed. -/
theorem twelve_complete_source_comparison (M k : ℕ) (c d : Fin 12 → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin 12, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    polarizedSourceBalance k c d r s =
      2*inner ℂ (coisometricSourceSynthesis k c r (fun i => (hstrip i).1))
        (coisometricSourceSynthesis k d s (fun i => (hstrip i).1)) +
      2*Complex.I*coisometricFourChannelBalance k c d r s (fun i => (hstrip i).1) :=
  polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance M k c d r s hstrip

/-- Reuse of the upstream TFVD reconstruction on full ordinary-state
superpositions. GG, GR, RG and RR survive. This is not an identification of
the TFVD analysis metric with the downstream Hankel coordinate verifier. -/
theorem twelve_tfvd_synthesis_four_channels {base : ℕ} (hbase : IsSupported base)
    (v w : Fin 12 → CarryVerticalL2) (c d : Fin 12 → ℂ) :
    let x := ∑ i, c i • v i
    let y := ∑ i, d i • w i
    let q := canonicalBR2CarryAmplitudeRatio base
    let Gx := carryVerticalL2WeightedGreen q (carryWeightedVerticalCenteredBracket q x)
    let Gy := carryVerticalL2WeightedGreen q (carryWeightedVerticalCenteredBracket q y)
    let Rx := carryWeightedVerticalReturn q (canonicalBR2CarryAmplitudeRatio_pos hbase).le
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) (carryWeightedVerticalTrace q x)
    let Ry := carryWeightedVerticalReturn q (canonicalBR2CarryAmplitudeRatio_pos hbase).le
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) (carryWeightedVerticalTrace q y)
    inner ℂ x y = inner ℂ Gx Gy+inner ℂ Gx Ry+inner ℂ Rx Gy+inner ℂ Rx Ry :=
  canonicalCarryTfvd_inner_eq_fourChannel hbase (∑ i, c i • v i) (∑ i, d i • w i)

end
end CarrySixthOdd
