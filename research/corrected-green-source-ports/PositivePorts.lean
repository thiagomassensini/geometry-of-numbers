import SourceCentering

/-! The old positive physical energy port, centered by the actual scalar
source. Seven sources are unconditional; arbitrary order retains the precise
return bound as an open premise. Gram limits are not vector limits. -/
namespace CarryCorrectedGreenPorts
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CarrySelfAdjointOperator.ChiralReturn
open CarryMaterialMixedSchurComparison CarryMaterialThirdNullComparison
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Source/return defect square root from the existing incident Hilbert
space. This does not factor a desired moment matrix. -/
def residualEnergyJet (k N : ℕ) (a : Fin (N+1)) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialReturnEnergyJet k (N+1) a -
    sourceCenterWeight a.val • radialReturnEnergyJet k (N+1) 0

theorem residualEnergyJet_zero (k N : ℕ) : residualEnergyJet k N 0 = 0 := by
  simp [residualEnergyJet, sourceCenterWeight_zero]

/-- Equality of FULL polarized balances, including all four ordered central
crosses. The contraction estimate is on the ACTUAL source return. -/
theorem residualEnergyJet_pairing_of_contractive (k N : ℕ)
    (hk : ‖radialReturnTransfer k (N+1)‖ ≤ 1) (a b : Fin (N+1)) :
    inner ℂ (residualEnergyJet k N a) (residualEnergyJet k N b) =
      inner ℂ (residualPositiveJordanJet k N a) (residualPositiveJordanJet k N b) -
        inner ℂ (residualNegativeJordanJet k N a) (residualNegativeJordanJet k N b) := by
  simp only [residualEnergyJet, residualPositiveJordanJet, residualNegativeJordanJet,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  simp_rw [radialReturnEnergyJet_gram k (N+1) hk,
    ← radialReturnJordanJets_pairing k (N+1)]
  ring

/-- Arbitrary finite order, conditional ONLY on the geometric return bound.
No positivity of moments, desired Gram identity or vector limit is assumed. -/
theorem residualEnergyJet_pairing_tendsto_of_contractive (N : ℕ)
    (hc : ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k (N+1)‖ ≤ 1)
    (a b : Fin (N+1)) :
    Tendsto (fun k => inner ℂ (residualEnergyJet k N a) (residualEnergyJet k N b)) atTop
      (𝓝 (carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) a.val b.val)) := by
  apply (residualJordan_pairing_tendsto N a b).congr'
  filter_upwards [hc] with k hk
  exact (residualEnergyJet_pairing_of_contractive k N hk a b).symm

/-- Seven actual source samples: unconditional POSITIVE inner products
converge to all entries of the corrected residual jet block, orders 0..6. -/
theorem residualEnergyJet_seven_pairing_tendsto (a b : Fin 7) :
    Tendsto (fun k => inner ℂ (residualEnergyJet k 6 a) (residualEnergyJet k 6 b)) atTop
      (𝓝 (carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) a.val b.val)) :=
  residualEnergyJet_pairing_tendsto_of_contractive 6
    radialReturnTransfer_seven_eventually_norm_le_one a b

/-- The destination is the confluent FULL physical Green difference from
the valve, whose hidden complement was preserved before readout. -/
theorem correctedGreen_seven_positive_pairing_tendsto
    (eta : ℝ) (heta : eta ≠ 0) (a b : Fin 7) :
    Tendsto (fun k => inner ℂ (residualEnergyJet k 6 a) (residualEnergyJet k 6 b)) atTop
      (𝓝 (carryValveConfluentJet eta a.val b.val)) := by
  rw [material_valve_confluent_jet eta heta]
  exact residualEnergyJet_seven_pairing_tendsto a b

/-- No imaginary residual survives at the canonical limit. This is obtained
after complex polarization and scalar source regularity, not by deleting a
quadrature at finite cutoff. -/
theorem residualJet_eq_real (p q : ℕ) :
    (carryMaterialResidualJet p q : ℂ) =
      carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) p q := by
  apply Complex.conj_eq_iff_re.mp
  rw [material_residual_complex_jet_source]
  have hc (n : ℕ) : conj (completedNativeGreenResponseTaylorCoefficient n) =
      completedNativeGreenResponseTaylorCoefficient n := by
    rw [← material_taylor_shift_center]
    exact material_taylor_shift_conj n 0
  simp only [map_sub, map_mul, map_div₀, Complex.conj_ofReal, hc]

theorem residualEnergyJet_seven_real_pairing_tendsto (a b : Fin 7) :
    Tendsto (fun k => (inner ℂ (residualEnergyJet k 6 a) (residualEnergyJet k 6 b)).re)
      atTop (𝓝 (carryMaterialResidualJet a.val b.val)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (residualEnergyJet_seven_pairing_tendsto a b)
  exact h

theorem residualEnergyJet_seven_imaginary_pairing_tendsto (a b : Fin 7) :
    Tendsto (fun k => (inner ℂ (residualEnergyJet k 6 a) (residualEnergyJet k 6 b)).im)
      atTop (𝓝 0) := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp
    (residualEnergyJet_seven_pairing_tendsto a b)
  rw [← residualJet_eq_real] at h
  simpa only [Function.comp_def, Complex.ofReal_im] using h

/-- The inherited real metric and its J-pairing retain BOTH quadratures.
Multiplication by i is the existing real-plane rotation. -/
theorem positivePort_rotation_pairing (k N : ℕ) (a b : Fin (N+1)) :
    (inner ℂ (residualEnergyJet k N a) (Complex.I • residualEnergyJet k N b)).re =
      -(inner ℂ (residualEnergyJet k N a) (residualEnergyJet k N b)).im := by
  rw [inner_smul_right]
  simp [Complex.mul_re]

/-- The genuine first residual jet calibrates to h1 IN THE LIMIT. This is
not the old ordinary physical central-clock norm that failed calibration. -/
theorem residualEnergyJet_first_norm_sq_tendsto :
    Tendsto (fun k => ‖residualEnergyJet k 6 1‖^2) atTop
      (𝓝 (canonicalCompletedNativeLogDerivativeMoment 1)) := by
  have h := residualEnergyJet_seven_real_pairing_tendsto 1 1
  norm_num only [Fin.val_one] at h
  rw [show carryMaterialResidualJet 1 1 = canonicalCompletedNativeLogDerivativeMoment 1 from
    material_residual_jet_odd_odd 0 0] at h
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h

end
end CarryCorrectedGreenPorts
