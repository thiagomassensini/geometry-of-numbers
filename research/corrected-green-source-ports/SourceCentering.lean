import PrimeClockGreenTransport
import CarrySelfAdjointOperator.CompletedNativeChiralReturnJordanEnergy

/-! Center the actual chiral source ports with coefficients of the completed
material response. The kernels below are existing Green observations, not
definitions of a Hilbert metric. No global Hilbert derivatives are used. -/
namespace CarryCorrectedGreenPorts
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CarryMaterialResponseComparison CarryMaterialThirdNullComparison
open CarryMaterialMixedSchurComparison CarryMaterialPositiveResidualComparison
open CarrySelfAdjointOperator.ChiralReturn
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Forced by the scalar source axis, after full material synthesis. -/
def sourceCenterWeight (p : ℕ) : ℂ :=
  carryMaterialTaylorShift (p+1) 0 / (carryMaterialResponseScale : ℂ)

theorem sourceCenterWeight_eq_coefficient (p : ℕ) :
    sourceCenterWeight p = completedNativeGreenResponseTaylorCoefficient (p+1) /
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [sourceCenterWeight, material_taylor_shift_center, material_scale_eq]

theorem sourceCenterWeight_conj (p : ℕ) :
    conj (sourceCenterWeight p) = sourceCenterWeight p := by
  simp only [sourceCenterWeight, map_div₀, material_taylor_shift_conj,
    Complex.conj_ofReal]

theorem sourceCenterWeight_zero : sourceCenterWeight 0 = 1 := by
  rw [sourceCenterWeight_eq_coefficient]
  change completedNativeGreenResponseTaylorCoefficient (2*0+1) /
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) = 1
  rw [completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  exact div_self (show (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) ≠ 0 from
    by exact_mod_cast canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne')

theorem sourceCenterWeight_one : sourceCenterWeight 1 = 0 := by
  rw [sourceCenterWeight_eq_coefficient]
  simp [completedNativeGreenResponseTaylorCoefficient_even_eq_zero 1]

/-- Central extraction on a GIVEN source-derived port sequence. This is
ordinary vector subtraction in its original Cauchy Hilbert space. -/
def centerPort {H : Type*} [AddCommGroup H] [Module ℂ H]
    (v : ℕ → H) (p : ℕ) : H := v p - sourceCenterWeight p • v 0

theorem centerPort_zero {H : Type*} [AddCommGroup H] [Module ℂ H]
    (v : ℕ → H) : centerPort v 0 = 0 := by
  simp [centerPort, sourceCenterWeight_zero]

theorem centerPort_pairing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℕ → H) (p q : ℕ) :
    inner ℂ (centerPort v p) (centerPort v q) =
      inner ℂ (v p) (v q) - sourceCenterWeight q * inner ℂ (v p) (v 0) -
      conj (sourceCenterWeight p) * inner ℂ (v 0) (v q) +
      conj (sourceCenterWeight p) * sourceCenterWeight q * inner ℂ (v 0) (v 0) := by
  simp only [centerPort, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right]
  ring

/-- The central Schur identity is DERIVED from the actual residual jets.
Every ordered coefficient comes from the completed response. -/
theorem centered_coefficient_eq_residual (p q : ℕ) :
    polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment p q -
      sourceCenterWeight q *
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment p 0 -
      conj (sourceCenterWeight p) *
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment 0 q +
      conj (sourceCenterWeight p) * sourceCenterWeight q *
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment 0 0 =
      carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) p q := by
  rw [material_residual_complex_jet_source, sourceCenterWeight_conj]
  simp_rw [← completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized]
  rw [sourceCenterWeight_eq_coefficient, sourceCenterWeight_eq_coefficient]
  have h0 := canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have hc : (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) ≠ 0 := by exact_mod_cast h0
  simp only [Nat.add_zero, Nat.zero_add]
  rw [completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0]
  field_simp
  ring

/-- Actual finite forward-difference source coefficients from the existing
chiral construction, with only the forced central extraction added. -/
def residualPositiveJordanJet (k N : ℕ) (a : Fin (N+1)) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialReturnJordanPositiveJet k (N+1) a -
    sourceCenterWeight a.val • radialReturnJordanPositiveJet k (N+1) 0

def residualNegativeJordanJet (k N : ℕ) (a : Fin (N+1)) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialReturnJordanNegativeJet k (N+1) a -
    sourceCenterWeight a.val • radialReturnJordanNegativeJet k (N+1) 0

/-- No positivity is assumed: BOTH complete channels converge as a signed
pairing to the corrected material residual, at every finite order. -/
theorem residualJordan_pairing_tendsto (N : ℕ) (a b : Fin (N+1)) :
    Tendsto (fun k =>
      inner ℂ (residualPositiveJordanJet k N a) (residualPositiveJordanJet k N b) -
      inner ℂ (residualNegativeJordanJet k N a) (residualNegativeJordanJet k N b)) atTop
      (𝓝 (carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) a.val b.val)) := by
  have h (i j : Fin (N+1)) : Tendsto (fun k =>
      inner ℂ (radialReturnJordanPositiveJet k (N+1) i) (radialReturnJordanPositiveJet k (N+1) j) -
      inner ℂ (radialReturnJordanNegativeJet k (N+1) i) (radialReturnJordanNegativeJet k (N+1) j))
      atTop (𝓝 (polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment i.val j.val)) := by
    simp_rw [radialReturnJordanJets_pairing]
    exact projectiveChiralDifferenceJet_pairing_tendsto_coefficient i.val j.val
  have ht := (((h a b).sub ((h a 0).const_mul (sourceCenterWeight b.val))).sub
    ((h 0 b).const_mul (conj (sourceCenterWeight a.val)))).add
      ((h 0 0).const_mul (conj (sourceCenterWeight a.val)*sourceCenterWeight b.val))
  simp only [Fin.val_zero] at ht
  rw [centered_coefficient_eq_residual] at ht
  convert ht using 1
  ext k
  simp only [residualPositiveJordanJet, residualNegativeJordanJet,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  ring

/-- This is the confluent observation of the FULL physical Green difference
from the valve ledger, including its hidden complement. Its row germs were
proved upstream; no division by a vanishing separation is made here. -/
theorem correctedGreenJordan_pairing_tendsto (eta : ℝ) (heta : eta ≠ 0)
    (N : ℕ) (a b : Fin (N+1)) :
    Tendsto (fun k =>
      inner ℂ (residualPositiveJordanJet k N a) (residualPositiveJordanJet k N b) -
      inner ℂ (residualNegativeJordanJet k N a) (residualNegativeJordanJet k N b)) atTop
      (𝓝 (carryValveConfluentJet eta a.val b.val)) := by
  rw [material_valve_confluent_jet eta heta]
  exact residualJordan_pairing_tendsto N a b

end
end CarryCorrectedGreenPorts
