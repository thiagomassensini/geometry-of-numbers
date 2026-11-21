import CPFormal.Analytic.CpC2OddCorePushforwardTfvd
import Mathlib.Tactic

/-!
Exact C2 finite odd-core connected deficit, evaluated on the ORIGINAL
rational dyadic branch mass with cutoff 60.

This is an arithmetic connected defect. The naive kernel
K(p,q)=a(p)a(q)-a(pq) has individually positive entries but
an INDEFINITE 2x2 matrix. Neither K nor -K is asserted to be the
native completed moment Schur Gram.
-/

namespace CarryWheelNativeSignedGate
open CPFormal.Carry.C2
open CPFormal.Analytic.Cp

theorem mass60_3 : oddCoreTruncatedMass 60 3 = (7/8 : ℚ) := by
  norm_num [oddCoreTruncatedMass, oddCoreMinusDepth, oddCorePlusDepth,
    oddCoreBranchMass, dyadicBranchWeight, Finset.sum_Icc_succ_top]

theorem mass60_5 : oddCoreTruncatedMass 60 5 = (3/4 : ℚ) := by
  norm_num [oddCoreTruncatedMass, oddCoreMinusDepth, oddCorePlusDepth,
    oddCoreBranchMass, dyadicBranchWeight, Finset.sum_Icc_succ_top]

theorem mass60_9 : oddCoreTruncatedMass 60 9 = (1/2 : ℚ) := by
  norm_num [oddCoreTruncatedMass, oddCoreMinusDepth, oddCorePlusDepth,
    oddCoreBranchMass, dyadicBranchWeight, Finset.sum_Icc_succ_top]

theorem mass60_15 : oddCoreTruncatedMass 60 15 = (1/4 : ℚ) := by
  norm_num [oddCoreTruncatedMass, oddCoreMinusDepth, oddCorePlusDepth,
    oddCoreBranchMass, dyadicBranchWeight, Finset.sum_Icc_succ_top]

theorem mass60_25 : oddCoreTruncatedMass 60 25 = (0 : ℚ) := by
  norm_num [oddCoreTruncatedMass, oddCoreMinusDepth, oddCorePlusDepth,
    oddCoreBranchMass, dyadicBranchWeight, Finset.sum_Icc_succ_top]

/-- Original finite multiplicative defect at (p,q)=(3,5). -/
theorem connected60_3_5_eq_neg :
    c2OddCoreConnectedCumulant 60 3 5 = -(13/32 : ℚ) := by
  norm_num [c2OddCoreConnectedCumulant, mass60_3, mass60_5, mass60_15]

def positiveConnectedDefect60 (p q : ℕ) : ℚ :=
  oddCoreTruncatedMass 60 p * oddCoreTruncatedMass 60 q -
    oddCoreTruncatedMass 60 (p*q)

theorem k60_3_3 : positiveConnectedDefect60 3 3 = 17/64 := by
  norm_num [positiveConnectedDefect60, mass60_3, mass60_9]

theorem k60_3_5 : positiveConnectedDefect60 3 5 = 13/32 := by
  norm_num [positiveConnectedDefect60, mass60_3, mass60_5, mass60_15]

theorem k60_5_5 : positiveConnectedDefect60 5 5 = 9/16 := by
  norm_num [positiveConnectedDefect60, mass60_5, mass60_25]

/-- A POSITIVE entrywise, yet NON-PSD, 2x2 connected-defect matrix. -/
theorem naive_connected_defect_matrix_det_negative :
    positiveConnectedDefect60 3 3 * positiveConnectedDefect60 5 5 -
      (positiveConnectedDefect60 3 5)^2 = -(1/64 : ℚ) := by
  rw [k60_3_3, k60_3_5, k60_5_5]
  norm_num

/-- Original dyadic-mass logic, a completely GENERIC conditional
implication. Exact mass doubling + antitonicity are the separate
obligations. This result does not assume a Gram identification. -/
theorem mass_connected_nonpos_of_dyadic_contraction
    (a : ℕ → ℚ)
    (ha_nonneg : ∀ m, 0 ≤ a m)
    (ha_antitone : ∀ {m n}, m ≤ n → a n ≤ a m)
    (ha_double_pos : ∀ m, 0 < a (2*m) → a (2*m) ≤ 2*a m - 1)
    {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    a (p*q) ≤ a p * a q := by
  have hx : 0 ≤ a (p*q) := ha_nonneg _
  by_cases hzero : a (p*q) = 0
  · rw [hzero]
    exact mul_nonneg (ha_nonneg _) (ha_nonneg _)
  have hpos : 0 < a (p*q) := lt_of_le_of_ne hx (Ne.symm hzero)
  have hple : 2*q ≤ p*q := by nlinarith
  have hqle : 2*p ≤ p*q := by nlinarith
  have hpge : a (p*q) ≤ a (2*q) := ha_antitone hple
  have hqge : a (p*q) ≤ a (2*p) := ha_antitone hqle
  have hpcon : a (p*q) ≤ 2*a p-1 :=
    le_trans hqge (ha_double_pos p (lt_of_lt_of_le hpos hqge))
  have hqcon : a (p*q) ≤ 2*a q-1 :=
    le_trans hpge (ha_double_pos q (lt_of_lt_of_le hpos hpge))
  have hap : 0 ≤ a p := ha_nonneg _
  have haq : 0 ≤ a q := ha_nonneg _
  nlinarith [sq_nonneg (a (p*q) - 1),
    mul_nonneg (sub_nonneg.mpr hpcon) (sub_nonneg.mpr hqcon)]

end CarryWheelNativeSignedGate
