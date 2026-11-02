import RelativeGate
import OddTrialPositivity
import FifthOddCertificate

namespace CarrySixthRelative
open CarrySelfAdjointOperator CarryDirectAnchor CarryIntegralCertificate CarryVariationalSchur
open CarryCriticalSource CarrySummableRadial CarryOddEnergy CarrySixthOdd
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

def twelveOrders : Finset ℕ := Finset.range 6

def twelveCoeff (i : ℕ) : ℝ := (CarrySixthOdd.trialCoefficient i 5 : ℝ)/(10:ℝ)^18

def twelveSolve : Fin 5 → ℝ := fun i => -twelveCoeff i.val

theorem twelve_coeff_last : twelveCoeff 5 = 1 := by
  norm_num [twelveCoeff,CarrySixthOdd.trialCoefficient,trialCoefficientData]

theorem twelve_old_isUnit : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 5) := by
  exact CarryThetaPattern.odd_source_five_posDef.isUnit

theorem twelve_trialFin_coeff (i : ℕ) (hi : i ∈ twelveOrders) :
    coefficientFromFin (trialFin 5 twelveSolve) i = twelveCoeff i := by
  have hi' : i<6 := Finset.mem_range.mp hi
  interval_cases i <;> norm_num [coefficientFromFin,trialFin,twelveSolve,twelveCoeff,
    CarrySixthOdd.trialCoefficient,trialCoefficientData,Fin.snoc]

theorem twelve_pairing_eq_original_form :
    trialPairing 5 5 = (10:ℝ)^36 * oddCanonicalForm twelveOrders twelveCoeff := by
  unfold trialPairing oddCanonicalForm twelveOrders
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold twelveCoeff
  norm_num
  ring

theorem twelve_pairing_lower : (1:ℝ) < trialPairing 5 5 := by
  have h := mem_trialPairingBox 5 5
  have hh := pos_of_mem (mem_add h (mem_neg (mem_point 1)))
    (show ((trialPairingBox 5 5).add (Box.point 1).neg).positive=true by decide +kernel)
  norm_num at hh
  linarith

theorem twelve_trial_form_lower : (1/(10:ℝ)^36) < oddCanonicalForm twelveOrders twelveCoeff := by
  have h := twelve_pairing_lower
  rw [twelve_pairing_eq_original_form] at h
  norm_num at *
  nlinarith

end
end CarrySixthRelative
