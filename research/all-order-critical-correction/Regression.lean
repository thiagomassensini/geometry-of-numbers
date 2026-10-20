import CriticalCorrection

/-! Original-source regression canaries: fixed normalization, the two
previous finite families, and a new within-sector orientation check.
These finite source signs are NOT premises of the all-order rate theorem. -/
namespace CarryAllOrderCorrection
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCriticalRelative CarrySourceLaw CarryCriticalMixed
open CarryIntegralCertificate Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 65536

theorem criticalCoefficients_empty (s : Fin 2) : criticalCoefficients s 0 = fun _ => 1 := by
  funext i
  fin_cases i
  simp [criticalCoefficients,Fin.snoc]

theorem empty_prefix_isUnit (s : Fin 2) : IsUnit (sourceMomentMatrix CarryCriticalSource.h s.val 0) := by
  have he : sourceMomentMatrix CarryCriticalSource.h s.val 0 = 1 := by
    ext i
    exact Fin.elim0 i
  rw [he]
  exact isUnit_one

theorem first_even_correction : criticalCorrection 0 0 = -2*canonicalCompletedNativeLogDerivativeMoment 1 := by
  unfold criticalCorrection
  rw [criticalCoefficients_empty]
  obtain ⟨h00,_,_,_,_,_⟩ := correctionWeight_canaries
  norm_num [canonicalCorrection,Fin.sum_univ_one,h00]

theorem first_odd_correction : criticalCorrection 1 0 = -10*canonicalCompletedNativeLogDerivativeMoment 2 := by
  unfold criticalCorrection
  rw [criticalCoefficients_empty]
  obtain ⟨_,_,_,h11,_,_⟩ := correctionWeight_canaries
  norm_num [canonicalCorrection,Fin.sum_univ_one,h11]
  ring

/-- First odd correction, derived from the GENERAL law on the actual source. -/
theorem first_odd_second_correction :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2 *
      (criticalBalance 1 0 k-2*sourceMomentSchur CarryCriticalSource.h 1 0))
      atTop (nhds (-10*canonicalCompletedNativeLogDerivativeMoment 2)) := by
  simpa only [first_odd_correction,Fin.val_one] using critical_second_correction 1 0 (empty_prefix_isUnit 1)

theorem source_h2_positive : 0 < canonicalCompletedNativeLogDerivativeMoment 2 := by
  apply pos_of_mem (mem_logMomentBox material_theta_integral_input 2)
  decide +kernel

theorem first_odd_correction_neg : criticalCorrection 1 0 < 0 := by
  rw [first_odd_correction]
  nlinarith [source_h2_positive]

theorem first_odd_eventually_below :
    ∀ᶠ k : ℕ in atTop, criticalBalance 1 0 k < 2*sourceMomentSchur CarryCriticalSource.h 1 0 :=
  critical_eventually_below_of_correction_neg 1 0 (empty_prefix_isUnit 1) first_odd_correction_neg

theorem even_two_coefficients : criticalCoefficients 0 1 = ![secondCriticalParameter,1] := by
  funext i
  fin_cases i
  all_goals norm_num [criticalCoefficients,Fin.snoc,Fin.castLT,secondCriticalParameter,Matrix.mulVec,
    Matrix.diagonal,sourceMomentMatrix,sourceMomentCoupling,dotProduct,Fin.sum_univ_one]
  all_goals ring

theorem odd_two_coefficients : criticalCoefficients 1 1 = ![oddCriticalParameter,1] := by
  funext i
  fin_cases i
  all_goals norm_num [criticalCoefficients,Fin.snoc,Fin.castLT,oddCriticalParameter,Matrix.mulVec,
    Matrix.diagonal,sourceMomentMatrix,sourceMomentCoupling,dotProduct,Fin.sum_univ_one]
  all_goals ring

theorem even_two_correction_matches : criticalCorrection 0 1 = balanceCorrection secondCriticalParameter := by
  unfold criticalCorrection
  rw [even_two_coefficients]
  exact canonicalCorrection_even_two secondCriticalParameter

theorem odd_two_correction_matches : criticalCorrection 1 1 = oddCorrection oddCriticalParameter := by
  unfold criticalCorrection
  rw [odd_two_coefficients]
  exact canonicalCorrection_odd_two oddCriticalParameter

/-- Independent reproduction of the two prior asymptotic laws from the new
arbitrary-dimension theorem. No old asymptotic proof is used. -/
theorem even_two_law_from_general :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2 *
      (criticalBalance 0 1 k-2*sourceMomentSchur CarryCriticalSource.h 0 1))
      atTop (nhds (balanceCorrection secondCriticalParameter)) := by
  simpa only [even_two_correction_matches,Fin.val_zero] using
    critical_second_correction 0 1 second_old_posDef.isUnit

theorem odd_two_law_from_general :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2 *
      (criticalBalance 1 1 k-2*sourceMomentSchur CarryCriticalSource.h 1 1))
      atTop (nhds (oddCorrection oddCriticalParameter)) := by
  simpa only [odd_two_correction_matches,Fin.val_one] using
    critical_second_correction 1 1 odd_old_posDef.isUnit

/-- Even the parity label does not determine the orientation: the first two
critical ODD directions have opposite source-certified corrections. -/
theorem odd_sector_opposite_corrections :
    criticalCorrection 1 0 < 0 ∧ 0 < criticalCorrection 1 1 := by
  rw [odd_two_correction_matches]
  exact ⟨first_odd_correction_neg,odd_correction_pos⟩

end
end CarryAllOrderCorrection
