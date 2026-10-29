import CompleteCorrection

namespace CarryQuarticCorrection
open CarrySelfAdjointOperator CarryCriticalTfvd CarryCubicTfvd CarryQuarticTaylor
open Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Only the existing OLD size-two system, with its two original couplings. -/
def oldBlockSolution (m : ℕ → ℝ) : Fin 2 → ℝ :=
  (sourceMomentMatrix m 0 2)⁻¹ *ᵥ sourceMomentCoupling m 0 2

/-- Algebraic orthogonalization needs only invertibility of the old block.
No positivity of the old or new quadratic form is used here. -/
theorem quartic_schur_identity (m : ℕ → ℝ) (hA : IsUnit (sourceMomentMatrix m 0 2)) :
    quarticQuadratic (m 0) (m 1) (m 2) (m 3) (m 4)
      (oldBlockSolution m 1) (oldBlockSolution m 0)=sourceMomentSchur m 0 2 := by
  letI := hA.invertible
  have hv : sourceMomentMatrix m 0 2 *ᵥ oldBlockSolution m=sourceMomentCoupling m 0 2 := by
    dsimp only [oldBlockSolution]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hv0 : m 0*oldBlockSolution m 0+m 1*oldBlockSolution m 1=m 2 := by
    simpa [sourceMomentMatrix,sourceMomentCoupling,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      using congrFun hv (0 : Fin 2)
  have hv1 : m 1*oldBlockSolution m 0+m 2*oldBlockSolution m 1=m 3 := by
    simpa [sourceMomentMatrix,sourceMomentCoupling,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      using congrFun hv (1 : Fin 2)
  have hs : sourceMomentSchur m 0 2=m 4-
      (m 2*oldBlockSolution m 0+m 3*oldBlockSolution m 1) := by
    simp [sourceMomentSchur,sourceMomentCoupling,dotProduct,Fin.sum_univ_two,oldBlockSolution]
  rw [hs]
  unfold quarticQuadratic
  linear_combination (oldBlockSolution m 0)*hv0+(oldBlockSolution m 1)*hv1

def criticalQuarticA : ℝ := oldBlockSolution h 1
def criticalQuarticB : ℝ := oldBlockSolution h 0

theorem critical_quartic_schur (hA : IsUnit (sourceMomentMatrix h 0 2)) :
    canonicalQuarticQuadratic criticalQuarticA criticalQuarticB=sourceMomentSchur h 0 2 := by
  exact quartic_schur_identity h hA

/-- The physical first correction reaches the named Schur, under the OLD
invertibility gate alone. Its sign is still not supplied as a premise. -/
theorem critical_scaled_error_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (hA : IsUnit (sourceMomentMatrix h 0 2)) :
    Tendsto (fun k : ℕ => ((k : ℝ)+1)^2*
      (fullEnergy k (criticalFamily k criticalQuarticA criticalQuarticB)-sourceMomentSchur h 0 2))
      atTop (nhds (quarticCorrection criticalQuarticA criticalQuarticB)) := by
  rw [← critical_quartic_schur hA]
  exact native_scaled_error_limit eta h0 h1 criticalQuarticA criticalQuarticB

theorem critical_scaled_norm_difference_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (hA : IsUnit (sourceMomentMatrix h 0 2)) :
    Tendsto (fun k : ℕ => ((k : ℝ)+1)^2*
      (‖(NativeLaguerre.physicalCompletedFiniteSource k (criticalFamily k criticalQuarticA criticalQuarticB)).1‖^2-
        ‖(NativeLaguerre.physicalCompletedFiniteSource k (criticalFamily k criticalQuarticA criticalQuarticB)).2‖^2-
        2*sourceMomentSchur h 0 2))
      atTop (nhds (2*quarticCorrection criticalQuarticA criticalQuarticB)) := by
  rw [← critical_quartic_schur hA]
  exact native_scaled_norm_difference_limit eta h0 h1 criticalQuarticA criticalQuarticB

theorem critical_full_energy_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (hA : IsUnit (sourceMomentMatrix h 0 2)) :
    Tendsto (fun k : ℕ => fullEnergy k (criticalFamily k criticalQuarticA criticalQuarticB))
      atTop (nhds (sourceMomentSchur h 0 2)) := by
  rw [← critical_quartic_schur hA]
  exact quartic_full_energy_limit eta h0 h1 criticalQuarticA criticalQuarticB

end
end CarryQuarticCorrection
