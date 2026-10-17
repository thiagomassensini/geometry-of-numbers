import IntegralInputChecks
import FullSourceBoxes
import NumericalPivotCheck

namespace CarryIntegralCertificate
open CarrySelfAdjointOperator GeometryOfNumbers.Analysis MeasureTheory
open CarryMaterialFourthPivotComparison
open scoped Matrix
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem momentInputBox tabledFullThetaMomentBox

/-- Unconditional membership of each genuine theta integral in the source rectangle.
For unused orders the enclosure is explicitly `all`. -/
theorem material_theta_integral_input (n : ℕ) :
    (momentInputBox n).Mem (completedNativeThetaTailMoment (2*n)) := by
  unfold momentInputBox
  split
  next hn =>
    apply mem_of_contained (mem_tabledFullThetaMomentBox (2*n) (by omega))
    exact integral_input_checks ⟨n,hn⟩
  next _ => simp only [Box.Mem]

/-- Quantitative enclosure obtained from the genuine infinite source integrals. -/
theorem material_fourth_pivot_bounds_integral :
    (16/10^27:ℝ) < carryMaterialFourthPivot ∧ carryMaterialFourthPivot < (17/10^27:ℝ) :=
  material_fourth_bounds_of_integral_inputs material_theta_integral_input

/-- The fourth even material pivot is strictly positive, with no source-box
hypothesis. All source integrals and all infinite tails are included. -/
theorem material_fourth_pivot_pos_integral : 0 < carryMaterialFourthPivot :=
  material_fourth_positive_of_integral_inputs material_theta_integral_input

theorem material_fourth_block_posDef_integral :
    Matrix.PosDef (fun i j : Fin 4 => carryMaterialEvenPairing i j) :=
  material_fourth_block_posDef_iff.mpr material_fourth_pivot_pos_integral

theorem material_fourth_critical_positive_integral :
    0 < carryPairingBilinear carryMaterialEvenPairing 4
      carryMaterialFourthCritical carryMaterialFourthCritical := by
  rw [material_fourth_critical_energy]
  exact material_fourth_pivot_pos_integral

/-- The source obligation itself, including the signed weight on the entire half-line. -/
theorem material_fourth_theta_integral_gate :
    -4*(Nat.factorial 18:ℝ)*material_fourth_characteristic_ceiling <
      (∫ u in Set.Ioi (0:ℝ), (1224*u^16-u^18)*XiThetaCosine.thetaTail u) := by
  rw [material_fourth_theta_balance_integral]
  exact material_fourth_pivot_pos_iff_theta_balance.mp material_fourth_pivot_pos_integral

theorem material_fourth_cholesky_integral :
    carryMaterialEvenCholesky 4*(carryMaterialEvenCholesky 4)ᵀ =
      (fun i j : Fin 4 => carryMaterialEvenPairing i j) :=
  material_fourth_cholesky_of_source_estimate
    (material_fourth_pivot_pos_iff_characteristic.mp material_fourth_pivot_pos_integral)

end CarryIntegralCertificate
