import OddLimit
import SourceSigns
import CriticalOrientation

namespace CarrySourceLaw
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCriticalRelative Filter Topology
open scoped BigOperators Matrix InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

def oddCriticalParameter : ℝ := -h 2/h 1

theorem odd_old_posDef : (sourceMomentMatrix h 1 1).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian _ _ _)
  intro x hx
  have hx0 : x 0 ≠ 0 := by
    intro hz
    apply hx
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi,hz]
  change 0 < x ⬝ᵥ (sourceMomentMatrix h 1 1 *ᵥ x)
  simp only [dotProduct, Matrix.mulVec, sourceMomentMatrix, Fin.sum_univ_one,
    Fin.val_zero, Nat.zero_add]
  nlinarith [source_h1_pos, sq_pos_of_ne_zero hx0]

theorem odd_old_solve :
    ((sourceMomentMatrix h 1 1)⁻¹ *ᵥ sourceMomentCoupling h 1 1) 0 = h 2/h 1 := by
  let u := (sourceMomentMatrix h 1 1)⁻¹ *ᵥ sourceMomentCoupling h 1 1
  letI := odd_old_posDef.isUnit.invertible
  have hu : sourceMomentMatrix h 1 1 *ᵥ u = sourceMomentCoupling h 1 1 := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hu0 := congrFun hu 0
  norm_num [Matrix.mulVec, dotProduct, sourceMomentMatrix, sourceMomentCoupling,
    Fin.sum_univ_one] at hu0
  apply (eq_div_iff source_h1_pos.ne').mpr
  change u 0*h 1 = h 2
  linarith

theorem odd_critical_coordinates : criticalCoordinates 1 1 = oddJet oddCriticalParameter := by
  funext i
  fin_cases i
  all_goals
    norm_num [criticalCoordinates, parityCoordinates, criticalCoefficients,
      nativeSourceBoundaryFromParity, oddJet, oddCriticalParameter, Fin.snoc,
      Matrix.mulVec, Matrix.diagonal, sourceMomentMatrix, sourceMomentCoupling, dotProduct,
      Fin.sum_univ_one]
  all_goals push_cast
  all_goals ring

theorem odd_critical_balance_exact (k : ℕ) :
    criticalBalance 1 1 k = oddBalance oddCriticalParameter k := by
  rw [criticalBalance_eq_storage]
  simp only [criticalInput, odd_critical_coordinates, oddBalance]

theorem odd_pivot_formula : sourceMomentSchur h 1 1 = h 3-(h 2)^2/h 1 := by
  unfold sourceMomentSchur
  simp only [Nat.mul_one, Nat.reduceAdd, dotProduct, Fin.sum_univ_one,
    sourceMomentCoupling, Fin.val_zero, Nat.zero_add, odd_old_solve]
  ring

theorem odd_constant_eq_pivot :
    oddConstant oddCriticalParameter = 2*sourceMomentSchur h 1 1 := by
  rw [odd_pivot_formula]
  unfold oddConstant oddCriticalParameter
  field_simp [source_h1_pos.ne']
  ring

theorem odd_correction_formula : oddCorrection oddCriticalParameter =
    (-10*(h 2)^3+168*h 1*h 2*h 3-60*(h 1)^2*h 4)/(h 1)^2 := by
  unfold oddCorrection oddCriticalParameter
  field_simp [source_h1_pos.ne']
  ring

theorem odd_correction_pos : 0 < oddCorrection oddCriticalParameter := by
  rw [odd_correction_formula]
  exact div_pos source_odd_correction_pos (sq_pos_of_pos source_h1_pos)

theorem odd_pivot_source_pos : 0 < sourceMomentSchur h 1 1 := by
  rw [odd_pivot_formula]
  apply sub_pos.mpr
  apply (div_lt_iff₀ source_h1_pos).mpr
  nlinarith [source_odd_pivot_margin_pos]

/-- In the next tested parity the actual physical balance approaches its
limit from ABOVE. This is not a negative pivot or a source modification. -/
theorem odd_critical_correction_tendsto :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2 *
      (criticalBalance 1 1 k-2*sourceMomentSchur h 1 1))
      atTop (nhds (oddCorrection oddCriticalParameter)) := by
  simp_rw [odd_critical_balance_exact, ← odd_constant_eq_pivot]
  exact odd_balance_correction_tendsto oddCriticalParameter

theorem odd_critical_eventually_above :
    ∀ᶠ k : ℕ in atTop, 2*sourceMomentSchur h 1 1 < criticalBalance 1 1 k := by
  have hp := (tendsto_order.mp odd_critical_correction_tendsto).1 0 odd_correction_pos
  filter_upwards [hp] with k hk
  have hc : 0 < ((k:ℝ)+1)^2 := by positivity
  nlinarith

/-- Refutes ONLY a universal below-limit law for these original critical
balances. It does not refute their eventual positivity or all-order Hankel. -/
theorem no_universal_critical_approach_from_below :
    ¬ (∀ s : Fin 2, ∀ n : ℕ, ∀ᶠ k : ℕ in atTop,
      criticalBalance s n k < 2*sourceMomentSchur h s.val n) := by
  intro hall
  obtain ⟨k,hk,hk'⟩ := ((hall 1 1).and odd_critical_eventually_above).exists
  exact (lt_asymm hk hk')

theorem two_critical_corrections_opposite :
    CarryCriticalMixed.balanceCorrection CarryCriticalMixed.secondCriticalParameter < 0 ∧
      0 < oddCorrection oddCriticalParameter :=
  ⟨CarryCriticalMixed.second_correction_neg, odd_correction_pos⟩

/-- The earlier even source certificate also refutes a universal above-limit
law. The two NO-GOs concern only a common orientation of finite corrections. -/
theorem no_universal_critical_approach_from_above :
    ¬ (∀ s : Fin 2, ∀ n : ℕ, ∀ᶠ k : ℕ in atTop,
      2*sourceMomentSchur h s.val n < criticalBalance s n k) := by
  intro hall
  have hb := CarryCriticalMixed.second_critical_between_zero_and_limit
  obtain ⟨k,hk,hk'⟩ := ((hall 0 1).and hb).exists
  exact lt_asymm hk hk'.2

end
end CarrySourceLaw
