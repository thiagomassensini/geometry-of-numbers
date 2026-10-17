import CriticalSource
import LimitTower

/-! A positive margin must survive the radial limit. This module states
exactly that obligation; it does not infer it from positive finite samples. -/
namespace CarryCriticalSource
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryReturnCompatibility Filter
open scoped Topology Matrix InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

def HasCriticalMargin (s : Fin 2) (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, ε ≤ criticalBalance s n k

/-- No bound uniform in n or a uniform radial cutoff is required. -/
theorem criticalMargin_iff_pivot (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) :
    HasCriticalMargin s n ↔ 0 < sourceMomentSchur h s.val n := by
  have ht := criticalBalance_tendsto s n hA
  constructor
  · rintro ⟨ε,hε,hb⟩
    have hl := ge_of_tendsto ht hb
    linarith
  · intro hs
    refine ⟨sourceMomentSchur h s.val n,hs,?_⟩
    exact ((tendsto_order.mp ht).1 _ (by linarith)).mono fun _ hk => hk.le

theorem criticalMargin_iff_sourceRemainder (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) :
    HasCriticalMargin s n ↔ 0 < nativeSourceSchurRemainder s.val n := by
  rw [criticalMargin_iff_pivot s n hA, nativeSourceSchurRemainder_eq]
  exact (mul_pos_iff_of_pos_left (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third)).symm

/-- A genuinely negative next pivot obstructs contraction of this finite
return, with an explicit source test. No claim about other candidates. -/
theorem negativePivot_not_eventually_contractive (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef)
    (hs : sourceMomentSchur h s.val n < 0) :
    ¬ (∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k (2*(n+1))‖ ≤ 1) := by
  apply not_eventually_contractive_of_negative_boundary_direction (n+1)
    (criticalCoordinates s n)
  rw [criticalCoordinates_boundary s n hA]
  linarith


/-- Keep the negative Jordan channel: domination is a source estimate,
not a consequence of the positive square-root construction. -/
theorem criticalMargin_iff_jordanGap (s : Fin 2) (n : ℕ) :
    HasCriticalMargin s n ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop,
      ‖radialReturnJordanNegativePort k (2*(n+1)) (criticalIncident s n k)‖^2+ε ≤
        ‖radialReturnJordanPositivePort k (2*(n+1)) (criticalIncident s n k)‖^2 := by
  constructor
  · rintro ⟨ε,hε,hb⟩
    refine ⟨ε,hε,hb.mono ?_⟩
    intro k hk
    rw [criticalBalance_eq_jordan] at hk
    linarith
  · rintro ⟨ε,hε,hb⟩
    refine ⟨ε,hε,hb.mono ?_⟩
    intro k hk
    rw [criticalBalance_eq_jordan]
    linarith

/-- An induction step on the OLD positive prefix, not positivity of the
new prefix supplied as a hidden hypothesis. -/
def AllCriticalMargins : Prop :=
  ∀ (s : Fin 2) (n : ℕ), (sourceMomentMatrix h s.val n).PosDef → HasCriticalMargin s n

theorem allCriticalMargins_matrices (hm : AllCriticalMargins) (s : Fin 2) :
    ∀ n, (sourceMomentMatrix h s.val n).PosDef := by
  intro n
  induction n with
  | zero =>
      apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian h s.val 0)
      intro x hx
      exact (hx (Subsingleton.elim _ _)).elim
  | succ n ih =>
      exact (sourceMomentMatrix_succ_posDef_iff h s.val n ih).mpr
        ((criticalMargin_iff_pivot s n ih).mp (hm s n ih))

theorem allCriticalMargins_iff_sourceRemainders :
    AllCriticalMargins ↔
      ∀ n, 0 < nativeSourceSchurRemainder 0 n ∧ 0 < nativeSourceSchurRemainder 1 n := by
  constructor
  · intro hm n
    constructor
    · exact (criticalMargin_iff_sourceRemainder 0 n
        (allCriticalMargins_matrices hm 0 n)).mp (hm 0 n (allCriticalMargins_matrices hm 0 n))
    · exact (criticalMargin_iff_sourceRemainder 1 n
        (allCriticalMargins_matrices hm 1 n)).mp (hm 1 n (allCriticalMargins_matrices hm 1 n))
  · intro hr s n hA
    apply (criticalMargin_iff_sourceRemainder s n hA).mpr
    fin_cases s
    · exact (hr n).1
    · exact (hr n).2

/-- The existing physical tower can be fed by the source-critical margins.
The family of margins is still the explicit, unresolved premise. -/
theorem allCriticalMargins_returnBounds (hm : AllCriticalMargins) : AllFiniteReturnBounds :=
  allFiniteReturnBounds_of_source_remainders
    (allCriticalMargins_iff_sourceRemainders.mp hm)

end
end CarryCriticalSource
