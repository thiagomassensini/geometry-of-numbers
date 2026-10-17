import NextSourceGate
import PolarizedCritical

namespace CarryCriticalSource
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn Filter
open scoped Topology InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem initial_pivot_regression (s : Fin 2) : sourceMomentSchur h s.val 0 = h s.val := by
  simp [sourceMomentSchur, dotProduct]

theorem eight_source_diagonal_limit_regression (s : Fin 2) :
    Tendsto (fun k => criticalPairing s s 3 k) atTop
      (nhds ((2*sourceMomentSchur h s.val 3 : ℝ) : ℂ)) :=
  criticalPairing_self_tendsto s 3 (sourceMatrices_through_four_posDef s 3 (by omega))

theorem eight_source_cross_limit_regression :
    Tendsto (fun k => criticalPairing 0 1 3 k) atTop (nhds 0) ∧
      Tendsto (fun k => criticalPairing 1 0 3 k) atTop (nhds 0) :=
  ⟨criticalPairing_even_odd_tendsto 3,criticalPairing_odd_even_tendsto 3⟩

/-- This is a signed physical test, not a contraction certificate for T_10. -/
theorem ten_source_even_direction_regression :
    0 < sourceMomentSchur h 0 4 ∧
      Tendsto (criticalBalance 0 4) atTop (nhds (2*sourceMomentSchur h 0 4)) ∧
      ∀ᶠ k : ℕ in atTop, sourceMomentSchur h 0 4 <
        ‖criticalIncident 0 4 k‖^2-‖criticalReturned 0 4 k‖^2 :=
  ⟨fifth_even_pivot_pos,
    criticalBalance_tendsto 0 4 (sourceMatrices_through_four_posDef 0 4 (by omega)),
    fifth_even_eventually_above_pivot⟩

theorem ten_source_jordan_gap_regression :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop,
      ‖radialReturnJordanNegativePort k 10 (criticalIncident 0 4 k)‖^2+ε ≤
        ‖radialReturnJordanPositivePort k 10 (criticalIncident 0 4 k)‖^2 :=
  (criticalMargin_iff_jordanGap 0 4).mp fifth_even_criticalMargin

end
end CarryCriticalSource
