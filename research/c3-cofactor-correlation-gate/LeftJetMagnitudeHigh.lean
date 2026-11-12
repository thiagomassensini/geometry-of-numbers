import LeftJetMagnitudeLow

namespace C3CofactorCorrelation
open CarryC3Boxes CarryC3Tail CarryC3Gamma
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

theorem left_jet48_correlated_box_abs_bound_high (r : Fin 6) :
    -leftJet48MagnitudeBound ⟨r.val + 7, by omega⟩ ≤
        (leftJet48CorrelatedBox ⟨r.val + 7, by omega⟩).lo ∧
      (leftJet48CorrelatedBox ⟨r.val + 7, by omega⟩).hi ≤
        leftJet48MagnitudeBound ⟨r.val + 7, by omega⟩ := by
  fin_cases r <;> decide +kernel

end
end C3CofactorCorrelation
