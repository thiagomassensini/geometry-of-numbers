import SigmaC5RationalNodeCenteredBoxes
import SigmaC5ZeroExpGenericRecurrence

namespace CarrySigmaObstruction

open ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The first Dirichlet summand is independent of the node: the centered log
  at `m = 1` vanishes, so its certified exponential box is the generic stage-4
  zero-input box. This isolates one summand of the C5 head without unfolding
  the other 98 summands. -/
theorem c5CenteredDirichletTermBox_one_eq_generic
    (nLog : ℕ) (logTwo : Interval) (S : ComplexInterval) :
    c5CenteredDirichletTermBoxWithLogTwo nLog 192 896 4 logTwo 1 S =
      c5GenericBox 11 15 := by
  rw [c5CenteredDirichletTermBoxWithLogTwo_one]
  simpa using
    (c5RoundedExpC_zero_stage_2_to_192_closed_form 4
      (by norm_num) (by norm_num))

/-- The production centered box uses the same exact first-summand reduction. -/
theorem c5CenteredDirichletTermBox_one_fixed
    (S : ComplexInterval) :
    c5CenteredDirichletTermBox 512 192 896 4 1 S =
      c5GenericBox 11 15 := by
  simpa [c5CenteredDirichletTermBox] using
    (c5CenteredDirichletTermBox_one_eq_generic 512
      (c5CenteredLog2I 512) S)

#print axioms c5CenteredDirichletTermBox_one_eq_generic
#print axioms c5CenteredDirichletTermBox_one_fixed

end CarrySigmaObstruction
