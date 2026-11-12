import SchurGate
import Regression

namespace C3Cofactor

noncomputable section
set_option autoImplicit false

/-- The fixed rational direction proposed for interval evaluation of the odd
third pivot. The cofactor identity itself is independent of this choice. -/
def oddReferenceX : ℝ := 14879782871 / 10 ^ 14

def oddReferenceY : ℝ := 1692226107996 / 10 ^ 14

theorem odd_reference_direction_is_positive
    (a b d e f g : ℝ) :
    oddPrefixDet a b d * oddDirectionEnergy a b d e f g oddReferenceX oddReferenceY -
        oddAdjugateResidual a b d e f oddReferenceX oddReferenceY =
      (oddThirdB a b d e f g).det := by
  simpa [oddReferenceX, oddReferenceY] using
    (odd_third_cofactor_identity a b d e f g oddReferenceX oddReferenceY).symm

/-- A positive rational canary exercises the conditional positive-definite gate. -/
theorem regression_positive_gate :
    (oddThirdB 1 0 1 0 0 1).PosDef := by
  apply odd_third_posDef_of_cofactor_gate 1 0 1 0 0 1 0 0
  all_goals norm_num [oddPrefixDet, oddDirectionEnergy, oddAdjugateResidual,
    oddResidual0, oddResidual1]

/-- The negative canary fails the independent strict margin, so the gate cannot
turn an arbitrary symmetric border into a positive matrix. -/
theorem regression_negative_margin :
    ¬ 0 < oddPrefixDet 1 0 1 * oddDirectionEnergy 1 0 1 0 0 (-1) 0 0 -
      oddAdjugateResidual 1 0 1 0 0 0 0 := by
  norm_num [oddPrefixDet, oddDirectionEnergy, oddAdjugateResidual,
    oddResidual0, oddResidual1]

/-- Singular leading blocks are still covered by the cofactor identity, while
the positive-definite gate correctly requires a strictly positive prefix. -/
theorem regression_singular_prefix_identity :
    (oddThirdB 1 1 1 0 0 1).det =
      oddPrefixDet 1 1 1 * oddDirectionEnergy 1 1 1 0 0 1 oddReferenceX oddReferenceY -
        oddAdjugateResidual 1 1 1 0 0 oddReferenceX oddReferenceY := by
  exact odd_third_cofactor_identity 1 1 1 0 0 1 oddReferenceX oddReferenceY

/-- A noncritical rational direction gives the same exact cofactor balance. -/
theorem regression_noncritical_direction :
    oddPrefixDet 2 1 3 * oddDirectionEnergy 2 1 3 1 1 4 (1 / 3) (-2 / 5) -
        oddAdjugateResidual 2 1 3 1 1 (1 / 3) (-2 / 5) =
      (oddThirdB 2 1 3 1 1 4).det := by
  exact (odd_third_cofactor_identity 2 1 3 1 1 4 (1 / 3) (-2 / 5)).symm

/-- The earlier exact synthetic negative control is imported from the TFVD
regression module; it is deliberately not classified as a physical Carry source. -/
theorem reused_synthetic_negative_control :
    ¬(CarrySourceBezout.coefficientBlock
        (CarrySourceBezout.sourceKernel CarrySourceBezout.negativeControl false) 2).PosSemidef :=
  CarrySourceBezout.regression_negative_control

#print axioms odd_reference_direction_is_positive
#print axioms regression_positive_gate
#print axioms regression_negative_margin
#print axioms regression_singular_prefix_identity
#print axioms regression_noncritical_direction
#print axioms reused_synthetic_negative_control

end
end C3Cofactor
