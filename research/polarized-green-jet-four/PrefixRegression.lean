import QuarticExpansion
import FiniteExpansion

namespace CarryPolarizedFour
open CarryGreenFinitePart CarryInteriorGreen CarryRadialGreen CarryRadialRefinement CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem quartic_prefix_input (k : ℕ) (a : ℝ) :
    quarticInput k ![-a,1,0]=CarryInteriorGreen.criticalInput k a := by
  rw [quartic_input_five]
  simp only [CarryInteriorGreen.criticalInput,critical_weight_real]
  norm_num [Fin.sum_univ_succ,fiveWeight,realWeight]
  push_cast
  module

theorem quartic_prefix_balance (η : ℝ) (a : ℝ) (k : ℕ) :
    quarticBalance η ![-a,1,0] ![-a,1,0] k=CarryGreenFinitePart.greenBalance η a k := by
  unfold quarticBalance quarticBulk quarticResidual
  rw [quartic_prefix_input]
  unfold CarryGreenFinitePart.greenBalance CarryInteriorGreen.criticalBulk CarryInteriorGreen.criticalResidual
  rw [physical_form_re_symm (CarryRadialGreen.reconstructedResidual 0 η k (CarryInteriorGreen.criticalInput k a))
    (CarryRadialGreen.reconstructedBulk 0 η k (CarryInteriorGreen.criticalInput k a))]
  ring

theorem quartic_prefix_finite (a : ℝ) :
    finiteTerm ![-a,1,0] ![-a,1,0]=CarryGreenFinitePart.finiteTerm a := by
  norm_num [finiteTerm,momentPairing,CarryGreenFinitePart.finiteTerm,Fin.sum_univ_succ]
  ring

theorem quartic_prefix_correction (a : ℝ) :
    correctionTerm ![-a,1,0] ![-a,1,0]=CarryGreenFinitePart.correctionTerm a := by
  have hz : (![-a,1,0] : Fin 3 → ℝ) 2=0 := rfl
  norm_num [correctionTerm,crosses,CarryGreenFinitePart.correctionTerm,hz]
  ring

theorem quartic_prefix_fourth (a : ℝ) :
    fourthTerm ![-a,1,0] ![-a,1,0]=CarryGreenFinitePart.fourthPolynomial a := by
  have hz : (![-a,1,0] : Fin 3 → ℝ) 2=0 := rfl
  norm_num [fourthTerm,crosses,CarryGreenFinitePart.fourthPolynomial,hz]
  ring

end
end CarryPolarizedFour
