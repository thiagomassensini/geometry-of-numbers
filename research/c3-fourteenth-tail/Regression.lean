import FourNativeBoxes

open CarryC3Boxes CarryC3Tail CarryTwoEvenJets
open scoped BigOperators

example (j : Fin 4) : ‖nativeEvenJets j-reference j‖ ≤ fourJetTolerance :=
  canonical_four_source_boxes j

example :
    0 < CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment 0*
        CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment 2-
      (CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment 1)^2 :=
  canonical_two_even_determinant_pos_from_c3

example (r : Fin 7) :
    ‖sourceJet r.val fullC3Signal-sourceJet r.val (acceleratedC3Head 64)‖ ≤ (1/10^19:ℝ) :=
  native_c3_seven_jet_error_at64 r

example : (∑ k : Fin 12, boundaryWeight k)=0 := by decide +kernel
example : (∑ k : Fin 12, (k.val:ℚ)*boundaryWeight k)=(-1/3:ℚ) := by decide +kernel

/-- The two original legs and their actual C3 addresses are retained. -/
example (w : ℂ) : CPFormal.Analytic.Cp.realCpSaturatedBracket 3 0
    (CarrySelfAdjointOperator.operatorHeightParameter w)=
      c3Sample 2 w-2*c3Sample 3 w+c3Sample 4 w := by
  rw [native_c3_cell_fd,fd_two]
  norm_num
  ring
