import FiniteReferenceTable
import SourceGate

namespace C3CofactorCorrelation

open C3Cofactor
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem completed_native_odd_third_block_posDef :
    (oddThirdB
      (sourceOddA (fun j : Fin 7 => nativeC j.val))
      (sourceOddB (fun j : Fin 7 => nativeC j.val))
      (sourceOddD (fun j : Fin 7 => nativeC j.val))
      (sourceOddE (fun j : Fin 7 => nativeC j.val))
      (sourceOddF (fun j : Fin 7 => nativeC j.val))
      (sourceOddG (fun j : Fin 7 => nativeC j.val))).PosDef := by
  apply source_odd_block_posDef_of_coefficient_boxes
  intro j
  exact native_even_coefficient_candidate_contains j

#print axioms completed_tail48_jet_error_tight
#print axioms completed_native_jet_reference_error48_tight
#print axioms native_even_coefficient_candidate_contains
#print axioms completed_native_odd_third_block_posDef

end
end C3CofactorCorrelation
