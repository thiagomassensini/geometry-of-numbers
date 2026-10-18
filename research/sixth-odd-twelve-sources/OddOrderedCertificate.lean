import OddTrialPositivity
import OrderedKernelPositivity

namespace CarrySixthOdd
open CarrySelfAdjointOperator CarryCriticalSource
open GeometryOfNumbers.Analysis CarryMaterialSourceFactorComparison
noncomputable section
set_option autoImplicit false

/-- Sign of the ORIGINAL ordered odd pivot, extracted from the genuine
finite matrix. No quantitative interval of the transformed pivot is reused. -/
theorem sixth_ordered_odd_pivot_pos : 0 < carryPairingPivot carryMaterialOddPairing 5 := by
  have hs (i j : ℕ) : carryMaterialOddPairing i j=carryMaterialOddPairing j i := by
    rw [material_odd_pairing_source,material_odd_pairing_source]
    congr 1
    omega
  have hm : Matrix.PosDef (fun i j : Fin 6 => carryMaterialOddPairing i.val j.val) := by
    convert odd_source_six_posDef using 1
    ext i j
    exact material_odd_pairing_source i.val j.val
  exact CarryOrderedKernel.ordered_pivot_pos_of_posDef carryMaterialOddPairing hs 5 hm

theorem sixth_odd_sourceRemainder_pos : 0 < nativeSourceSchurRemainder 1 5 :=
  (criticalMargin_iff_sourceRemainder 1 5 CarryThetaPattern.odd_source_five_posDef).mp
    sixth_odd_criticalMargin

end
end CarrySixthOdd
