import GeometryOfNumbers.Analysis.CarryMaterialFourthPivot

open GeometryOfNumbers.Analysis
noncomputable section

-- The new pivot is order eight of the same residual, after three reductions.
example : carryMaterialFourthPivot = carryPairingRemainder carryMaterialEvenPairing 3 3 3 := rfl

-- Both ordered couplings to the old order-six direction are retained.
example : carryMaterialFourthPivot =
    carryPairingRemainder carryMaterialEvenPairing 2 3 3-
      carryPairingRemainder carryMaterialEvenPairing 2 3 2*
        carryPairingRemainder carryMaterialEvenPairing 2 2 3/
          carryPairingPivot carryMaterialEvenPairing 2 := rfl

-- The critical combination is nonzero even though it cancels old columns.
example : carryMaterialFourthCritical 3 = 1 := carryMaterialFourthCritical_last
example : carryMaterialFourthCritical ≠ 0 := carryMaterialFourthCritical_ne_zero

-- This property requires only OLD nondegeneracy, not the NEW source sign.
example (hK : ∀ i j, carryMaterialEvenPairing i j = carryMaterialEvenPairing j i)
    (hp : ∀ r < 3, carryPairingPivot carryMaterialEvenPairing r ≠ 0) :
    carryPairingBilinear carryMaterialEvenPairing 4
      carryMaterialFourthCritical carryMaterialFourthCritical = carryMaterialFourthPivot := by
  rw [carryMaterialFourthCritical_pairing hK hp,carryMaterialFourthCritical_last,mul_one]

-- The threshold reads the existing material response rather than new fields.
example : carryMaterialFourthSourceThreshold =
    (carryMaterialTaylorShift 9 0).re^2/carryMaterialResponseScale+carryMaterialFourthOldCoupling := rfl
