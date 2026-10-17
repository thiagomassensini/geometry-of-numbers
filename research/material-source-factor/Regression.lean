import GeometryOfNumbers.Analysis.CarryMaterialSourceFactor

/-! Regressions on the literal completed material residual. No freely chosen
field, target moment matrix or positivity assumption is substituted. -/
open GeometryOfNumbers.Analysis
open scoped Matrix
noncomputable section

-- The recurrence starts at the actual two independently ordered observations.
example : carryPairingPivot carryMaterialEvenPairing 0 = carryMaterialResidualJet 2 2 := rfl
example : carryPairingPivot carryMaterialEvenPairing 1 = carryMaterialMixedPivot := rfl

-- The new order-six pivot retains both ordered old-new couplings.
example : carryPairingPivot carryMaterialEvenPairing 2 =
    carryMaterialResidualJet 6 6-
      carryMaterialResidualJet 6 2*carryMaterialResidualJet 2 6/carryMaterialResidualJet 2 2-
      (carryMaterialResidualJet 6 4-
        carryMaterialResidualJet 6 2*carryMaterialResidualJet 2 4/carryMaterialResidualJet 2 2)*
      (carryMaterialResidualJet 4 6-
        carryMaterialResidualJet 4 2*carryMaterialResidualJet 2 6/carryMaterialResidualJet 2 2)/
      carryMaterialMixedPivot := rfl

-- Odd observations remain the original independent sector.
example : carryMaterialOddPairing 0 1 = carryMaterialResidualJet 1 3 := rfl

-- Taking a real square root never silently certifies its input sign.
example (i j : Fin 3) : carryMaterialEvenCholesky 3 i j =
    carryPairingColumn carryMaterialEvenPairing j i*
      Real.sqrt (carryPairingPivot carryMaterialEvenPairing j) := rfl

-- Candidate factors are compatible as coefficients across finite cutoffs.
example (i j : Fin 3) :
    carryMaterialEvenCholesky 3 i j =
      carryMaterialEvenCholesky 4 (Fin.castLE (by decide) i) (Fin.castLE (by decide) j) := rfl

-- Both arguments of the bilinear ledger remain independent.
example (x y : Fin 3 → ℝ) : carryPairingBilinear carryMaterialEvenPairing 3 x y =
    ∑ i : Fin 3, ∑ j : Fin 3,
      carryMaterialResidualJet (2*(i.val+1)) (2*(j.val+1))*x i*y j := rfl
