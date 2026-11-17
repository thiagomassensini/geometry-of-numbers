import GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen
import Mathlib.Tactic

/-!
# Physical C2 projective-chiral arms with the hidden Green complement

This construction uses ONLY the completed physical source from GoN:
companion/value pairs and their original readout-hidden complements.
It is not obtained by factoring a target moment matrix, fitting an auxiliary
state, or inventing a Hilbert metric.

The two Hilbert arms retain both the original full state and the hidden
completion. Their difference exactly recovers the existing valve's Wronskian
before any division by a characteristic, height or parameter separation.
-/

namespace GeometryOfNumbers.Analysis

open BaseTwoCompletion
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- Genuine source chirality on arbitrary physical companion/value pairs. -/
def carryMaterialChiralPositiveLeg (x : MaterialCarrier × MaterialCarrier) :
    MaterialCarrier := x.1 + Complex.I • x.2

def carryMaterialChiralNegativeLeg (x : MaterialCarrier × MaterialCarrier) :
    MaterialCarrier := x.1 - Complex.I • x.2

/-- The signed chiral identity uses the original complex Hilbert inner
product and the original ordered Green form. -/
theorem carryMaterialChiralLegs_green (x y : MaterialCarrier × MaterialCarrier) :
    inner ℂ (carryMaterialChiralPositiveLeg x) (carryMaterialChiralPositiveLeg y) -
      inner ℂ (carryMaterialChiralNegativeLeg x) (carryMaterialChiralNegativeLeg y) =
      -2 * Complex.I * carryMaterialPairGreen x y := by
  simp only [carryMaterialChiralPositiveLeg, carryMaterialChiralNegativeLeg,
    carryMaterialPairGreen, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring

/-- The source's incident and hidden-return sectors live in an authentic
Hilbert direct sum, not in a scalar boundary trace. -/
abbrev CarryMaterialCompleteChiralArm :=
  WithLp 2 (MaterialCarrier × MaterialCarrier)

/-- The hidden component is intentionally placed in the opposite chirality,
so it is SUBTRACTED from the complete physical Green balance. -/
def carryMaterialCompleteChiralPositive
    (x : MaterialCarrier × MaterialCarrier) : CarryMaterialCompleteChiralArm :=
  WithLp.toLp 2
    (carryMaterialChiralPositiveLeg x,
      carryMaterialChiralNegativeLeg (carryMaterialPairComplement x))

def carryMaterialCompleteChiralNegative
    (x : MaterialCarrier × MaterialCarrier) : CarryMaterialCompleteChiralArm :=
  WithLp.toLp 2
    (carryMaterialChiralNegativeLeg x,
      carryMaterialChiralPositiveLeg (carryMaterialPairComplement x))

private theorem carryMaterialChiralArm_inner
    (x y : MaterialCarrier × MaterialCarrier) :
    inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      inner ℂ x.1 y.1 + inner ℂ x.2 y.2 := by
  exact WithLp.prod_inner_apply (WithLp.toLp 2 x) (WithLp.toLp 2 y)

/-- Full (not boundary-only) source polarization with all ordered crosses. -/
theorem carryMaterialCompleteChiralDifference_eq_green
    (x y : MaterialCarrier × MaterialCarrier) :
    inner ℂ (carryMaterialCompleteChiralPositive x) (carryMaterialCompleteChiralPositive y) -
      inner ℂ (carryMaterialCompleteChiralNegative x) (carryMaterialCompleteChiralNegative y) =
      -2 * Complex.I *
        (carryMaterialPairGreen x y -
          carryMaterialPairGreen (carryMaterialPairComplement x)
            (carryMaterialPairComplement y)) := by
  simp only [carryMaterialCompleteChiralPositive,
    carryMaterialCompleteChiralNegative, carryMaterialChiralArm_inner]
  have hraw := carryMaterialChiralLegs_green x y
  have hhidden := carryMaterialChiralLegs_green
    (carryMaterialPairComplement x) (carryMaterialPairComplement y)
  calc
    _ = (inner ℂ (carryMaterialChiralPositiveLeg x)
                 (carryMaterialChiralPositiveLeg y) -
           inner ℂ (carryMaterialChiralNegativeLeg x)
                 (carryMaterialChiralNegativeLeg y)) -
        (inner ℂ (carryMaterialChiralPositiveLeg (carryMaterialPairComplement x))
                 (carryMaterialChiralPositiveLeg (carryMaterialPairComplement y)) -
           inner ℂ (carryMaterialChiralNegativeLeg (carryMaterialPairComplement x))
                 (carryMaterialChiralNegativeLeg (carryMaterialPairComplement y))) := by ring
    _ = _ := by rw [hraw, hhidden]; ring

/-- The source-derived two-arm pairing has fixed orientation I/2.
Its value is the original full Green balance with its hidden complement. -/
def carryMaterialCompleteChiralGreenPairing (t u : ℝ) : ℂ :=
  (Complex.I / 2) *
    (inner ℂ
        (carryMaterialCompleteChiralPositive (carryMaterialCompanionValuePair t))
        (carryMaterialCompleteChiralPositive (carryMaterialCompanionValuePair u)) -
      inner ℂ
        (carryMaterialCompleteChiralNegative (carryMaterialCompanionValuePair t))
        (carryMaterialCompleteChiralNegative (carryMaterialCompanionValuePair u)))

theorem carryMaterialCompleteChiralGreenPairing_eq_physical (t u : ℝ) :
    carryMaterialCompleteChiralGreenPairing t u =
      carryMaterialPairGreen (carryMaterialCompanionValuePair t)
          (carryMaterialCompanionValuePair u) -
        carryMaterialPairGreen
          (carryMaterialPairComplement (carryMaterialCompanionValuePair t))
          (carryMaterialPairComplement (carryMaterialCompanionValuePair u)) := by
  rw [carryMaterialCompleteChiralGreenPairing,
    carryMaterialCompleteChiralDifference_eq_green]
  calc
    _ = -(Complex.I ^ 2) *
      (carryMaterialPairGreen (carryMaterialCompanionValuePair t)
          (carryMaterialCompanionValuePair u) -
        carryMaterialPairGreen
          (carryMaterialPairComplement (carryMaterialCompanionValuePair t))
          (carryMaterialPairComplement (carryMaterialCompanionValuePair u))) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- Native source → projective valve: both effective channels are physical,
and their signed pairing is exactly the full completed valve return Green.
The gauge eta is a coordinate choice only, with eta != 0. -/
theorem carryMaterialCompleteChiralGreenPairing_eq_valve
    (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    carryMaterialCompleteChiralGreenPairing t u =
      carryValveReturnGreen eta t u := by
  rw [carryMaterialCompleteChiralGreenPairing_eq_physical]
  exact carryValveReturnGreen_physical_ledger eta heta t u

/-- The visible vs hidden energy is NOT a positive Gram by construction:
the exact source product is a difference of two positive Hilbert Grams,
with the Green quarter-turn retained. -/
theorem carryMaterialCompleteChiralGreenPairing_eq_twoGrams
    (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    carryValveReturnGreen eta t u =
      (Complex.I / 2) *
        (inner ℂ
            (carryMaterialCompleteChiralPositive (carryMaterialCompanionValuePair t))
            (carryMaterialCompleteChiralPositive (carryMaterialCompanionValuePair u)) -
          inner ℂ
            (carryMaterialCompleteChiralNegative (carryMaterialCompanionValuePair t))
            (carryMaterialCompleteChiralNegative (carryMaterialCompanionValuePair u))) := by
  exact (carryMaterialCompleteChiralGreenPairing_eq_valve eta heta t u).symm


/-- Physical source on a finite family of actual real times. The two matrices
are ordinary positive Hilbert Grams of concretely constructed material arms.
Their SIGNED difference is the full valve/Wronskian matrix, not a claim that
the difference is positive. This keeps *all* i,j crossings. -/
theorem carryMaterialCompleteChiralValveMatrix_eq_gramDifference
    (eta : ℝ) (heta : eta ≠ 0) (N : ℕ) (time : Fin N → ℝ) :
    Matrix.of (fun i j : Fin N =>
      carryValveReturnGreen eta (time i) (time j)) =
      (Complex.I / 2) •
        (Matrix.gram ℂ
          (fun i : Fin N =>
            carryMaterialCompleteChiralPositive
              (carryMaterialCompanionValuePair (time i))) -
         Matrix.gram ℂ
          (fun i : Fin N =>
            carryMaterialCompleteChiralNegative
              (carryMaterialCompanionValuePair (time i)))) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.gram_apply]
  exact (carryMaterialCompleteChiralGreenPairing_eq_valve eta heta
    (time i) (time j)).symm


end
end GeometryOfNumbers.Analysis


/-! Audit: only standard proof principles. -/
#print axioms GeometryOfNumbers.Analysis.carryMaterialChiralLegs_green
#print axioms GeometryOfNumbers.Analysis.carryMaterialCompleteChiralDifference_eq_green
#print axioms GeometryOfNumbers.Analysis.carryMaterialCompleteChiralGreenPairing_eq_valve
#print axioms GeometryOfNumbers.Analysis.carryMaterialCompleteChiralValveMatrix_eq_gramDifference
