import PhysicalPickSevenFinal
import PhysicalPickEightSign
import GeometryOfNumbers.Analysis.CarryMaterialPickEightSchurCriterion
import Mathlib.Tactic

/-!
The final physical eighth C2 radial Cauchy--Pick gate.
The physical source comes from the previously proved C2 material readout;
the unshifted H4 margin follows from material Cholesky4,
while the shifted odd K3 margin comes from the exact source-12
odd discriminant identified in the previous sixth-direction proof.
-/
namespace CarryMaterialPhysicalRadialMultiplierGate
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator Filter
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

theorem physicalC2RadialPickMatrix_eight_det_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop,
      0 < (physicalC2RadialPickMatrix k 8).det.re := by
  filter_upwards [physicalC2RadialPickMatrix_eventually_eq_native_dslope 8,
    canonicalCompletedNativeRadialDslopeSampleMatrix_eight_det_eventually_re_pos]
    with k hEq hDet
  rwa [hEq]

theorem physicalC2RadialPickMatrix_eight_leading_seven_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      ((physicalC2RadialPickMatrix k 8).submatrix
         Fin.castSucc Fin.castSucc).PosDef := by
  filter_upwards [physicalC2RadialPickMatrix_seven_eventually_posDef] with k hk
  have hSub :
      (physicalC2RadialPickMatrix k 8).submatrix
          Fin.castSucc Fin.castSucc =
        physicalC2RadialPickMatrix k 7 := by
    ext i j
    rfl
  rwa [hSub]

/-- ACTUAL physical material C2 radial Pick 8×8 is strictly positive
on sufficiently fine canonical eight-height radial families. -/
theorem physicalC2RadialPickMatrix_eight_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      (physicalC2RadialPickMatrix k 8).PosDef := by
  filter_upwards [physicalC2RadialPickMatrix_eight_leading_seven_eventually_posDef,
    physicalC2RadialPickMatrix_eight_det_eventually_re_pos,
    physicalC2Radial_eventually_regular 8] with k hLeading hDetRe hRegular
  let M := physicalC2RadialPickMatrix k 8
  have hHerm : M.IsHermitian := by
    exact carryMaterialComplexSourcePickMatrix_isHermitian 8
      (fun i => canonicalCompletedC3RadialTiltPoint k i)
      (fun i => canonicalCompletedC3RadialTiltPoint_im_pos k i)
      (fun i => (hRegular i).1)
  have hDetStar : star M.det = M.det := by
    calc
      star M.det = (Mᴴ).det := (Matrix.det_conjTranspose M).symm
      _ = M.det := by rw [hHerm]
  have hDetIm : M.det.im = 0 := by
    exact Complex.conj_eq_iff_im.mp (by simpa [Complex.star_def] using hDetStar)
  have hDet : (0 : ℂ) < M.det :=
    Complex.pos_iff.mpr ⟨hDetRe, hDetIm.symm⟩
  exact hermitian_fin_eight_posDef_of_leading_posDef_det_pos M
    hHerm hLeading hDet

/-- The strict 8×8 SOURCE multiplier defect follows from the
invertible physical Hermite--Biehler gauge, not diagonal-only inequalities. -/
theorem physicalC2RadialDefectMatrix_eight_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      (physicalC2RadialDefectMatrix k 8).PosDef := by
  filter_upwards [physicalC2RadialPickMatrix_eight_eventually_posDef,
    physicalC2Radial_eventually_regular 8] with k hPick hReg
  have hU : ∀ i : Fin 8,
      0 < (canonicalCompletedC3RadialTiltPoint k i).im :=
    fun i => canonicalCompletedC3RadialTiltPoint_im_pos k i
  exact (carryMaterialComplexSourcePickMatrix_posDef_iff_sourceDefect 8
    (fun i => canonicalCompletedC3RadialTiltPoint k i)
    hU (fun i => (hReg i).1) (fun i => (hReg i).2)).mp hPick

#print axioms physicalC2RadialPickMatrix_eight_eventually_posDef
#print axioms physicalC2RadialDefectMatrix_eight_eventually_posDef

end CarryMaterialPhysicalRadialMultiplierGate
