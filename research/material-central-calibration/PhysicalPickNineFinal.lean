import PhysicalPickEightFinal
import PhysicalPickNineSign
import GeometryOfNumbers.Analysis.CarryMaterialPickNineSchurCriterion
import Mathlib.Tactic

/-!
The final physical ninth C2 radial Cauchy--Pick gate.
The physical source comes from the previously proved C2 material readout;
the new unshifted H5 margin follows from the ORIGINAL material
restoredEvenFiveFactor. The shifted odd K4 was certified in GoN #342
from the unchanged C2 source eight-coordinate discriminant.
-/
namespace CarryMaterialPhysicalRadialMultiplierGate
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator Filter
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

theorem physicalC2RadialPickMatrix_nine_det_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop,
      0 < (physicalC2RadialPickMatrix k 9).det.re := by
  filter_upwards [physicalC2RadialPickMatrix_eventually_eq_native_dslope 9,
    canonicalCompletedNativeRadialDslopeSampleMatrix_nine_det_eventually_re_pos]
    with k hEq hDet
  rwa [hEq]

theorem physicalC2RadialPickMatrix_nine_leading_eight_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      ((physicalC2RadialPickMatrix k 9).submatrix
         Fin.castSucc Fin.castSucc).PosDef := by
  filter_upwards [physicalC2RadialPickMatrix_eight_eventually_posDef] with k hk
  have hSub :
      (physicalC2RadialPickMatrix k 9).submatrix
          Fin.castSucc Fin.castSucc =
        physicalC2RadialPickMatrix k 8 := by
    ext i j
    rfl
  rwa [hSub]

/-- ACTUAL physical material C2 radial Pick 9×9 is strictly positive
on sufficiently fine canonical nine-height radial families. -/
theorem physicalC2RadialPickMatrix_nine_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      (physicalC2RadialPickMatrix k 9).PosDef := by
  filter_upwards [physicalC2RadialPickMatrix_nine_leading_eight_eventually_posDef,
    physicalC2RadialPickMatrix_nine_det_eventually_re_pos,
    physicalC2Radial_eventually_regular 9] with k hLeading hDetRe hRegular
  let M := physicalC2RadialPickMatrix k 9
  have hHerm : M.IsHermitian := by
    exact carryMaterialComplexSourcePickMatrix_isHermitian 9
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
  exact hermitian_fin_nine_posDef_of_leading_posDef_det_pos M
    hHerm hLeading hDet

/-- The strict 9×9 SOURCE multiplier defect follows from the
invertible physical Hermite--Biehler gauge, not diagonal-only inequalities. -/
theorem physicalC2RadialDefectMatrix_nine_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      (physicalC2RadialDefectMatrix k 9).PosDef := by
  filter_upwards [physicalC2RadialPickMatrix_nine_eventually_posDef,
    physicalC2Radial_eventually_regular 9] with k hPick hReg
  have hU : ∀ i : Fin 9,
      0 < (canonicalCompletedC3RadialTiltPoint k i).im :=
    fun i => canonicalCompletedC3RadialTiltPoint_im_pos k i
  exact (carryMaterialComplexSourcePickMatrix_posDef_iff_sourceDefect 9
    (fun i => canonicalCompletedC3RadialTiltPoint k i)
    hU (fun i => (hReg i).1) (fun i => (hReg i).2)).mp hPick

#print axioms physicalC2RadialPickMatrix_nine_eventually_posDef
#print axioms physicalC2RadialDefectMatrix_nine_eventually_posDef

end CarryMaterialPhysicalRadialMultiplierGate
