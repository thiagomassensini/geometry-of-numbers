import FiniteReferenceTable
import SourceGate
import SourceSchurShift
import CofactorTransport

namespace C3CofactorChiral

open C3Cofactor CarrySourceBezout CarrySelfAdjointOperator
open scoped Matrix

noncomputable section
set_option autoImplicit false

private def prefixBall (a b d : RationalBall) : RationalBall :=
  (a.mul d).sub (b.mul b)

private theorem prefixBall_contains {a b d : RationalBall} {av bv dv : ℝ}
    (ha : a.Contains av) (hb : b.Contains bv) (hd : d.Contains dv) :
    (prefixBall a b d).Contains (oddPrefixDet av bv dv) := by
  simpa only [prefixBall, oddPrefixDet, pow_two] using
    RationalBall.sub_contains (RationalBall.mul_contains ha hd) (RationalBall.mul_contains hb hb)

private def cofactorMarginBall (a b d e f g : RationalBall) (x y : ℚ) : RationalBall :=
  let X := RationalBall.point x
  let Y := RationalBall.point y
  let two := RationalBall.point 2
  let r₀ := ((a.mul X).add (b.mul Y)).add e
  let r₁ := ((b.mul X).add (d.mul Y)).add f
  let energy := ((((((a.mul (X.mul X)).add (((two.mul b).mul X).mul Y)).add
    (d.mul (Y.mul Y))).add ((two.mul e).mul X)).add ((two.mul f).mul Y)).add g)
  let residual := ((d.mul (r₀.mul r₀)).sub (((two.mul b).mul r₀).mul r₁)).add
    (a.mul (r₁.mul r₁))
  ((prefixBall a b d).mul energy).sub residual

private theorem cofactorMarginBall_contains
    {a b d e f g : RationalBall} {av bv dv ev fv gv : ℝ}
    (ha : a.Contains av) (hb : b.Contains bv) (hd : d.Contains dv)
    (he : e.Contains ev) (hf : f.Contains fv) (hg : g.Contains gv) (x y : ℚ) :
    (cofactorMarginBall a b d e f g x y).Contains
      (oddPrefixDet av bv dv * oddDirectionEnergy av bv dv ev fv gv x y -
        oddAdjugateResidual av bv dv ev fv x y) := by
  have htwo : (RationalBall.point 2).Contains (2 : ℝ) := by
    exact_mod_cast RationalBall.point_contains 2
  have hx := RationalBall.point_contains x
  have hy := RationalBall.point_contains y
  have hD := prefixBall_contains ha hb hd
  simp only [cofactorMarginBall, oddDirectionEnergy, oddAdjugateResidual,
    oddResidual0, oddResidual1, pow_two]
  repeat first
    | assumption
    | apply RationalBall.add_contains
    | apply RationalBall.sub_contains
    | apply RationalBall.mul_contains
    | apply RationalBall.neg_contains

private abbrev cb := candidateCoefficientBall
private def evenABall := ((cb 0).mul (cb 1)).neg
private def evenBBall := (RationalBall.point (-2)).mul ((cb 0).mul (cb 2))
private def evenEBall := (RationalBall.point (-3)).mul ((cb 0).mul (cb 3))
private def evenDBall := evenEBall.sub ((cb 1).mul (cb 2))
private def evenFBall := ((RationalBall.point (-4)).mul ((cb 0).mul (cb 4))).sub
  ((RationalBall.point 2).mul ((cb 1).mul (cb 3)))
private def evenGBall := (((RationalBall.point (-5)).mul ((cb 0).mul (cb 5))).sub
  ((RationalBall.point 3).mul ((cb 1).mul (cb 4)))).sub ((cb 2).mul (cb 3))

private def evenX : ℚ := 16943337609 / 10^14
private def evenY : ℚ := 1799554820555 / 10^14

private theorem even_certificate :
    let c := nativeC
    let a := -(c 0 * c 1)
    let b := -2 * (c 0 * c 2)
    let e := -3 * (c 0 * c 3)
    let d := e - c 1 * c 2
    let f := -4 * (c 0 * c 4) - 2 * (c 1 * c 3)
    let g := -5 * (c 0 * c 5) - 3 * (c 1 * c 4) - c 2 * c 3
    0 < a ∧ 0 < oddPrefixDet a b d ∧
      (3/10^24 : ℝ) <
        oddPrefixDet a b d * oddDirectionEnergy a b d e f g evenX evenY -
          oddAdjugateResidual a b d e f evenX evenY := by
  dsimp only
  have hc := C3CofactorCorrelation.native_even_source_coefficient_boxes
  have hscale (k : ℚ) (i j : Fin 7) :=
    RationalBall.mul_contains (RationalBall.point_contains k)
      (RationalBall.mul_contains (hc i) (hc j))
  have ha := RationalBall.neg_contains (RationalBall.mul_contains (hc 0) (hc 1))
  have hb := hscale (-2) 0 2
  have he := hscale (-3) 0 3
  have hd := RationalBall.sub_contains he (RationalBall.mul_contains (hc 1) (hc 2))
  have hf := RationalBall.sub_contains (hscale (-4) 0 4) (hscale 2 1 3)
  have hg := RationalBall.sub_contains (RationalBall.sub_contains (hscale (-5) 0 5)
    (hscale 3 1 4)) (RationalBall.mul_contains (hc 2) (hc 3))
  have hA := RationalBall.lower_le_of_contains (b := evenABall) ha
  have hD := RationalBall.lower_le_of_contains
    (b := prefixBall evenABall evenBBall evenDBall) (prefixBall_contains ha hb hd)
  have hM := RationalBall.lower_le_of_contains
    (b := cofactorMarginBall evenABall evenBBall evenDBall evenEBall evenFBall evenGBall evenX evenY)
    (cofactorMarginBall_contains ha hb hd he hf hg evenX evenY)
  push_cast at hA hD hM
  simp only [neg_mul] at hD hM ⊢
  refine ⟨lt_of_lt_of_le ?_ hA, lt_of_lt_of_le ?_ hD, lt_of_lt_of_le ?_ hM⟩
  all_goals norm_num [evenABall, evenBBall, evenDBall, evenEBall, evenFBall, evenGBall,
    prefixBall, cofactorMarginBall, evenX, evenY, candidateCoefficientBall,
    RationalBall.point, RationalBall.neg, RationalBall.add, RationalBall.sub, RationalBall.mul]

private theorem native_even_block_eq :
    coefficientBlock (sourceKernel nativeC false) 3 =
      oddThirdB (-(nativeC 0 * nativeC 1)) (-2 * (nativeC 0 * nativeC 2))
        (-3 * (nativeC 0 * nativeC 3) - nativeC 1 * nativeC 2)
        (-3 * (nativeC 0 * nativeC 3))
        (-4 * (nativeC 0 * nativeC 4) - 2 * (nativeC 1 * nativeC 3))
        (-5 * (nativeC 0 * nativeC 5) - 3 * (nativeC 1 * nativeC 4) -
          nativeC 2 * nativeC 3) := by
  rw [CarrySourceDimensionThree.even_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddThirdB] <;> ring

theorem c3_even_third_bezout_det_lower :
    (3/10^24 : ℝ) < (coefficientBlock (sourceKernel nativeC false) 3).det := by
  rw [native_even_block_eq, odd_third_cofactor_identity _ _ _ _ _ _ (evenX : ℝ) (evenY : ℝ)]
  exact even_certificate.2.2

theorem c3_even_third_native_pivot_positive :
    0 < sourceMomentSchur nativeH 0 2 := by
  have hB : (coefficientBlock (sourceKernel nativeC false) 3).PosDef := by
    rw [native_even_block_eq]
    exact odd_third_posDef_of_cofactor_gate _ _ _ _ _ _ (evenX : ℝ) (evenY : ℝ)
      even_certificate.1 even_certificate.2.1 (lt_trans (by norm_num) even_certificate.2.2)
  have hH := (native_source_bezout_posDef_iff false 3).mp hB
  have hA : IsUnit (sourceMomentMatrix nativeH 0 2) :=
    (hH.submatrix (Fin.castSucc_injective 2)).isUnit
  exact C3GeneralCofactor.sourceMomentSchur_pos_of_block_posDef _ 0 2 hA hH

#print axioms c3_even_third_bezout_det_lower
#print axioms c3_even_third_native_pivot_positive

end
end C3CofactorChiral
