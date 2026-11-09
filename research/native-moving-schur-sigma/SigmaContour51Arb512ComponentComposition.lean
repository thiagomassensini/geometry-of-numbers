import SigmaContour51ArbIntervalComposition
import SigmaContour51ArbBoundCertificate512
import SigmaContour51ArcGeometry
import Mathlib.Tactic

/-!
# Component-box bridge for the 512-arc circle response certificate

This module makes the analytic inputs to the external 512-arc response table
explicit. Supplying sound boxes for `s`, ζ, ζ′ and digamma, positive denominator
norm-square ranges, and a rational norm bound for the composed response box
proves the exact Arb endpoint inclusion on every point of the closed arc. The
geometric `s` field can be supplied by `SigmaContour51ArcGeometry`; this module
does not manufacture the analytic component boxes or assert their Arb bounds.
-/

namespace CarrySigmaObstruction

open ZetaLean ZetaLean.ComplexInterval
open CarrySelfAdjointOperator Complex

noncomputable section
set_option autoImplicit false

/-- Component certificate for the original source response on one closed 512 arc.
The exact rational comparison is against the indexed outward Arb endpoint. -/
structure Contour51Arb512ArcComponentBoxes (k : ℕ) where
  sBox : ComplexInterval
  zetaBox : ComplexInterval
  zetaDerivativeBox : ComplexInterval
  digammaBox : ComplexInterval
  logPiBox : ComplexInterval
  sNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo
  sMinusOneNormSqPos :
    0 < (ComplexInterval.normSqRange
      (ComplexInterval.sub sBox contour51ArbOneBox)).lo
  zetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo
  sContains : ∀ u ∈ contour51Arb512ParameterArc k,
    sBox.contains (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)))
  zetaContains : ∀ u ∈ contour51Arb512ParameterArc k,
    zetaBox.contains (riemannZeta
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))))
  zetaDerivativeContains : ∀ u ∈ contour51Arb512ParameterArc k,
    zetaDerivativeBox.contains (deriv riemannZeta
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))))
  digammaContains : ∀ u ∈ contour51Arb512ParameterArc k,
    digammaBox.contains (Complex.digamma
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)) / 2))
  logPiContains : logPiBox.contains (Complex.log (Real.pi : ℂ))
  composedResponseNormBound :
    ComplexInterval.normBound
      (contour51ArbOriginalResponseBox sBox zetaBox zetaDerivativeBox digammaBox logPiBox
        sNormSqPos sMinusOneNormSqPos zetaNormSqPos) ≤
      contour51Arb512ResponseUpperBound k

/-- A single component record proves the original response inclusion on that entire closed arc.
The bound is on the Euclidean norm of the source response, not only a sampled value. -/
theorem contour51Arb512ResponseArcEvaluatorInclusion_of_component_boxes_at_arc
    {k : ℕ} (hk : k < 512) (hbox : Contour51Arb512ArcComponentBoxes k) :
    ∀ u : ℝ, u ∈ contour51Arb512ParameterArc k →
      ‖contour51OriginalResponse (circleMap 0 51 (-Real.pi * u))‖ ≤
        contour51Arb512ResponseUpperBound k := by
  intro u hu
  have hStart : (0 : ℝ) ≤ (k : ℝ) / 512 := by
    positivity
  have hEnd : (((k + 1 : ℕ) : ℝ) / 512) ≤ 1 := by
    have hkNat : k + 1 ≤ 512 := Nat.succ_le_of_lt hk
    have hkReal : ((k + 1 : ℕ) : ℝ) ≤ 512 := by exact_mod_cast hkNat
    rw [div_le_one₀ (by norm_num : (0 : ℝ) < 512)]
    exact hkReal
  have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hu with ⟨huLo, huHi⟩
    exact ⟨le_trans hStart huLo, le_trans huHi hEnd⟩
  have hResponse := contour51ArbOriginalResponseBox_contains_lower_path hu01
    (hbox.sContains u hu) (hbox.zetaContains u hu)
    (hbox.zetaDerivativeContains u hu) (hbox.digammaContains u hu)
    hbox.logPiContains hbox.sNormSqPos hbox.sMinusOneNormSqPos hbox.zetaNormSqPos
  have hNormBound := ComplexInterval.norm_le_normBound hResponse
  exact le_trans hNormBound (by exact_mod_cast hbox.composedResponseNormBound)

/-- Component records for every arc discharge the complete 512-arc evaluator inclusion used by
the conditional Arb-to-Lean circle-bound bridge. The records remain analytic inputs. -/
theorem contour51Arb512ResponseArcEvaluatorInclusion_of_all_component_boxes
    (hboxes : ∀ k : ℕ, k < 512 → Contour51Arb512ArcComponentBoxes k) :
    contour51Arb512ResponseArcEvaluatorInclusion := by
  intro k hk u hu
  exact contour51Arb512ResponseArcEvaluatorInclusion_of_component_boxes_at_arc
    hk (hboxes k hk) u hu

#print axioms contour51Arb512ResponseArcEvaluatorInclusion_of_component_boxes_at_arc
#print axioms contour51Arb512ResponseArcEvaluatorInclusion_of_all_component_boxes

end
end CarrySigmaObstruction
