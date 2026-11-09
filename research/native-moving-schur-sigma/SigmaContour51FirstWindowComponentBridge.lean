import SigmaContour51ArbIntervalComposition
import SigmaContour51ArcGeometry
import SigmaContour51C5PiBridge
import Mathlib.Tactic

/-!
# Component-box route from the original evaluator to the first central determinant

This module packages the three original-source residual integrands needed for the
`s = 0` determinant. The geometric boxes for `s` and `z` and the C5 `log π` box
are supplied by existing Lean theorems. Zeta, zeta derivative, digamma, norm
positivity, power-denominator positivity, and endpoint comparisons remain explicit
analytic inputs. No Arb table endpoint is treated as a pointwise theorem here.
-/

namespace CarrySigmaObstruction

open ZetaLean ZetaLean.ComplexInterval
open CarrySelfAdjointOperator Complex
open scoped Interval

noncomputable section
set_option autoImplicit false

/-- Select the already exported lower endpoint for one of the first three residual orders. -/
def contour51Arb4096LowerArcEndpointFirstThree (k : ℕ) (n : Fin 3) : ℚ :=
  if n.val = 0 then contour51Arb4096LowerArcEndpoint0 k
  else if n.val = 1 then contour51Arb4096LowerArcEndpoint1 k
  else contour51Arb4096LowerArcEndpoint2 k

/-- Select the already exported upper endpoint for one of the first three residual orders. -/
def contour51Arb4096UpperArcEndpointFirstThree (k : ℕ) (n : Fin 3) : ℚ :=
  if n.val = 0 then contour51Arb4096UpperArcEndpoint0 k
  else if n.val = 1 then contour51Arb4096UpperArcEndpoint1 k
  else contour51Arb4096UpperArcEndpoint2 k

@[simp] theorem contour51Arb4096LowerArcEndpointFirstThree_zero (k : ℕ) :
    contour51Arb4096LowerArcEndpointFirstThree k 0 = contour51Arb4096LowerArcEndpoint0 k := by
  simp [contour51Arb4096LowerArcEndpointFirstThree]

@[simp] theorem contour51Arb4096LowerArcEndpointFirstThree_one (k : ℕ) :
    contour51Arb4096LowerArcEndpointFirstThree k 1 = contour51Arb4096LowerArcEndpoint1 k := by
  simp [contour51Arb4096LowerArcEndpointFirstThree]

@[simp] theorem contour51Arb4096LowerArcEndpointFirstThree_two (k : ℕ) :
    contour51Arb4096LowerArcEndpointFirstThree k 2 = contour51Arb4096LowerArcEndpoint2 k := by
  simp [contour51Arb4096LowerArcEndpointFirstThree]

@[simp] theorem contour51Arb4096UpperArcEndpointFirstThree_zero (k : ℕ) :
    contour51Arb4096UpperArcEndpointFirstThree k 0 = contour51Arb4096UpperArcEndpoint0 k := by
  simp [contour51Arb4096UpperArcEndpointFirstThree]

@[simp] theorem contour51Arb4096UpperArcEndpointFirstThree_one (k : ℕ) :
    contour51Arb4096UpperArcEndpointFirstThree k 1 = contour51Arb4096UpperArcEndpoint1 k := by
  simp [contour51Arb4096UpperArcEndpointFirstThree]

@[simp] theorem contour51Arb4096UpperArcEndpointFirstThree_two (k : ℕ) :
    contour51Arb4096UpperArcEndpointFirstThree k 2 = contour51Arb4096UpperArcEndpoint2 k := by
  simp [contour51Arb4096UpperArcEndpointFirstThree]

/-- Analytic component inputs on one complete 4096 arc for all three residual orders.
The proven geometric boxes are fixed to the boxes from `SigmaContour51ArcGeometry`; this record
therefore asks only for the analytic function ranges, sound denominator ranges, and exact output
comparisons against the existing Arb endpoints. -/
structure Contour51Arb4096FirstThreeArcComponentBoxes (k : ℕ) where
  zetaBox : ComplexInterval
  zetaDerivativeBox : ComplexInterval
  digammaBox : ComplexInterval
  sNormSqPos : 0 <
    (ComplexInterval.normSqRange (contour51Arc4096SBox k)).lo
  sMinusOneNormSqPos : 0 <
    (ComplexInterval.normSqRange
      (ComplexInterval.sub (contour51Arc4096SBox k) contour51ArbOneBox)).lo
  zetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo
  zetaContains : ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    zetaBox.contains
      (riemannZeta (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))))
  zetaDerivativeContains :
    ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
      zetaDerivativeBox.contains
        (deriv riemannZeta (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))))
  digammaContains :
    ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
      digammaBox.contains (Complex.digamma
        (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)) / 2))
  parameterPowerNormSqPos : ∀ n : Fin 3,
    0 < (ComplexInterval.normSqRange
      (ComplexInterval.powI (contour51Arc4096ZBox k) (2 * n.val + 1))).lo
  composedLowerEndpoint : ∀ n : Fin 3,
    ((contour51Arb4096LowerArcEndpointFirstThree k n : ℚ) : ℝ) ≤
      (contour51ArbResidualIntegrandBox n.val
        (contour51Arc4096SBox k) zetaBox zetaDerivativeBox digammaBox contour51C5LogPiBox
        (contour51Arc4096ZBox k) sNormSqPos sMinusOneNormSqPos zetaNormSqPos
        (parameterPowerNormSqPos n)).re.lo
  composedUpperEndpoint : ∀ n : Fin 3,
    (contour51ArbResidualIntegrandBox n.val
      (contour51Arc4096SBox k) zetaBox zetaDerivativeBox digammaBox contour51C5LogPiBox
      (contour51Arc4096ZBox k) sNormSqPos sMinusOneNormSqPos zetaNormSqPos
      (parameterPowerNormSqPos n)).re.hi ≤
      ((contour51Arb4096UpperArcEndpointFirstThree k n : ℚ) : ℝ)

private theorem contour51Arb4096FirstThreeArcEvaluatorInclusion_at_arc
    {k : ℕ} (hk : k < 4096)
    (hbox : Contour51Arb4096FirstThreeArcComponentBoxes k) (n : Fin 3) :
    ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
      ((contour51Arb4096LowerArcEndpointFirstThree k n : ℚ) : ℝ) ≤
          (contour51OriginalAngularResidualIntegrand n.val (-Real.pi * u)).re ∧
        (contour51OriginalAngularResidualIntegrand n.val (-Real.pi * u)).re ≤
          ((contour51Arb4096UpperArcEndpointFirstThree k n : ℚ) : ℝ) := by
  intro u hu
  have hkLower : (0 : ℝ) ≤ (k : ℝ) / 4096 := by positivity
  have hkUpper : (((k + 1 : ℕ) : ℝ) / 4096) ≤ 1 := by
    have hkNat : k + 1 ≤ 4096 := Nat.succ_le_of_lt hk
    have hkCast : ((k + 1 : ℕ) : ℝ) ≤ (4096 : ℝ) := by exact_mod_cast hkNat
    calc
      ((k + 1 : ℕ) : ℝ) / 4096 ≤ (4096 : ℝ) / 4096 :=
        div_le_div_of_nonneg_right hkCast (by positivity)
      _ = 1 := by norm_num
  have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hkLower hu.1, le_trans hu.2 hkUpper⟩
  have hs := contour51Arc4096SBox_contains hk hu
  have hz := contour51Arc4096ZBox_contains hk hu
  have hBox := contour51ArbResidualIntegrandBox_contains n.val hu01 hs
    (hbox.zetaContains u hu) (hbox.zetaDerivativeContains u hu)
    (hbox.digammaContains u hu) contour51C5LogPiBox_contains
    hbox.sNormSqPos hbox.sMinusOneNormSqPos hbox.zetaNormSqPos hz
    (hbox.parameterPowerNormSqPos n) rfl rfl
  constructor
  · exact_mod_cast (le_trans (hbox.composedLowerEndpoint n) hBox.1.1)
  · exact_mod_cast (le_trans hBox.1.2 (hbox.composedUpperEndpoint n))

/-- Supplying all component records proves the exact three-order, all-arc Arb inclusion required
for the direct first-window determinant route. -/
theorem contour51Arb4096FirstThreeArcEvaluatorInclusion_of_component_boxes
    (hboxes : ∀ k : ℕ, k < 4096 → Contour51Arb4096FirstThreeArcComponentBoxes k) :
    contour51Arb4096FirstThreeArcEvaluatorInclusion := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simpa using contour51Arb4096FirstThreeArcEvaluatorInclusion_at_arc hk (hboxes k hk) 0
  · intro k hk
    simpa using contour51Arb4096FirstThreeArcEvaluatorInclusion_at_arc hk (hboxes k hk) 1
  · intro k hk
    simpa using contour51Arb4096FirstThreeArcEvaluatorInclusion_at_arc hk (hboxes k hk) 2

/-- The first central determinant has a strict absolute margin of `10⁻⁹` under the explicit
per-arc analytic records. The records are not supplied by this theorem. -/
theorem completedNative_sigmaPadeD_zero_pos_of_first_three_component_boxes
    (hboxes : ∀ k : ℕ, k < 4096 → Contour51Arb4096FirstThreeArcComponentBoxes k) :
    1 / 1000000000 < CarrySigmaPade.sigmaPadeD 0 0 := by
  have hArc := contour51Arb4096FirstThreeArcEvaluatorInclusion_of_component_boxes hboxes
  have hPath :=
    contour51ArbFirstThreeLowerPathResidualIntervalBounds_of_4096_arc_evaluator_inclusion hArc
  rcases completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals hPath with
    ⟨ts, hStrictMono, hRootBounds, hRootBoxes, hMargin⟩
  exact hMargin

#print axioms contour51Arb4096FirstThreeArcEvaluatorInclusion_at_arc
#print axioms contour51Arb4096FirstThreeArcEvaluatorInclusion_of_component_boxes
#print axioms completedNative_sigmaPadeD_zero_pos_of_first_three_component_boxes

end
end CarrySigmaObstruction
