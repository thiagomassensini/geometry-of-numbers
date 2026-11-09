import SigmaContour51ArbContourBridge
import SigmaContour51ComplexIntervalDivision
import Mathlib.Tactic

/-!
# Component-box composition for the radius-51 Arb evaluator

This module composes explicit certified component boxes into a box for the original source
response and the `n = 0` residual integrand. Every enclosure of `s`, `ζ(s)`, `ζ'(s)`,
`digamma(s/2)`, `log π`, and the contour parameter remains an input hypothesis. The result
does not certify those component boxes or claim an Arb-to-Lean evaluator inclusion by itself.
-/

namespace CarrySigmaObstruction

open ZetaLean ZetaLean.ComplexInterval
open CarrySelfAdjointOperator Complex
open scoped Interval

noncomputable section
set_option autoImplicit false

def contour51ArbOneBox : ComplexInterval := ComplexInterval.exact 1 0

/-- Rational rectangle obtained by composing the five analytic factors in the exact
`xi'/xi` expression used by Arb. The division boxes use the interval squared-norm enclosures of
their denominator rectangles. -/
def contour51ArbSigmaXiLogDerivativeBox
    (sBox zetaBox zetaDerivativeBox digammaBox logPiBox : ComplexInterval)
    (sNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo)
    (sMinusOneNormSqPos : 0 < (ComplexInterval.normSqRange
      (ComplexInterval.sub sBox contour51ArbOneBox)).lo)
    (zetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo) :
    ComplexInterval :=
  let sMinusOneBox := ComplexInterval.sub sBox contour51ArbOneBox
  let invSBox := ComplexInterval.divBox contour51ArbOneBox sBox
    (ComplexInterval.normSqRange sBox) sNormSqPos
  let invSMinusOneBox := ComplexInterval.divBox contour51ArbOneBox sMinusOneBox
    (ComplexInterval.normSqRange sMinusOneBox) sMinusOneNormSqPos
  let gammaBox := ComplexInterval.smulQ (1 / 2) digammaBox
  let logPiTermBox := ComplexInterval.smulQ (-1 / 2) logPiBox
  let zetaLogDerivativeBox := ComplexInterval.divBox zetaDerivativeBox zetaBox
    (ComplexInterval.normSqRange zetaBox) zetaNormSqPos
  ((((invSBox.add invSMinusOneBox).add logPiTermBox).add gammaBox).add
    zetaLogDerivativeBox)

/-- The completed source response box, using `R = -(i/2) * xi'/xi`. -/
def contour51ArbOriginalResponseBox
    (sBox zetaBox zetaDerivativeBox digammaBox logPiBox : ComplexInterval)
    (sNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo)
    (sMinusOneNormSqPos : 0 < (ComplexInterval.normSqRange
      (ComplexInterval.sub sBox contour51ArbOneBox)).lo)
    (zetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo) :
    ComplexInterval :=
  (ComplexInterval.exact 0 (-1 / 2)).mul
    (contour51ArbSigmaXiLogDerivativeBox sBox zetaBox zetaDerivativeBox digammaBox logPiBox
      sNormSqPos sMinusOneNormSqPos zetaNormSqPos)

/-- The `n = 0` angular residual evaluator box, with a supplied rectangle for the contour
parameter `z`. -/
def contour51ArbN0ResidualIntegrandBox
    (sBox zetaBox zetaDerivativeBox digammaBox logPiBox parameterBox : ComplexInterval)
    (sNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo)
    (sMinusOneNormSqPos : 0 < (ComplexInterval.normSqRange
      (ComplexInterval.sub sBox contour51ArbOneBox)).lo)
    (zetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo)
    (parameterNormSqPos : 0 < (ComplexInterval.normSqRange parameterBox).lo) :
    ComplexInterval :=
  ComplexInterval.divBox
    (contour51ArbOriginalResponseBox sBox zetaBox zetaDerivativeBox digammaBox logPiBox
      sNormSqPos sMinusOneNormSqPos zetaNormSqPos)
    parameterBox (ComplexInterval.normSqRange parameterBox) parameterNormSqPos

/-- Generic residual quotient box. The denominator enclosure is the interval power
`parameterBox.powI (2*n+1)`, not a sampled approximation to the contour parameter. -/
def contour51ArbResidualIntegrandBox
    (n : ℕ)
    (sBox zetaBox zetaDerivativeBox digammaBox logPiBox parameterBox : ComplexInterval)
    (sNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo)
    (sMinusOneNormSqPos : 0 < (ComplexInterval.normSqRange
      (ComplexInterval.sub sBox contour51ArbOneBox)).lo)
    (zetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo)
    (parameterPowerNormSqPos : 0 < (ComplexInterval.normSqRange
      (ComplexInterval.powI parameterBox (2 * n + 1))).lo) :
    ComplexInterval :=
  ComplexInterval.divBox
    (contour51ArbOriginalResponseBox sBox zetaBox zetaDerivativeBox digammaBox logPiBox
      sNormSqPos sMinusOneNormSqPos zetaNormSqPos)
    (ComplexInterval.powI parameterBox (2 * n + 1))
    (ComplexInterval.normSqRange (ComplexInterval.powI parameterBox (2 * n + 1)))
    parameterPowerNormSqPos

theorem contour51ArbSigmaXiLogDerivativeBox_contains
    {s : ℂ}
    {sBox zetaBox zetaDerivativeBox digammaBox logPiBox : ComplexInterval}
    (hs : sBox.contains s)
    (hzeta : zetaBox.contains (riemannZeta s))
    (hzetaDerivative : zetaDerivativeBox.contains (deriv riemannZeta s))
    (hdigamma : digammaBox.contains (Complex.digamma (s / 2)))
    (hlogPi : logPiBox.contains (Complex.log (Real.pi : ℂ)))
    (hsNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo)
    (hsMinusOneNormSqPos :
      0 < (ComplexInterval.normSqRange
        (ComplexInterval.sub sBox contour51ArbOneBox)).lo)
    (hzetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo) :
    (contour51ArbSigmaXiLogDerivativeBox sBox zetaBox zetaDerivativeBox digammaBox logPiBox
      hsNormSqPos hsMinusOneNormSqPos hzetaNormSqPos).contains
      (1 / s + 1 / (s - 1) - (Complex.log (Real.pi : ℂ)) / 2 +
        Complex.digamma (s / 2) / 2 + deriv riemannZeta s / riemannZeta s) := by
  have hOne : contour51ArbOneBox.contains (1 : ℂ) := by
    norm_num [contour51ArbOneBox, ComplexInterval.exact, Interval.exact,
      ComplexInterval.contains, Interval.contains]
  let sMinusOneBox := ComplexInterval.sub sBox contour51ArbOneBox
  have hsMinusOne : sMinusOneBox.contains (s - 1) := by
    simpa [sMinusOneBox, contour51ArbOneBox] using
      (ComplexInterval.contains_sub hs hOne)
  have hsInv :
      (ComplexInterval.divBox contour51ArbOneBox sBox
        (ComplexInterval.normSqRange sBox) hsNormSqPos).contains (1 / s) := by
    exact ComplexInterval.contains_divBox hOne hs
      (ComplexInterval.contains_normSqRange hs) hsNormSqPos
  have hsMinusOneInv :
      (ComplexInterval.divBox contour51ArbOneBox sMinusOneBox
        (ComplexInterval.normSqRange sMinusOneBox) hsMinusOneNormSqPos).contains
          (1 / (s - 1)) := by
    exact ComplexInterval.contains_divBox hOne hsMinusOne
      (ComplexInterval.contains_normSqRange hsMinusOne) hsMinusOneNormSqPos
  have hlogPiTerm :
      (ComplexInterval.smulQ (-1 / 2) logPiBox).contains
        (-(Complex.log (Real.pi : ℂ)) / 2) := by
    have h := ComplexInterval.contains_smulQ (q := (-1 / 2 : ℚ)) hlogPi
    convert h using 1
    push_cast
    ring
  have hdigammaTerm :
      (ComplexInterval.smulQ (1 / 2) digammaBox).contains
        (Complex.digamma (s / 2) / 2) := by
    have h := ComplexInterval.contains_smulQ (q := (1 / 2 : ℚ)) hdigamma
    convert h using 1
    push_cast
    ring
  have hzetaLogDerivative :
      (ComplexInterval.divBox zetaDerivativeBox zetaBox
        (ComplexInterval.normSqRange zetaBox) hzetaNormSqPos).contains
        (deriv riemannZeta s / riemannZeta s) := by
    exact ComplexInterval.contains_divBox hzetaDerivative hzeta
      (ComplexInterval.contains_normSqRange hzeta) hzetaNormSqPos
  have hsum₁ := ComplexInterval.contains_add hsInv hsMinusOneInv
  have hsum₂ := ComplexInterval.contains_add hsum₁ hlogPiTerm
  have hsum₃ := ComplexInterval.contains_add hsum₂ hdigammaTerm
  have hsum₄ := ComplexInterval.contains_add hsum₃ hzetaLogDerivative
  convert hsum₄ using 1
  simp only [contour51ArbSigmaXiLogDerivativeBox, sMinusOneBox,
    contour51ArbOneBox]
  congr 1
  ring

theorem contour51ArbOriginalResponseBox_contains
    {s : ℂ}
    {sBox zetaBox zetaDerivativeBox digammaBox logPiBox : ComplexInterval}
    (hs : sBox.contains s)
    (hzeta : zetaBox.contains (riemannZeta s))
    (hzetaDerivative : zetaDerivativeBox.contains (deriv riemannZeta s))
    (hdigamma : digammaBox.contains (Complex.digamma (s / 2)))
    (hlogPi : logPiBox.contains (Complex.log (Real.pi : ℂ)))
    (hsNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo)
    (hsMinusOneNormSqPos :
      0 < (ComplexInterval.normSqRange
        (ComplexInterval.sub sBox contour51ArbOneBox)).lo)
    (hzetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo) :
    (contour51ArbOriginalResponseBox sBox zetaBox zetaDerivativeBox digammaBox logPiBox
      hsNormSqPos hsMinusOneNormSqPos hzetaNormSqPos).contains
      (-(Complex.I / 2 : ℂ) *
        (1 / s + 1 / (s - 1) - (Complex.log (Real.pi : ℂ)) / 2 +
          Complex.digamma (s / 2) / 2 + deriv riemannZeta s / riemannZeta s)) := by
  have hFactor : (ComplexInterval.exact 0 (-1 / 2)).contains (-(Complex.I / 2 : ℂ)) := by
    norm_num [ComplexInterval.exact, Interval.exact,
      ComplexInterval.contains, Interval.contains]
  exact ComplexInterval.contains_mul hFactor
    (contour51ArbSigmaXiLogDerivativeBox_contains hs hzeta hzetaDerivative
      hdigamma hlogPi hsNormSqPos hsMinusOneNormSqPos hzetaNormSqPos)

theorem contour51ArbOriginalResponseBox_contains_lower_path
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    {sBox zetaBox zetaDerivativeBox digammaBox logPiBox : ComplexInterval}
    (hs : sBox.contains
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))))
    (hzeta : zetaBox.contains (riemannZeta
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)))) )
    (hzetaDerivative : zetaDerivativeBox.contains (deriv riemannZeta
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)))))
    (hdigamma : digammaBox.contains (Complex.digamma
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)) / 2)))
    (hlogPi : logPiBox.contains (Complex.log (Real.pi : ℂ)))
    (hsNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo)
    (hsMinusOneNormSqPos :
      0 < (ComplexInterval.normSqRange
        (ComplexInterval.sub sBox contour51ArbOneBox)).lo)
    (hzetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo) :
    (contour51ArbOriginalResponseBox sBox zetaBox zetaDerivativeBox digammaBox logPiBox
      hsNormSqPos hsMinusOneNormSqPos hzetaNormSqPos).contains
      (contour51OriginalResponse (circleMap 0 51 (-Real.pi * u))) := by
  rw [contour51OriginalResponse_eq_arb_formula_lower_path hu]
  exact contour51ArbOriginalResponseBox_contains hs hzeta hzetaDerivative hdigamma
    hlogPi hsNormSqPos hsMinusOneNormSqPos hzetaNormSqPos

theorem contour51ArbN0ResidualIntegrandBox_contains
    {u : ℝ} {s z : ℂ}
    {sBox zetaBox zetaDerivativeBox digammaBox logPiBox parameterBox : ComplexInterval}
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hs : sBox.contains s)
    (hzeta : zetaBox.contains (riemannZeta s))
    (hzetaDerivative : zetaDerivativeBox.contains (deriv riemannZeta s))
    (hdigamma : digammaBox.contains (Complex.digamma (s / 2)))
    (hlogPi : logPiBox.contains (Complex.log (Real.pi : ℂ)))
    (hsNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo)
    (hsMinusOneNormSqPos :
      0 < (ComplexInterval.normSqRange
        (ComplexInterval.sub sBox contour51ArbOneBox)).lo)
    (hzetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo)
    (hz : parameterBox.contains z)
    (hzNormSqPos : 0 < (ComplexInterval.normSqRange parameterBox).lo)
    (hsPath : s = operatorHeightParameter (circleMap 0 51 (-Real.pi * u)))
    (hzPath : z = circleMap 0 51 (-Real.pi * u)) :
    (contour51ArbN0ResidualIntegrandBox sBox zetaBox zetaDerivativeBox digammaBox logPiBox
      parameterBox hsNormSqPos hsMinusOneNormSqPos hzetaNormSqPos hzNormSqPos).contains
      (contour51OriginalAngularResidualIntegrand 0 (-Real.pi * u)) := by
  have hResponse := contour51ArbOriginalResponseBox_contains_lower_path hu
    (by simpa [hsPath] using hs)
    (by simpa [hsPath] using hzeta)
    (by simpa [hsPath] using hzetaDerivative)
    (by simpa [hsPath] using hdigamma)
    hlogPi hsNormSqPos hsMinusOneNormSqPos hzetaNormSqPos
  have hNormSq := ComplexInterval.contains_normSqRange hz
  have hQuotient := ComplexInterval.contains_divBox hResponse hz hNormSq hzNormSqPos
  simpa [contour51ArbN0ResidualIntegrandBox, contour51ArbOriginalResponseBox,
    contour51ArbSigmaXiLogDerivativeBox, contour51OriginalAngularResidualIntegrand,
    contour51OriginalResidualQuotient, hsPath, hzPath, contour51ArbOneBox,
    sub_eq_add_neg, pow_one] using hQuotient

/-- For every order `n`, component boxes for the source response and contour parameter compose
to a pointwise box for the original residual quotient. Positivity of the squared-norm interval
for the powered parameter box is an explicit hypothesis. -/
theorem contour51ArbResidualIntegrandBox_contains
    (n : ℕ) {u : ℝ} {s z : ℂ}
    {sBox zetaBox zetaDerivativeBox digammaBox logPiBox parameterBox : ComplexInterval}
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hs : sBox.contains s)
    (hzeta : zetaBox.contains (riemannZeta s))
    (hzetaDerivative : zetaDerivativeBox.contains (deriv riemannZeta s))
    (hdigamma : digammaBox.contains (Complex.digamma (s / 2)))
    (hlogPi : logPiBox.contains (Complex.log (Real.pi : ℂ)))
    (hsNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo)
    (hsMinusOneNormSqPos : 0 < (ComplexInterval.normSqRange
      (ComplexInterval.sub sBox contour51ArbOneBox)).lo)
    (hzetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo)
    (hz : parameterBox.contains z)
    (hParameterPowerNormSqPos : 0 < (ComplexInterval.normSqRange
      (ComplexInterval.powI parameterBox (2 * n + 1))).lo)
    (hsPath : s = operatorHeightParameter (circleMap 0 51 (-Real.pi * u)))
    (hzPath : z = circleMap 0 51 (-Real.pi * u)) :
    (contour51ArbResidualIntegrandBox n sBox zetaBox zetaDerivativeBox digammaBox logPiBox
      parameterBox hsNormSqPos hsMinusOneNormSqPos hzetaNormSqPos
      hParameterPowerNormSqPos).contains
      (contour51OriginalAngularResidualIntegrand n (-Real.pi * u)) := by
  have hResponse := contour51ArbOriginalResponseBox_contains_lower_path hu
    (by simpa [hsPath] using hs)
    (by simpa [hsPath] using hzeta)
    (by simpa [hsPath] using hzetaDerivative)
    (by simpa [hsPath] using hdigamma)
    hlogPi hsNormSqPos hsMinusOneNormSqPos hzetaNormSqPos
  have hPower := ComplexInterval.contains_powI hz (2 * n + 1)
  have hNormSq := ComplexInterval.contains_normSqRange hPower
  have hQuotient := ComplexInterval.contains_divBox hResponse hPower hNormSq
    hParameterPowerNormSqPos
  simpa [contour51ArbResidualIntegrandBox, contour51ArbOriginalResponseBox,
    contour51ArbSigmaXiLogDerivativeBox, contour51OriginalAngularResidualIntegrand,
    contour51OriginalResidualQuotient, hsPath, hzPath, contour51ArbOneBox] using hQuotient

/-- A certificate record for the `n = 0` integrand on one complete closed arc. Its fields are
component-box hypotheses plus exact rational comparisons of the composed output box with the
exported Arb endpoints. This is only a composition interface: no field is supplied by the endpoint
table arithmetic alone. -/
structure Contour51Arb4096N0ArcComponentBoxes (k : ℕ) where
  sBox : ComplexInterval
  zetaBox : ComplexInterval
  zetaDerivativeBox : ComplexInterval
  digammaBox : ComplexInterval
  logPiBox : ComplexInterval
  parameterBox : ComplexInterval
  sNormSqPos : 0 < (ComplexInterval.normSqRange sBox).lo
  sMinusOneNormSqPos :
    0 < (ComplexInterval.normSqRange
      (ComplexInterval.sub sBox contour51ArbOneBox)).lo
  zetaNormSqPos : 0 < (ComplexInterval.normSqRange zetaBox).lo
  parameterNormSqPos : 0 < (ComplexInterval.normSqRange parameterBox).lo
  sContains : ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    sBox.contains (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)))
  zetaContains : ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    zetaBox.contains (riemannZeta (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))))
  zetaDerivativeContains :
    ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
      zetaDerivativeBox.contains
        (deriv riemannZeta (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))))
  digammaContains : ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    digammaBox.contains (Complex.digamma
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u)) / 2))
  logPiContains : logPiBox.contains (Complex.log (Real.pi : ℂ))
  parameterContains : ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
    parameterBox.contains (circleMap 0 51 (-Real.pi * u))
  composedLowerEndpoint :
    ((contour51Arb4096LowerArcEndpoint0 k : ℚ) : ℝ) ≤
      (contour51ArbN0ResidualIntegrandBox sBox zetaBox zetaDerivativeBox digammaBox
        logPiBox parameterBox sNormSqPos sMinusOneNormSqPos zetaNormSqPos
        parameterNormSqPos).re.lo
  composedUpperEndpoint :
    (contour51ArbN0ResidualIntegrandBox sBox zetaBox zetaDerivativeBox digammaBox
      logPiBox parameterBox sNormSqPos sMinusOneNormSqPos zetaNormSqPos
      parameterNormSqPos).re.hi ≤ ((contour51Arb4096UpperArcEndpoint0 k : ℚ) : ℝ)

theorem contour51Arb4096N0ArcEvaluatorInclusion_of_component_boxes
    {k : ℕ} (hk : k < 4096) (hbox : Contour51Arb4096N0ArcComponentBoxes k) :
    ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
      ((contour51Arb4096LowerArcEndpoint0 k : ℚ) : ℝ) ≤
          (contour51OriginalAngularResidualIntegrand 0 (-Real.pi * u)).re ∧
        (contour51OriginalAngularResidualIntegrand 0 (-Real.pi * u)).re ≤
          ((contour51Arb4096UpperArcEndpoint0 k : ℚ) : ℝ) := by
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
  have hBox := contour51ArbN0ResidualIntegrandBox_contains hu01
    (hbox.sContains u hu) (hbox.zetaContains u hu) (hbox.zetaDerivativeContains u hu)
    (hbox.digammaContains u hu) hbox.logPiContains hbox.sNormSqPos
    hbox.sMinusOneNormSqPos hbox.zetaNormSqPos (hbox.parameterContains u hu)
    hbox.parameterNormSqPos rfl rfl
  constructor
  · exact_mod_cast (le_trans hbox.composedLowerEndpoint hBox.1.1)
  · exact_mod_cast (le_trans hBox.1.2 hbox.composedUpperEndpoint)

/-- If such explicit component-box certificates are supplied for every closed 4096 arc, they
prove the `n = 0` conjunct of the existing first-three Arb-to-Lean inclusion proposition. The
certificates themselves remain open. -/
theorem contour51Arb4096N0AllArcEvaluatorInclusion_of_component_boxes
    (hboxes : ∀ k : ℕ, k < 4096 → Contour51Arb4096N0ArcComponentBoxes k) :
    ∀ k : ℕ, k < 4096 → ∀ u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096),
      ((contour51Arb4096LowerArcEndpoint0 k : ℚ) : ℝ) ≤
          (contour51OriginalAngularResidualIntegrand 0 (-Real.pi * u)).re ∧
        (contour51OriginalAngularResidualIntegrand 0 (-Real.pi * u)).re ≤
          ((contour51Arb4096UpperArcEndpoint0 k : ℚ) : ℝ) := by
  intro k hk
  exact contour51Arb4096N0ArcEvaluatorInclusion_of_component_boxes hk (hboxes k hk)

#print axioms contour51ArbSigmaXiLogDerivativeBox_contains
#print axioms contour51ArbOriginalResponseBox_contains
#print axioms contour51ArbOriginalResponseBox_contains_lower_path
#print axioms contour51ArbN0ResidualIntegrandBox_contains
#print axioms contour51ArbResidualIntegrandBox_contains
#print axioms contour51Arb4096N0ArcEvaluatorInclusion_of_component_boxes
#print axioms contour51Arb4096N0AllArcEvaluatorInclusion_of_component_boxes

end
end CarrySigmaObstruction
