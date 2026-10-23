import GammaValueBoxes

namespace CarryC3Gamma
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

/-- Only the already existing non-Gamma part of Xi, with original parameters. -/
def xiBeforeGamma (w : ℂ) : ℂ :=
  (1/2:ℂ)*operatorHeightParameter w*(operatorHeightParameter w-1)*
    Complex.exp (-(operatorHeightParameter w/2)*(Real.log Real.pi:ℂ))

theorem native_xi_gamma_factorization (w : ℂ) :
    nativeXiCompletionFactor w = xiBeforeGamma w*nativeGamma w := rfl

/-- Exact factorization of the C3 multiplier already used in the complete
TFVD trace. It does not change the chart, the Gamma argument, or the source. -/
theorem c3_value_multiplier_gamma_factorization (w : ℂ) :
    valueMultiplier w = (xiBeforeGamma w/cpChartFactor 3 (operatorHeightParameter w))*
      nativeGamma w := by
  rw [valueMultiplier,native_xi_gamma_factorization]
  ring

end
end CarryC3Gamma
