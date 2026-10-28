import SourceJets
import CarrySelfAdjointOperator.CompletedNativeChiralPickFactorization

namespace CarryRadialFlow
open CarrySelfAdjointOperator Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def cayleyResponse (z : ℂ) : ℂ :=
  (completedNativeOperatorLogDerivative z-Complex.I)/
    (completedNativeOperatorLogDerivative z+Complex.I)

theorem original_quotient_analytic :
    AnalyticAt ℂ completedNativeHermiteBiehlerChiralQuotient 0 := by
  have hf := completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  unfold completedNativeHermiteBiehlerChiralQuotient
    completedNativePositiveHermiteBiehlerCoordinate completedNativeNegativeHermiteBiehlerCoordinate
  apply (hf.deriv.neg.fun_sub (analyticAt_const.fun_mul hf)).div
    (hf.deriv.neg.fun_add (analyticAt_const.fun_mul hf))
  have hp : completedNativePositiveHermiteBiehlerCoordinate 0≠0 := by
    rw [completedNativePositiveHermiteBiehlerCoordinate_zero]
    exact mul_ne_zero Complex.I_ne_zero completedNativeOperatorCharacteristic_zero_ne_zero
  exact hp

/-- The existing original chiral quotient is the Cayley readout of the
existing logarithmic derivative, locally at its regular center. -/
theorem original_quotient_eq_cayley :
    completedNativeHermiteBiehlerChiralQuotient =ᶠ[nhds 0] cayleyResponse := by
  filter_upwards [completedNativeChiralPickFactorization_eventually_regular] with z hz
  have hf := hz.2.1
  have hp := hz.2.2
  have hd : completedNativeOperatorLogDerivative z+Complex.I≠0 := by
    intro h
    apply hp
    unfold completedNativePositiveHermiteBiehlerCoordinate
    have he : (completedNativeOperatorLogDerivative z+Complex.I)*
        completedNativeOperatorCharacteristic z=
        -deriv completedNativeOperatorCharacteristic z+
          Complex.I*completedNativeOperatorCharacteristic z := by
      unfold completedNativeOperatorLogDerivative
      field_simp [hf]
    rw [h,zero_mul] at he
    exact he.symm
  unfold completedNativeHermiteBiehlerChiralQuotient cayleyResponse
  unfold completedNativePositiveHermiteBiehlerCoordinate at hp
  unfold completedNativePositiveHermiteBiehlerCoordinate
    completedNativeNegativeHermiteBiehlerCoordinate
  unfold completedNativeOperatorLogDerivative at hd ⊢
  field_simp [hf,hp,hd]

/-- Exact derivative of the source Cayley response. This is an identity,
not a positivity assumption about its two-argument kernel. -/
theorem cayley_flow_equation :
    ∀ᶠ z : ℂ in nhds 0,
      z*deriv cayleyResponse z=2*Complex.I*flowResponse z*cayleyResponse z := by
  have hc : ContinuousAt (fun z => completedNativeOperatorLogDerivative z+Complex.I) 0 := by
    exact nativeSourceLogSlope_analyticAt.continuousAt.add continuousAt_const
  have hc2 : ContinuousAt (fun z => 1+completedNativeOperatorLogDerivative z^2) 0 := by
    exact continuousAt_const.add (nativeSourceLogSlope_analyticAt.pow 2).continuousAt
  have hd : completedNativeOperatorLogDerivative 0+Complex.I≠0 := by simp [source_zero]
  have hd2 : (1+completedNativeOperatorLogDerivative 0^2:ℂ)≠0 := by simp [source_zero]
  filter_upwards [nativeSourceLogSlope_analyticAt.eventually_analyticAt,
    hc.eventually_ne hd,hc2.eventually_ne hd2] with z hz hn hquad
  have he := ((hz.differentiableAt.hasDerivAt.sub_const Complex.I).div
    (hz.differentiableAt.hasDerivAt.add_const Complex.I) hn).deriv
  change deriv cayleyResponse z=_ at he
  rw [he]
  unfold cayleyResponse flowResponse
  field_simp [hn,hquad]
  ring_nf
  norm_num [Complex.I_sq]

/-- The diagnostic flow is genuinely attached to the original quotient;
the derivative is transported through the proved equality of germs. -/
theorem original_quotient_flow_equation :
    ∀ᶠ z : ℂ in nhds 0,
      z*deriv completedNativeHermiteBiehlerChiralQuotient z=
        2*Complex.I*flowResponse z*completedNativeHermiteBiehlerChiralQuotient z := by
  filter_upwards [original_quotient_eq_cayley,
    original_quotient_eq_cayley.deriv,cayley_flow_equation] with z hz hdz he
  rw [hz,hdz]
  exact he

end
end CarryRadialFlow
