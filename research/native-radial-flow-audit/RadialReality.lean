import CayleyFlow
import ResponseReality

namespace CarryRadialFlow
open CarrySelfAdjointOperator Filter Topology
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem original_rotated_response (z : ℂ) :
    completedNativeOperatorLogDerivative (Complex.I*z)=
      2*Complex.I*CarryCriticalTfvd.responseReadout z := by
  unfold CarryCriticalTfvd.responseReadout
  rw [source_normalized_response]
  ring_nf
  norm_num [Complex.I_sq]

/-- Radial reality comes from the EXISTING native-channel reflection after
completion. It is not imposed on the quotient as a positivity hypothesis. -/
theorem original_quotient_radial_real :
    ∀ᶠ t : ℝ in nhds 0,
      conj (completedNativeHermiteBiehlerChiralQuotient (Complex.I*(t:ℂ)))=
        completedNativeHermiteBiehlerChiralQuotient (Complex.I*(t:ℂ)) := by
  have ht : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)) (nhds 0) (nhds 0) := by
    simpa using ((Complex.continuous_ofReal.tendsto (0:ℝ)).const_mul Complex.I)
  filter_upwards [ht.eventually original_quotient_eq_cayley] with t he
  rw [he]
  unfold cayleyResponse
  rw [original_rotated_response]
  have hr := CarryMixedParity.response_real_ray t
  simp only [map_div₀,map_sub,map_add,map_mul,map_ofNat,Complex.conj_I,hr]
  have hn : (2:ℂ)*(-Complex.I)*CarryCriticalTfvd.responseReadout (t:ℂ)-(-Complex.I)=
      -(2*Complex.I*CarryCriticalTfvd.responseReadout (t:ℂ)-Complex.I) := by ring
  have hd : (2:ℂ)*(-Complex.I)*CarryCriticalTfvd.responseReadout (t:ℂ)+(-Complex.I)=
      -(2*Complex.I*CarryCriticalTfvd.responseReadout (t:ℂ)+Complex.I) := by ring
  rw [hn,hd,neg_div_neg_eq]

end
end CarryRadialFlow
