import FlowJets
import IntegralCertificate

namespace CarryRadialFlow
open CarrySelfAdjointOperator CarryIntegralCertificate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

def flowWitness (a b c d : ℝ) : ℝ :=
  (49/1000000)*(3*b-a^3)-(7/500)*(5*c-5*a^2*b+a^5)+
    (7*d-7*a^2*c-7*a*b^2+7*a^4*b-a^7)

def slopeBox (n : ℕ) : Box := (Box.point 2).mul (logMomentBox n)
def firstFlowBox : Box := ((Box.point 3).mul (slopeBox 1)).add (((slopeBox 0).pow 3).neg)
def secondFlowBox : Box := (((Box.point 5).mul (slopeBox 2)).add
  ((((Box.point 5).mul ((slopeBox 0).pow 2)).mul (slopeBox 1)).neg)).add ((slopeBox 0).pow 5)
def thirdFlowBox : Box := (((((Box.point 7).mul (slopeBox 3)).add
  ((((Box.point 7).mul ((slopeBox 0).pow 2)).mul (slopeBox 2)).neg)).add
  ((((Box.point 7).mul (slopeBox 0)).mul ((slopeBox 1).pow 2)).neg)).add
  (((Box.point 7).mul ((slopeBox 0).pow 4)).mul (slopeBox 1))).add (((slopeBox 0).pow 7).neg)
def flowWitnessBox : Box := (((Box.rat 49 1000000).mul firstFlowBox).add
  (((Box.rat 7 500).mul secondFlowBox).neg)).add thirdFlowBox

theorem flowWitnessBox_negative : flowWitnessBox.neg.positive=true := by decide +kernel

/-- A strict inequality for the ORIGINAL source, from the existing exact
theta integral boxes. No checkpoint or Hankel positivity theorem is used. -/
theorem source_flow_witness_neg :
    flowWitness (2*canonicalCompletedNativeLogDerivativeMoment 0)
      (2*canonicalCompletedNativeLogDerivativeMoment 1)
      (2*canonicalCompletedNativeLogDerivativeMoment 2)
      (2*canonicalCompletedNativeLogDerivativeMoment 3)<0 := by
  have ha := mem_mul (mem_point 2) (mem_logMomentBox material_theta_integral_input 0)
  have hb := mem_mul (mem_point 2) (mem_logMomentBox material_theta_integral_input 1)
  have hc := mem_mul (mem_point 2) (mem_logMomentBox material_theta_integral_input 2)
  have hd := mem_mul (mem_point 2) (mem_logMomentBox material_theta_integral_input 3)
  have h1 := mem_add (mem_mul (mem_point 3) hb) (mem_neg (mem_pow ha 3))
  have h2 := mem_add (mem_add (mem_mul (mem_point 5) hc)
    (mem_neg (mem_mul (mem_mul (mem_point 5) (mem_pow ha 2)) hb))) (mem_pow ha 5)
  have h3 := mem_add (mem_add (mem_add (mem_add (mem_mul (mem_point 7) hd)
    (mem_neg (mem_mul (mem_mul (mem_point 7) (mem_pow ha 2)) hc)))
    (mem_neg (mem_mul (mem_mul (mem_point 7) ha) (mem_pow hb 2))))
    (mem_mul (mem_mul (mem_point 7) (mem_pow ha 4)) hb)) (mem_neg (mem_pow ha 7))
  have h := mem_add (mem_add (mem_mul (mem_rat 49 1000000) h1)
    (mem_neg (mem_mul (mem_rat 7 500) h2))) h3
  have hm : flowWitnessBox.Mem (flowWitness
      (2*canonicalCompletedNativeLogDerivativeMoment 0)
      (2*canonicalCompletedNativeLogDerivativeMoment 1)
      (2*canonicalCompletedNativeLogDerivativeMoment 2)
      (2*canonicalCompletedNativeLogDerivativeMoment 3)) := by
    dsimp only [flowWitnessBox,firstFlowBox,secondFlowBox,thirdFlowBox,slopeBox]
    convert h using 1
    norm_num only [Int.cast_ofNat]
    unfold flowWitness
    ring
  have hp := pos_of_mem (mem_neg hm) flowWitnessBox_negative
  linarith

/-- Negative mixed jet of the actual analytic flow response, with the
factorials and original source coefficients fixed in the Lean kernel. -/
theorem actual_flow_jet_witness_neg :
    ((49/1000000:ℂ)*tc flowResponse 3-(7/500:ℂ)*tc flowResponse 5+
      tc flowResponse 7).re<0 := by
  have h3 := flow_first_eight (3:Fin 8)
  have h5 := flow_first_eight (5:Fin 8)
  have h7 := flow_first_eight (7:Fin 8)
  norm_num [flowJetPolynomial] at h3 h5 h7
  have he : (49/1000000:ℂ)*tc flowResponse 3-(7/500:ℂ)*tc flowResponse 5+tc flowResponse 7=
      (flowWitness (2*canonicalCompletedNativeLogDerivativeMoment 0)
        (2*canonicalCompletedNativeLogDerivativeMoment 1)
        (2*canonicalCompletedNativeLogDerivativeMoment 2)
        (2*canonicalCompletedNativeLogDerivativeMoment 3):ℂ) := by
    rw [h3,h5,h7]
    unfold flowWitness
    push_cast
    ring
  rw [he]
  exact source_flow_witness_neg

end
end CarryRadialFlow
