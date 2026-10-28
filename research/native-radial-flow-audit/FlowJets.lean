import SourceJets
namespace CarryRadialFlow
open CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def flowJetPolynomial (a b c d : ℂ) (m : Fin 8) : ℂ :=
  ![0,a,0,3*b-a^3,0,5*c-5*a^2*b+a^5,0,
    7*d-7*a^2*c-7*a*b^2+7*a^4*b-a^7] m

/-- The first eight Taylor jets of the ACTUAL derived source response.
No diagnostic sequence replaces the canonical source. -/
theorem flow_first_eight (m : Fin 8) :
    tc flowResponse m=flowJetPolynomial
      (2*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))
      (2*(canonicalCompletedNativeLogDerivativeMoment 1:ℂ))
      (2*(canonicalCompletedNativeLogDerivativeMoment 2:ℂ))
      (2*(canonicalCompletedNativeLogDerivativeMoment 3:ℂ)) m := by
  let a : ℂ := 2*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)
  let b : ℂ := 2*(canonicalCompletedNativeLogDerivativeMoment 1:ℂ)
  let c : ℂ := 2*(canonicalCompletedNativeLogDerivativeMoment 2:ℂ)
  let d : ℂ := 2*(canonicalCompletedNativeLogDerivativeMoment 3:ℂ)
  change tc flowResponse m=flowJetPolynomial a b c d m
  have q0 : tc completedNativeOperatorLogDerivative 0=0 := by simpa using source_tc_even 0
  have q1 : tc completedNativeOperatorLogDerivative 1=a := by simpa using source_tc_odd 0
  have q2 : tc completedNativeOperatorLogDerivative 2=0 := by simpa using source_tc_even 1
  have q3 : tc completedNativeOperatorLogDerivative 3=b := by simpa using source_tc_odd 1
  have q4 : tc completedNativeOperatorLogDerivative 4=0 := by simpa using source_tc_even 2
  have q5 : tc completedNativeOperatorLogDerivative 5=c := by simpa using source_tc_odd 2
  have q6 : tc completedNativeOperatorLogDerivative 6=0 := by simpa using source_tc_even 3
  have q7 : tc completedNativeOperatorLogDerivative 7=d := by simpa using source_tc_odd 3
  have r0 : tc flowResponse 0=0 := by
    have h := flow_tc_recurrence 0
    norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7] at h
    linear_combination h
  have r1 : tc flowResponse 1=a := by
    have h := flow_tc_recurrence 1
    norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, r0] at h
    linear_combination h
  have r2 : tc flowResponse 2=0 := by
    have h := flow_tc_recurrence 2
    norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, r0, r1] at h
    linear_combination h
  have r3 : tc flowResponse 3=3*b-a^3 := by
    have h := flow_tc_recurrence 3
    norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, r0, r1, r2] at h
    linear_combination h
  have r4 : tc flowResponse 4=0 := by
    have h := flow_tc_recurrence 4
    norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, r0, r1, r2, r3] at h
    linear_combination h
  have r5 : tc flowResponse 5=5*c-5*a^2*b+a^5 := by
    have h := flow_tc_recurrence 5
    norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, r0, r1, r2, r3, r4] at h
    linear_combination h
  have r6 : tc flowResponse 6=0 := by
    have h := flow_tc_recurrence 6
    norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, r0, r1, r2, r3, r4, r5] at h
    linear_combination h
  have r7 : tc flowResponse 7=7*d-7*a^2*c-7*a*b^2+7*a^4*b-a^7 := by
    have h := flow_tc_recurrence 7
    norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, r0, r1, r2, r3, r4, r5, r6] at h
    linear_combination h
  fin_cases m
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7

end
end CarryRadialFlow
