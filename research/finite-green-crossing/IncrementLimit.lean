import MixedEnergy

namespace CarryFiniteGreen
open CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem adjacent_points_difference (k : ℕ) :
    canonicalCompletedC3RadialTiltPoint k 1-canonicalCompletedC3RadialTiltPoint k 0=
      canonicalCompletedC3RadialTiltPoint k 0 := by
  rw [canonicalCompletedC3RadialTiltPoint_eq_I_mul_im k 1,
    canonicalCompletedC3RadialTiltPoint_eq_I_mul_im k 0]
  simp only [canonicalCompletedC3RadialTiltPoint_im,Nat.cast_one,Nat.cast_zero,zero_add]
  push_cast
  ring

theorem radial_point_scaled (k : ℕ) :
    ((k : ℂ)+1)*canonicalCompletedC3RadialTiltPoint k 0=Complex.I := by
  rw [canonicalCompletedC3RadialTiltPoint_eq_I_mul_im k 0]
  simp only [canonicalCompletedC3RadialTiltPoint_im,Nat.cast_zero,zero_add]
  push_cast
  have hk : (k : ℂ)+1≠0 := by exact_mod_cast (show (k : ℝ)+1≠0 by positivity)
  field_simp [hk]

theorem scaled_increment_dslope (k : ℕ) :
    ((k : ℂ)+1)*responseIncrement k=Complex.I*dslope nativeResponse
      (canonicalCompletedC3RadialTiltPoint k 0) (canonicalCompletedC3RadialTiltPoint k 1) := by
  have h := sub_smul_dslope nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)
    (canonicalCompletedC3RadialTiltPoint k 1)
  change (_-_)*dslope nativeResponse _ _=responseIncrement k at h
  rw [adjacent_points_difference] at h
  rw [← h,← mul_assoc,radial_point_scaled]

theorem scaled_response_dslope (k : ℕ) :
    ((k : ℂ)+1)*nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)=
      Complex.I*dslope nativeResponse 0 (canonicalCompletedC3RadialTiltPoint k 0) := by
  have h := sub_smul_dslope nativeResponse 0 (canonicalCompletedC3RadialTiltPoint k 0)
  have hz : nativeResponse 0=0 := completedNativeGreenNormalizedResponse_zero
  simp only [smul_eq_mul,sub_zero,hz] at h
  rw [← h,← mul_assoc,radial_point_scaled]

theorem native_derivative_zero : deriv nativeResponse 0=
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simpa [nativeResponse,completedNativeGreenResponseTaylorCoefficient,iteratedDeriv_one] using
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0

theorem scaled_increment_limit :
    Tendsto (fun (k : ℕ) => ((k : ℂ)+1)*responseIncrement k) atTop
      (nhds (Complex.I*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  have hp := (canonicalCompletedC3RadialTiltPoint_tendsto_zero 0).prodMk_nhds
    (canonicalCompletedC3RadialTiltPoint_tendsto_zero 1)
  have h := (completedGreenDslope_tendsto_prod_of_analyticAt
    completedNativeGreenNormalizedResponse_analyticAt).comp hp
  rw [native_derivative_zero] at h
  simpa only [Function.comp_def,← scaled_increment_dslope] using h.const_mul Complex.I

theorem scaled_response_limit :
    Tendsto (fun (k : ℕ) => ((k : ℂ)+1)*nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)) atTop
      (nhds (Complex.I*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  have hp := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0)).prodMk_nhds
    (canonicalCompletedC3RadialTiltPoint_tendsto_zero 0)
  have h := (completedGreenDslope_tendsto_prod_of_analyticAt
    completedNativeGreenNormalizedResponse_analyticAt).comp hp
  rw [native_derivative_zero] at h
  simpa only [Function.comp_def,← scaled_response_dslope] using h.const_mul Complex.I

theorem increment_ruler_limit : Tendsto (fun (k : ℕ) => ((k : ℝ)+1)*(responseIncrement k).im) atTop
    (nhds (canonicalCompletedNativeLogDerivativeMoment 0)) := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp scaled_increment_limit
  simpa [Function.comp_def,Complex.mul_im] using h

theorem incident_ruler_limit : Tendsto (fun (k : ℕ) => ((k : ℝ)+1)*
      (nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)).im) atTop
    (nhds (canonicalCompletedNativeLogDerivativeMoment 0)) := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp scaled_response_limit
  simpa [Function.comp_def,Complex.mul_im] using h

theorem mixed_energy_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) :
    Tendsto (fun (k : ℕ) => (physicalForm (reconstructedBulk 0 η k initialInput)
      (reconstructedResidual 0 η k initialInput)).re) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 0*greenBudget η)) := by
  have heq : (fun (k : ℕ) => (physicalForm (reconstructedBulk 0 η k initialInput)
      (reconstructedResidual 0 η k initialInput)).re) =ᶠ[atTop]
      (fun (k : ℕ) => ((k : ℝ)+1)*(responseIncrement k).im*greenBudget η) := by
    filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 2] with k hk
    exact initial_mixed_real η hη0 hη1 k (hk ⟨0,by omega⟩).2.1 (hk ⟨0,by omega⟩).2.2
      (hk ⟨1,by omega⟩).2.1 (hk ⟨1,by omega⟩).2.2
  exact (increment_ruler_limit.mul_const (greenBudget η)).congr' heq.symm

theorem bulk_energy_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) :
    Tendsto (fun (k : ℕ) => (physicalForm (reconstructedBulk 0 η k initialInput)
      (reconstructedBulk 0 η k initialInput)).re) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 0*(1-2*greenBudget η))) := by
  have heq : (fun (k : ℕ) => (physicalForm (reconstructedBulk 0 η k initialInput)
      (reconstructedBulk 0 η k initialInput)).re) =ᶠ[atTop]
      (fun (k : ℕ) => ((k : ℝ)+1)*(nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)).im-
        2*(((k : ℝ)+1)*(responseIncrement k).im*greenBudget η)) := by
    filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 2] with k hk
    exact initial_bulk_real η hη0 hη1 k (hk ⟨0,by omega⟩).2.1 (hk ⟨0,by omega⟩).2.2
      (hk ⟨1,by omega⟩).2.1 (hk ⟨1,by omega⟩).2.2
  have h := incident_ruler_limit.sub ((increment_ruler_limit.mul_const (greenBudget η)).const_mul 2)
  convert h.congr' heq.symm using 1
  ring

theorem source_energy_limit :
    Tendsto (fun (k : ℕ) => (physicalForm (projectiveLegs k 0) (projectiveLegs k 0)).re) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 0)) := by
  have heq : (fun (k : ℕ) => (physicalForm (projectiveLegs k 0) (projectiveLegs k 0)).re) =ᶠ[atTop]
      (fun (k : ℕ) => ((k : ℝ)+1)*(nativeResponse (canonicalCompletedC3RadialTiltPoint k 0)).im) := by
    filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 1] with k hk
    exact initial_source_energy k (hk ⟨0,by omega⟩).2.1 (hk ⟨0,by omega⟩).2.2
  exact incident_ruler_limit.congr' heq.symm

end
end CarryFiniteGreen
