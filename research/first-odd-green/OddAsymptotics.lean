import OddPortOverlap
import IncrementLimit

namespace CarryFirstOddGreen
open CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem node_regular_eventually : ∀ᶠ k : ℕ in atTop, nodeRegular k := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 3] with k hk
  exact fun i => (hk i).2

theorem adjacent_increment_step (k j : ℕ) :
    canonicalCompletedC3RadialTiltPoint k (j+1)-canonicalCompletedC3RadialTiltPoint k j=
      canonicalCompletedC3RadialTiltPoint k 0 := by
  rw [canonicalCompletedC3RadialTiltPoint_eq_I_mul_im k (j+1),
    canonicalCompletedC3RadialTiltPoint_eq_I_mul_im k j,
    canonicalCompletedC3RadialTiltPoint_eq_I_mul_im k 0]
  simp only [canonicalCompletedC3RadialTiltPoint_im,Nat.cast_zero,zero_add,Nat.cast_add,Nat.cast_one]
  push_cast
  ring

theorem scaled_increment_basis (k j : ℕ) :
    ((k : ℂ)+1)*increment k j=Complex.I*dslope nativeResponse
      (canonicalCompletedC3RadialTiltPoint k j) (canonicalCompletedC3RadialTiltPoint k (j+1)) := by
  have h := sub_smul_dslope nativeResponse (canonicalCompletedC3RadialTiltPoint k j)
    (canonicalCompletedC3RadialTiltPoint k (j+1))
  change (_-_)*dslope nativeResponse _ _=increment k j at h
  rw [adjacent_increment_step] at h
  rw [← h,← mul_assoc,radial_point_scaled]

theorem increment_basis_limit (j : ℕ) :
    Tendsto (fun (k : ℕ) => ((k : ℂ)+1)*increment k j) atTop
      (nhds (Complex.I*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  have hp := (canonicalCompletedC3RadialTiltPoint_tendsto_zero j).prodMk_nhds
    (canonicalCompletedC3RadialTiltPoint_tendsto_zero (j+1))
  have h := (completedGreenDslope_tendsto_prod_of_analyticAt
    completedNativeGreenNormalizedResponse_analyticAt).comp hp
  rw [native_derivative_zero] at h
  simpa only [Function.comp_def,← scaled_increment_basis] using h.const_mul Complex.I

theorem odd_mixed_scaled_exact (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (k : ℕ) (hreg : nodeRegular k) :
    physicalForm (oddBulk η k) (oddResidual η k)/((k : ℂ)+1)^2=
      -Complex.I*(((k : ℂ)+1)*increment k 1*portOverlap η 1-
        ((k : ℂ)+1)*increment k 0*portOverlap η 0) := by
  rw [odd_mixed_exact η hη0 hη1 k hreg]
  have hk : (k : ℂ)+1≠0 := by exact_mod_cast (show (k : ℝ)+1≠0 by positivity)
  field_simp [hk]

/-- Leading growth of the original mixed crossing, not an all-order sign law. -/
theorem odd_mixed_scaled_complex_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) :
    Tendsto (fun (k : ℕ) => physicalForm (oddBulk η k) (oddResidual η k)/((k : ℂ)+1)^2)
      atTop (nhds ((canonicalCompletedNativeLogDerivativeMoment 0*oddCoefficient η : ℝ) : ℂ)) := by
  have h := (((increment_basis_limit 1).mul_const (portOverlap η 1)).sub
    ((increment_basis_limit 0).mul_const (portOverlap η 0))).const_mul (-Complex.I)
  have ht : -Complex.I*(Complex.I*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*portOverlap η 1-
      Complex.I*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*portOverlap η 0)=
      ((canonicalCompletedNativeLogDerivativeMoment 0*oddCoefficient η : ℝ) : ℂ) := by
    calc
      _ = (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*(portOverlap η 1-portOverlap η 0) := by
        linear_combination -((canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*
          (portOverlap η 1-portOverlap η 0))*Complex.I_mul_I
      _ = _ := by rw [overlap_difference η hη0.le hη1]; push_cast; rfl
  rw [ht] at h
  apply h.congr'
  filter_upwards [node_regular_eventually] with k hk
  exact (odd_mixed_scaled_exact η hη0 hη1 k hk).symm

theorem complex_real_div (z : ℂ) (a : ℝ) : (z/(a : ℂ)).re=z.re/a := by
  rw [div_eq_mul_inv,← Complex.ofReal_inv,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rfl

theorem odd_mixed_scaled_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) :
    Tendsto (fun (k : ℕ) => (physicalForm (oddBulk η k) (oddResidual η k)).re/((k : ℝ)+1)^2)
      atTop (nhds (canonicalCompletedNativeLogDerivativeMoment 0*oddCoefficient η)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (odd_mixed_scaled_complex_limit η hη0 hη1)
  simpa only [Function.comp_def,← Complex.ofReal_natCast,← Complex.ofReal_one,
    ← Complex.ofReal_add,← Complex.ofReal_pow,complex_real_div,Complex.ofReal_re] using h

theorem form_same_power (m : ℕ) (x y : PhysicalPair) :
    physicalForm (pairPower m x) (pairPower m y)=physicalForm x y := by
  change (2 : ℂ)⁻¹*(inner ℂ (powerIsometry m x.1) (powerIsometry m y.1)-
    inner ℂ (powerIsometry m x.2) (powerIsometry m y.2))=_
  rw [power_isometry_inner,power_isometry_inner]
  rfl

/-- The complete signed energy still converges to the SAME canonical h1. -/
theorem odd_source_complex_limit :
    Tendsto (fun (k : ℕ) => physicalForm (physicalJet k 1) (physicalJet k 1)) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) := by
  have hd : Tendsto (fun k : ℕ => (k,k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  have h := (common_odd_jets 0 0).comp hd
  simpa only [Function.comp_def,commonJetPairing,form_same_power] using h

theorem odd_source_limit :
    Tendsto (fun (k : ℕ) => (physicalForm (physicalJet k 1) (physicalJet k 1)).re) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 1)) := by
  simpa only [Function.comp_def,Complex.ofReal_re] using
    Complex.continuous_re.continuousAt.tendsto.comp odd_source_complex_limit

theorem inverse_radial_mass_limit : Tendsto (fun (k : ℕ) => ((k : ℝ)+1)⁻¹) atTop (nhds 0) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp canonicalGreenJetStep_tendsto_zero
  simpa [Function.comp_def,canonicalGreenJetStep,← Complex.ofReal_natCast,
    ← Complex.ofReal_one,← Complex.ofReal_add,← Complex.ofReal_inv] using h

theorem odd_source_scaled_limit :
    Tendsto (fun (k : ℕ) => (physicalForm (physicalJet k 1) (physicalJet k 1)).re/((k : ℝ)+1)^2)
      atTop (nhds 0) := by
  have h := odd_source_limit.mul (inverse_radial_mass_limit.pow 2)
  simpa [div_eq_mul_inv,inv_pow] using h

/-- A negative bulk of the SAME quadratic growth cancels both mixed crosses. -/
theorem odd_bulk_scaled_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) :
    Tendsto (fun (k : ℕ) => (physicalForm (oddBulk η k) (oddBulk η k)).re/((k : ℝ)+1)^2)
      atTop (nhds (-2*(canonicalCompletedNativeLogDerivativeMoment 0*oddCoefficient η))) := by
  have h := odd_source_scaled_limit.sub ((odd_mixed_scaled_limit η hη0 hη1).const_mul 2)
  simp only [zero_sub,← neg_mul] at h
  apply h.congr'
  filter_upwards [node_regular_eventually] with k hk
  have he := odd_energy_three_sectors η hη0 hη1 k hk
  rw [he]
  ring

end
end CarryFirstOddGreen
