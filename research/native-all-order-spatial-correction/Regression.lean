import NativeSpatialLaw
import FourthBoundaryDefect

namespace CarrySpatialCorrection
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarryCurvatureGreen
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The old quadratic-family seed includes an explicit MINUS sign. -/
theorem native_profile_zero : nativeEvenProfile 0= -seedInput := by
  simp [nativeEvenProfile, staticStencil, rawStencil, seedInput, triple,
    completedGreenForwardWeight]

/-- The original three-address second-difference source. -/
theorem native_profile_one : nativeEvenProfile 1=curvatureInput := by
  ext j
  simp only [nativeEvenProfile, staticStencil, Finsupp.smul_apply, smul_eq_mul,
    raw_stencil_apply]
  rcases j with _ | _ | _ | j
  all_goals try { norm_num [completedGreenForwardWeight, curvatureInput, triple] }
  simp [completedGreenForwardWeight, curvatureInput, triple,
    Nat.choose_eq_zero_of_lt (show 2 < j+3 by omega)]

/-- The original five-address fourth-difference source. -/
theorem native_profile_two : nativeEvenProfile 2=fourthShape := by
  rw [fourth_shape_explicit]
  ext j
  simp only [nativeEvenProfile, staticStencil, Finsupp.smul_apply, smul_eq_mul,
    raw_stencil_apply]
  rcases j with _ | _ | _ | _ | _ | j
  all_goals try { norm_num [completedGreenForwardWeight, Nat.choose, Nat.factorial] }
  simp [completedGreenForwardWeight,
    Nat.choose_eq_zero_of_lt (show 4 < j+5 by omega)]

/-- Original imaginary step: the even phase cannot be silently deleted. -/
theorem radial_even_calibration (k r : ℕ) :
    radialJetCoefficients k (2*r)=((k:ℂ)+1)^(2*r) • nativeEvenProfile r := by
  have hi : Complex.I^(2*r)=(-1:ℂ)^r := by rw [pow_mul, Complex.I_sq]
  have hf : ((2*r).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (2*r)
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (show k+1≠0 by omega)
  have hs : ((-1:ℂ)^r)^2=1 := by rw [← pow_mul, Nat.mul_comm r 2, pow_mul]; norm_num
  have he :
      (((2*r).factorial:ℂ)*(Complex.I*((k:ℂ)+1)⁻¹)^(2*r))⁻¹=
      ((k:ℂ)+1)^(2*r)*((-1:ℂ)^r*((2*r).factorial:ℂ)⁻¹) := by
    rw [mul_pow, hi, inv_pow]
    field_simp
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hs.symm
  simp only [radialJetCoefficients, canonicalCompletedC3RadialSecondStep,
    canonicalGreenJetStep, nativeEvenProfile, staticStencil, smul_smul, he]

/-- Exact recovery of the old 55/2 from the universal two-input law. -/
theorem quartic_weight11_regression (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    sectorKernel false eta h0 h1 (monomialWeight 11) fourthShape fourthShape=(55/2:ℂ) := by
  have h := native_first_correction eta h0 h1 2 2
  norm_num [native_profile_two, spatialCorrection, curvature, slope] at h
  linear_combination h/2

/-- Independent-index table, including the formerly tested mixed entries. -/
theorem correction_table :
    spatialCorrection 0 0=1 ∧ spatialCorrection 0 2=20 ∧ spatialCorrection 0 4=126 ∧
    spatialCorrection 2 2=14 ∧ spatialCorrection 2 4=75 ∧ spatialCorrection 4 4=55 := by
  norm_num [spatialCorrection, curvature, slope]

/-- Positive entries in this coefficient table do NOT make it a positive form.
This is a coefficient-table obstruction, not a negative canonical pivot. -/
theorem correction_table_negative_direction :
    (20:ℂ)^2*spatialCorrection 0 0+
      2*20*(-1)*spatialCorrection 0 2+(-1)^2*spatialCorrection 2 2= -386 := by
  norm_num [spatialCorrection, curvature, slope]

end
end CarrySpatialCorrection
