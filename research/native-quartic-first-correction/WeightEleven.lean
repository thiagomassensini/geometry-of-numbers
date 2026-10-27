import QuarticKernel
import Taylor11

namespace CarryQuarticCorrection
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCurvatureGreen
open CarryQuarticTaylor NativeLaguerre
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The ORIGINAL 4!-normalized source and Cauchy metric force this value. -/
theorem full_quartic_weight11_complex (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    sectorKernel false eta h0 h1 (monomialWeight 11) fourthShape fourthShape=(55/2 : ℂ) := by
  have hs : fourthShape=five (1/24) (-(1/6)) (1/4) (-(1/6)) (1/24) := fourth_shape_explicit
  simp only [hs,full_five_pairing]
  norm_num [monomialWeight,map_div₀,map_neg,map_ofNat]

theorem full_quartic_weight11_real (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (sectorKernel false eta h0 h1 (monomialWeight 11) fourthShape fourthShape).re=55/2 := by
  rw [full_quartic_weight11_complex]
  norm_num

/-- Complex identity BEFORE any diagonal real readout; no condition on R. -/
theorem zero_remainder_kernel (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (a b : ℝ) :
    sectorKernel false eta h0 h1 (remainderWeight11 R 0)
      (quarticProfile a b 0) (quarticProfile a b 0)=(55/2 : ℂ)*R 0 := by
  have hw : remainderWeight11 R 0=(fun j => R 0*monomialWeight 11 j) := by
    funext j
    simp only [remainderWeight11,monomialWeight,Complex.ofReal_zero,mul_zero]
    ring
  simp only [quarticProfile,zero_pow (by decide : 2≠0),zero_pow (by decide : 4≠0),
    mul_zero,Complex.ofReal_zero,zero_smul,sub_zero]
  rw [hw,kernel_scale_weight,full_quartic_weight11_complex]
  ring

end
end CarryQuarticCorrection
