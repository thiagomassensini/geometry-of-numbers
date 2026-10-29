import ExplicitSourceTail
import SixEnergyTransport

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator CarryMovingRadial CarryMaterialVariation CarryBoundaryReconstruction
open NativeLaguerre CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem native_response_norm_bound (z : ℂ) (hz : ‖z‖ < 1/4)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    ‖completedNativeOperatorLogDerivative z‖ ≤ 1/4 := by
  have ht := native_response_prefix_error z hz hF 0
  simp only [Finset.range_zero,Finset.sum_empty,mul_zero,sub_zero,pow_zero,mul_one] at ht
  have hden : 0 < 1-(22/175:ℝ)*‖z‖^2 := by nlinarith [norm_nonneg z]
  apply ht.trans
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  nlinarith [norm_nonneg z]

theorem native_positive_coordinate_ne_zero (z : ℂ) (hz : ‖z‖ < 1/4)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativePositiveHermiteBiehlerCoordinate z ≠ 0 := by
  have hb := native_response_norm_bound z hz hF
  have hq : completedNativeOperatorLogDerivative z+Complex.I ≠ 0 := by
    intro he
    have hh : completedNativeOperatorLogDerivative z = -Complex.I := eq_neg_of_add_eq_zero_left he
    rw [hh] at hb
    norm_num at hb
  have he : completedNativePositiveHermiteBiehlerCoordinate z=
      completedNativeOperatorCharacteristic z*(completedNativeOperatorLogDerivative z+Complex.I) := by
    unfold completedNativePositiveHermiteBiehlerCoordinate completedNativeOperatorLogDerivative
    field_simp [hF]
  rw [he]
  exact mul_ne_zero hF hq

theorem imaginary_radial_regular (y : ℝ) (hy : |y| < 1/4) :
    completedNativeOperatorCharacteristic (Complex.I*(y:ℂ)) ≠ 0 ∧
    completedNativePositiveHermiteBiehlerCoordinate (Complex.I*(y:ℂ)) ≠ 0 := by
  have hF := imaginary_characteristic_ne_zero y hy
  refine ⟨hF,native_positive_coordinate_ne_zero _ ?_ hF⟩
  simpa [norm_mul] using hy

theorem six_radial_regular (h : ℝ) (hh : |h| < 1/24) (j : Fin 6) :
    completedNativeOperatorCharacteristic (point h j) ≠ 0 ∧
    completedNativePositiveHermiteBiehlerCoordinate (point h j) ≠ 0 := by
  have he : point h j=Complex.I*((((j:ℝ)+1)*h:ℝ):ℂ) := by unfold point; push_cast; ring
  have hp : |((j:ℝ)+1)*h| < 1/4 := by
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(j:ℝ)+1)]
    have hj : (j:ℝ)+1≤6 := by exact_mod_cast (show (j:ℕ)+1≤6 by omega)
    have hb := mul_le_mul_of_nonneg_right hj (abs_nonneg h)
    linarith
  rw [he]
  exact imaginary_radial_regular _ hp

/-- Full source identity at EVERY native step below the explicit cutoff,
with original amplitude and both legs, instead of an unspecified eventual set. -/
theorem six_physical_at_explicit_step (k : ℕ) (hk : radialFourSourceStep k < 1/24) :
    sixPhysical k=(sixEnergy sixU sixV (canonicalGreenJetStep k)).re := by
  have hreg (j : Fin 6) := six_radial_regular (radialFourSourceStep k)
    (by rwa [abs_of_pos (radial_step_positive k)]) j
  have he := physical_response_pair 6 k (sixRaw sixU sixV (canonicalGreenJetStep k))
    (sixRaw sixU sixV (canonicalGreenJetStep k))
    (fun j => by rw [← point_at_grid]; exact (hreg j).1)
    (fun j => by rw [← point_at_grid]; exact (hreg j).2)
  rw [six_curve_eq_original] at he
  have hc := six_response_energy sixU sixV (radialFourSourceStep k) (radial_step_positive k).ne'
  rw [← canonicalGreenJetStep_eq_radialFourSourceStep k] at hc
  rw [hc] at he
  have hn := CarryTailReturn.signed_diagonal_norm
    (physicalCompletedFiniteSource k (sixInput sixU sixV k))
  have hr := congrArg Complex.re he
  norm_num [Complex.mul_re] at hr
  exact hn.symm.trans hr

end
end CarryEffectiveRadial
