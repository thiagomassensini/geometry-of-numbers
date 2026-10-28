import FiniteNormBudget
import Mathlib.Tactic

namespace CarryRadialExtrapolation
open CarrySelfAdjointOperator CarryEffectiveRadial CarryMaterialVariation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Exact two-resolution cancellation, independent of any sign. -/
theorem quadratic_cancellation (h L C E F : ℂ) :
    (4*(L+C*(h/2)^2+(h/2)^4*F)-(L+C*h^2+h^4*E))/3-L =
      (h^4/3)*(F/4-E) := by ring

/-- A uniform bound for the complete remainders gives a fourth-order error. -/
theorem extrapolation_error (h L C E F : ℂ) (M : ℝ)
    (hE : ‖E‖ ≤ M) (hF : ‖F‖ ≤ M) :
    ‖(4*(L+C*(h/2)^2+(h/2)^4*F)-(L+C*h^2+h^4*E))/3-L‖ ≤
      (5/12:ℝ)*M*‖h‖^4 := by
  rw [quadratic_cancellation,norm_mul,norm_div,norm_pow,Complex.norm_ofNat]
  have hb : ‖F/4-E‖ ≤ (5/4:ℝ)*M := by
    calc
      _ ≤ ‖F/4‖+‖E‖ := norm_sub_le _ _
      _ ≤ (5/4:ℝ)*M := by
        rw [norm_div,Complex.norm_ofNat]
        linarith
  have hp : 0 ≤ ‖h‖^4 := by positivity
  have ht := mul_le_mul_of_nonneg_left hb hp
  nlinarith

/-- The native radial step at 2k+1 is exactly half of its kth step. -/
theorem radial_step_half (k : ℕ) :
    (1/(((2*k+1:ℕ):ℝ)+1)) = (1/((k:ℝ)+1))/2 := by
  push_cast
  field_simp
  ring


/-- Apply the exact cancellation to the six-address native source, using
its already-proved analytic remainder, with no assumption on its sign. -/
theorem six_source_extrapolation (u v : ℝ) (z : ℂ) (M : ℝ)
    (hz : ‖z‖ < 1/24) (hn : z ≠ 0)
    (hF : ∀ j : Fin 6, completedNativeOperatorCharacteristic (Complex.I*((j:ℂ)+1)*z) ≠ 0)
    (hFhalf : ∀ j : Fin 6, completedNativeOperatorCharacteristic (Complex.I*((j:ℂ)+1)*(z/2)) ≠ 0)
    (hE : ‖sixEffectiveRemainder u v z‖ ≤ M)
    (hEhalf : ‖sixEffectiveRemainder u v (z/2)‖ ≤ M) :
    ‖(4*sixEnergy u v (z/2)-sixEnergy u v z)/3-(sixLimit u v:ℂ)‖ ≤
      (5/12:ℝ)*M*‖z‖^4 := by
  have hzhalf : ‖z/2‖ < 1/24 := by
    rw [norm_div,Complex.norm_ofNat]
    linarith [norm_nonneg z]
  have he := six_expansion_on_disc u v z hz hn hF
  have hh := six_expansion_on_disc u v (z/2) hzhalf (div_ne_zero hn (by norm_num)) hFhalf
  rw [he,hh]
  exact extrapolation_error z (sixLimit u v:ℂ) (sixCorrection u v:ℂ)
    (sixEffectiveRemainder u v z) (sixEffectiveRemainder u v (z/2)) M hE hEhalf


/-- The earlier six-source explicit remainder budget supplies M = 10^20
at both resolutions, without any sign assumption. -/
theorem six_source_extrapolation_effective (u v : ℝ) (z : ℂ)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hz : ‖z‖ < 1/24) (hn : z ≠ 0)
    (hF : ∀ j : Fin 6, completedNativeOperatorCharacteristic (Complex.I*((j:ℂ)+1)*z) ≠ 0)
    (hFhalf : ∀ j : Fin 6, completedNativeOperatorCharacteristic (Complex.I*((j:ℂ)+1)*(z/2)) ≠ 0) :
    ‖(4*sixEnergy u v (z/2)-sixEnergy u v z)/3-(sixLimit u v:ℂ)‖ ≤
      (5/12:ℝ)*(10:ℝ)^20*‖z‖^4 := by
  apply six_source_extrapolation u v z ((10:ℝ)^20) hz hn hF hFhalf
  · apply six_effective_remainder_bound u v z hu hv
    linarith
  · apply six_effective_remainder_bound u v (z/2) hu hv
    rw [norm_div,Complex.norm_ofNat]
    linarith [norm_nonneg z]


/-- The half-step relation is for the existing physical radial grid. -/
theorem original_radial_step_half (k : ℕ) :
    radialFourSourceStep (2*k+1)=radialFourSourceStep k/2 := by
  simpa only [radialFourSourceStep,one_div] using radial_step_half k

end
end CarryRadialExtrapolation
