import RestrictedAdvance
import Mathlib.Analysis.SpecificLimits.Normed

namespace CarryRadialGreen
open CarryPhysicalTrace CarryRadialRefinement CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Only the resolvent denominator of an integer power of the old M_x. -/
def greenDenominator (r : ℕ) (η : ℝ) : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace :=
  1-(η : ℂ) • nativeAdvance^r

/-- Its actual Banach-algebra inverse. The valid domain is proved below. -/
def greenResolvent (r : ℕ) (η : ℝ) : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace :=
  Ring.inverse (greenDenominator r η)

theorem green_denominator_isUnit (r : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    IsUnit (greenDenominator r η) := by
  unfold greenDenominator
  apply isUnit_one_sub_of_norm_lt_one (R := PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace)
    (x := (η : ℂ) • nativeAdvance^r)
  have hp : ‖nativeAdvance^r‖ ≤ 1 :=
    (norm_pow_le nativeAdvance r).trans (pow_le_one₀ (norm_nonneg nativeAdvance) native_advance_norm_le_one)
  have he : ‖(η : ℂ) • nativeAdvance^r‖ ≤ η := by
    have hb := ContinuousLinearMap.opNorm_smul_le (η : ℂ) (nativeAdvance^r)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hη0] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hp hη0).trans_eq (mul_one η))
  exact he.trans_lt hη1

theorem green_left_inverse (r : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    greenResolvent r η*greenDenominator r η=1 :=
  Ring.inverse_mul_cancel _ (green_denominator_isUnit r η hη0 hη1)

theorem green_right_inverse (r : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    greenDenominator r η*greenResolvent r η=1 :=
  Ring.mul_inverse_cancel _ (green_denominator_isUnit r η hη0 hη1)

theorem green_resolvent_denominator (r : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (x : PhysicalCauchySpace) : greenResolvent r η (greenDenominator r η x)=x := by
  simpa only [mul_apply_eq_comp,one_apply_eq_self] using
    congrArg (fun T : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace => T x) (green_left_inverse r η hη0 hη1)

theorem green_denominator_resolvent (r : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (x : PhysicalCauchySpace) : greenDenominator r η (greenResolvent r η x)=x := by
  simpa only [mul_apply_eq_comp,one_apply_eq_self] using
    congrArg (fun T : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace => T x) (green_right_inverse r η hη0 hη1)

theorem power_green_denominator (m : ℕ) (η : ℝ) (x : PhysicalCauchySpace) :
    powerIsometry m (greenDenominator 1 η x) =
      greenDenominator (m+1) η (powerIsometry m x) := by
  simp only [greenDenominator,sub_apply,one_apply_eq_self,
    smul_apply,pow_one,map_sub,map_smul,power_advance]

/-- The resolvent covariance is an operator identity on the original closure,
not merely a diagonal norm relation or a statement about a chosen readout. -/
theorem power_green_resolvent (m : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (x : PhysicalCauchySpace) : powerIsometry m (greenResolvent 1 η x) =
      greenResolvent (m+1) η (powerIsometry m x) := by
  calc
    _ = greenResolvent (m+1) η (greenDenominator (m+1) η
        (powerIsometry m (greenResolvent 1 η x))) :=
      (green_resolvent_denominator (m+1) η hη0 hη1 _).symm
    _ = greenResolvent (m+1) η (powerIsometry m (greenDenominator 1 η (greenResolvent 1 η x))) := by
      rw [power_green_denominator]
    _ = _ := by rw [green_denominator_resolvent 1 η hη0 hη1]

theorem power_green_resolvent_squared (m : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (x : PhysicalCauchySpace) : powerIsometry m (((greenResolvent 1 η)^2) x) =
      ((greenResolvent (m+1) η)^2) (powerIsometry m x) := by
  simp only [pow_two,mul_apply_eq_comp,power_green_resolvent m η hη0 hη1]

theorem native_advance_pow_coe (r : ℕ) (x : PhysicalCauchySpace) :
    ((nativeAdvance^r) x : CanonicalCompletedNativeChiralCauchyCarrier) =
      (physicalRadialAdvance^r) (x : CanonicalCompletedNativeChiralCauchyCarrier) := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ,mul_apply_eq_comp,ih,pow_succ,mul_apply_eq_comp,native_advance_coe]

theorem green_denominator_coe (r : ℕ) (η : ℝ) (x : PhysicalCauchySpace) :
    (greenDenominator r η x : CanonicalCompletedNativeChiralCauchyCarrier) =
      (1-(η : ℂ) • physicalRadialAdvance^r) (x : CanonicalCompletedNativeChiralCauchyCarrier) := by
  simp only [greenDenominator,sub_apply,one_apply_eq_self,
    smul_apply,Submodule.coe_sub,Submodule.coe_smul,native_advance_pow_coe]

/-- Identification with the OLD physical Green resolvent, so the inverse is
not a replacement operator introduced for the target positivity. -/
theorem green_resolvent_one_original (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (x : PhysicalCauchySpace) :
    (greenResolvent 1 η x : CanonicalCompletedNativeChiralCauchyCarrier) =
      physicalGreenResolvent η hη0 hη1 (x : CanonicalCompletedNativeChiralCauchyCarrier) := by
  have he := congrArg (fun y : PhysicalCauchySpace => (y : CanonicalCompletedNativeChiralCauchyCarrier))
    (green_denominator_resolvent 1 η hη0 hη1 x)
  rw [green_denominator_coe,pow_one] at he
  calc
    _ = physicalGreenResolvent η hη0 hη1
        ((1-(η : ℂ) • physicalRadialAdvance) (greenResolvent 1 η x : CanonicalCompletedNativeChiralCauchyCarrier)) := by
      symm
      simpa only [mul_apply_eq_comp,one_apply_eq_self] using
        congrArg (fun T : CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ]
          CanonicalCompletedNativeChiralCauchyCarrier => T (greenResolvent 1 η x))
          (physicalGreenResolvent_left_inverse η hη0 hη1)
    _ = _ := by rw [he]

end
end CarryRadialGreen
