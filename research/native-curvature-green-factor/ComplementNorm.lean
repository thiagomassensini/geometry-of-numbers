import CarrySelfAdjointOperator.NativePhysicalGreenResolvent

namespace CarryCurvatureGreen
open CarrySelfAdjointOperator NativeLaguerre
open scoped unitInterval InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

abbrev PhysicalSpace := CanonicalCompletedNativeChiralCauchyCarrier
abbrev physicalComplement : PhysicalSpace →L[ℂ] PhysicalSpace := 1-physicalRadialAdvance

/-- The ORIGINAL valve is a contraction on the whole physical L2 space. -/
theorem physical_valve_norm_le_one (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖(1-(q : ℂ) • physicalRadialAdvance : PhysicalSpace →L[ℂ] PhysicalSpace)‖ ≤ 1 := by
  rw [physicalRadialAdvance,← intervalMultiplier_smul,← intervalMultiplier_one,← intervalMultiplier_sub]
  apply (intervalMultiplier_norm_le _).trans
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ)≤1)).mpr
  intro u
  have hqu : 0 ≤ q*(u : ℝ) := mul_nonneg hq0 u.property.1
  have hqu1 : q*(u : ℝ) ≤ 1 :=
    (mul_le_of_le_one_right hq0 u.property.2).trans hq1
  simp only [ContinuousMap.sub_apply,ContinuousMap.one_apply,ContinuousMap.smul_apply,
    physicalRadialCoefficient,ContinuousMap.coe_mk,smul_eq_mul,← Complex.ofReal_mul,
    ← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith : 0≤1-q*(u : ℝ))]
  linarith

theorem physical_complement_norm_le_one : ‖physicalComplement‖ ≤ 1 := by
  simpa using physical_valve_norm_le_one 1 (by norm_num) (by norm_num)

theorem physical_complement_contracts (f : PhysicalSpace) : ‖physicalComplement f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖physicalComplement‖*‖f‖ := physicalComplement.le_opNorm f
    _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right physical_complement_norm_le_one (norm_nonneg _)
    _ = _ := one_mul _

theorem physical_complement_selfAdjoint : IsSelfAdjoint physicalComplement :=
  physicalRadialAdvance_complement_isPositive.isSelfAdjoint

/-- An expanding inverse is deduced from the physical valve, not postulated. -/
theorem resolvent_norm_lower (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta < 1) (f : PhysicalSpace) :
    ‖f‖ ≤ ‖physicalGreenResolvent eta h0 h1 f‖ := by
  let D : PhysicalSpace →L[ℂ] PhysicalSpace := 1-(eta : ℂ) • physicalRadialAdvance
  let R := physicalGreenResolvent eta h0 h1
  have hi := congrArg (fun T : PhysicalSpace →L[ℂ] PhysicalSpace => T f)
    (physicalGreenResolvent_right_inverse eta h0 h1)
  change D (R f)=f at hi
  calc
    ‖f‖ = ‖D (R f)‖ := congrArg norm hi.symm
    _ ≤ ‖D‖*‖R f‖ := D.le_opNorm _
    _ ≤ 1*‖R f‖ := mul_le_mul_of_nonneg_right
      (physical_valve_norm_le_one eta h0 h1.le) (norm_nonneg _)
    _ = _ := one_mul _

end
end CarryCurvatureGreen
