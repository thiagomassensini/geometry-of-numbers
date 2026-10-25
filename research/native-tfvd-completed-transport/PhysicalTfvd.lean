import ShiftTransport

namespace CarryNativeTfvd
open CarrySelfAdjointOperator CarryVerticalSynthesis
open CPFormal.Analytic.Cp (NativeGpreTowerHilbert)
open GeometryOfNumbers.Analysis.RealCarry
open scoped BigOperators InnerProductSpace lp ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem solve_linear_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B M : E →L[ℂ] E) (z : ℂ) (f g boundary : E)
    (hInv : A (B f) = f) (hComm : ∀ v, A (M v) = M (A v))
    (hn : B f = z • M g + boundary) :
    f = z • M (A g) + A boundary := by
  calc
    f = A (B f) := hInv.symm
    _ = A (z • M g + boundary) := congrArg A hn
    _ = _ := by rw [map_add, map_smul, hComm]

/-- The exact original TFVD is transported as a vector identity on the entire
native real tower; its two trace coordinates are not discarded. -/
theorem synthesized_tfvd (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (X : NativeGpreTowerHilbert) :
    nativeSynthesis X =
      nativeSynthesis (carryVerticalL2WeightedGreen eta
        (carryWeightedVerticalCenteredBracket eta X)) +
      nativeSynthesis (carryWeightedVerticalReturn eta h0.le h1
        (carryWeightedVerticalTrace eta X)) := by
  have h := congrArg (fun T : NativeGpreTowerHilbert →L[ℝ] NativeGpreTowerHilbert => T X)
    (carryWeightedVerticalTfvd_identity eta h0 h1)
  change carryVerticalL2WeightedGreen eta (carryWeightedVerticalCenteredBracket eta X) +
    carryWeightedVerticalReturn eta h0.le h1 (carryWeightedVerticalTrace eta X) = X at h
  simpa only [map_add] using (congrArg nativeSynthesis h).symm

theorem physical_numerator_two_traces (eta : ℝ) (heta : eta ≠ 0)
    (X : NativeGpreTowerHilbert) :
    ((1 - (eta : ℂ) • NativeLaguerre.physicalRadialAdvance)^2 :
      CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier)
      (nativeSynthesis X) =
      eta • NativeLaguerre.physicalRadialAdvance
        (nativeSynthesis (carryWeightedVerticalCenteredBracket eta X)) +
      (X 0) • completedNativeChiralCauchyFeature 0 +
      (X 1 - 2 * eta * X 0) • completedNativeChiralCauchyFeature 1 := by
  have h := congrArg nativeSynthesis (vertical_numerator_two_traces eta heta X)
  simp only [map_add, map_sub, map_smul, native_synthesis_shift,
    native_synthesis_column] at h
  calc
    _ = nativeSynthesis X - (2 * eta) •
        NativeLaguerre.physicalRadialAdvance (nativeSynthesis X) +
        eta ^ 2 • NativeLaguerre.physicalRadialAdvance
          (NativeLaguerre.physicalRadialAdvance (nativeSynthesis X)) := by
      simp only [pow_two, mul_apply_eq_comp, sub_apply, one_apply_eq_self,
        smul_apply, map_sub, map_smul, smul_sub, smul_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal]
      push_cast
      module
    _ = _ := h

theorem physical_resolvent_commutes_advance (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta < 1) :
    Commute (NativeLaguerre.physicalGreenResolvent eta h0 h1)
      NativeLaguerre.physicalRadialAdvance := by
  unfold Commute SemiconjBy
  rw [NativeLaguerre.physicalGreenResolvent, NativeLaguerre.physicalRadialAdvance,
    ← NativeLaguerre.intervalMultiplier_mul, ← NativeLaguerre.intervalMultiplier_mul,
    mul_comm]

/-- Solve the original physical valve while retaining the whole boundary vector. -/
theorem physical_resolvent_solve (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta < 1)
    (f g boundary : CanonicalCompletedNativeChiralCauchyCarrier)
    (hn : ((1 - (eta : ℂ) • NativeLaguerre.physicalRadialAdvance)^2 :
      CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ]
        CanonicalCompletedNativeChiralCauchyCarrier) f =
        (eta : ℂ) • NativeLaguerre.physicalRadialAdvance g + boundary) :
    f = NativeLaguerre.physicalGreenOperator eta h0 h1 g +
      ((NativeLaguerre.physicalGreenResolvent eta h0 h1)^2) boundary := by
  let R : CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ]
      CanonicalCompletedNativeChiralCauchyCarrier := NativeLaguerre.physicalGreenResolvent eta h0 h1
  let M : CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ]
      CanonicalCompletedNativeChiralCauchyCarrier := NativeLaguerre.physicalRadialAdvance
  have hr := NativeLaguerre.physicalGreenResolvent_reconstruct eta h0 h1 f
  have hc := (physical_resolvent_commutes_advance eta h0 h1).pow_left 2
  have hpoint (v : CanonicalCompletedNativeChiralCauchyCarrier) :
      (R^2) (M v) = M ((R^2) v) :=
    congrArg (fun T : CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ]
      CanonicalCompletedNativeChiralCauchyCarrier => T v) hc.eq
  have hs := solve_linear_step (R^2) ((1 - (eta : ℂ) • M)^2) M (eta : ℂ)
    f g boundary hr hpoint hn
  exact hs

/-- A physical Green reconstruction with the original bounded resolvent, on
every native tower input, not just a separate finite polynomial model. -/
theorem physical_tfvd_reconstruction (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (X : NativeGpreTowerHilbert) :
    nativeSynthesis X =
      NativeLaguerre.physicalGreenOperator eta h0.le h1
        (nativeSynthesis (carryWeightedVerticalCenteredBracket eta X)) +
      ((NativeLaguerre.physicalGreenResolvent eta h0.le h1)^2)
        ((X 0) • completedNativeChiralCauchyFeature 0 +
          (X 1 - 2 * eta * X 0) • completedNativeChiralCauchyFeature 1) := by
  apply physical_resolvent_solve eta h0.le h1
  have h := physical_numerator_two_traces eta h0.ne' X
  simpa only [add_assoc, RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_eq_complex_ofReal] using h

/-- The transported TFVD return is completely specified by the same two
boundary data. It is not declared equal to the completed chiral reflection. -/
theorem physical_boundary_return (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a b : ℝ) :
    nativeSynthesis (carryWeightedVerticalReturn eta h0.le h1 (a,b)) =
      ((NativeLaguerre.physicalGreenResolvent eta h0.le h1)^2)
        (a • completedNativeChiralCauchyFeature 0 +
          (eta * (b - a)) • completedNativeChiralCauchyFeature 1) := by
  have h := physical_tfvd_reconstruction eta h0 h1
    (carryWeightedVerticalReturn eta h0.le h1 (a,b))
  have hb := congrArg (fun T => T (a,b))
    (carryWeightedVerticalCenteredBracket_comp_return eta h0 h1)
  change carryWeightedVerticalCenteredBracket eta
    (carryWeightedVerticalReturn eta h0.le h1 (a,b)) = 0 at hb
  rw [hb, map_zero, map_zero, zero_add] at h
  have he : eta * (a + b) - 2 * eta * a = eta * (b - a) := by ring
  simpa only [carryWeightedVerticalReturn_apply, pow_zero, zero_mul, add_zero,
    one_mul, pow_one, Nat.cast_one, Nat.cast_zero, he] using h

/-- The Green intertwining holds on the ACTUAL bracket range, including all
infinite tails; it is obtained by comparing complete reconstructions. -/
theorem physical_green_on_bracket (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (X : NativeGpreTowerHilbert) :
    nativeSynthesis (carryVerticalL2WeightedGreen eta
      (carryWeightedVerticalCenteredBracket eta X)) =
      NativeLaguerre.physicalGreenOperator eta h0.le h1
        (nativeSynthesis (carryWeightedVerticalCenteredBracket eta X)) := by
  have hs := synthesized_tfvd eta h0 h1 X
  have hp := physical_tfvd_reconstruction eta h0 h1 X
  rw [carryWeightedVerticalTrace_apply,
    physical_boundary_return eta h0 h1] at hs
  have he : eta * (eta⁻¹ * X 1 - X 0 - X 0) = X 1 - 2 * eta * X 0 := by
    field_simp [h0.ne']
    ring
  rw [he] at hs
  exact add_right_cancel (hs.symm.trans hp)

end
end CarryNativeTfvd
