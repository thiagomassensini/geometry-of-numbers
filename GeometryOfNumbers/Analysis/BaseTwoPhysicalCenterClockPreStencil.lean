import GeometryOfNumbers.Analysis.BaseTwoPhysicalCenterClockGreenParseval

/-! # Pre-stencil localization of the concrete center-clock defect
A nonzero odd coordinate at material 3 survives both the residual and direct
Green sectors. The seed coordinate itself remains zero. No stencil is changed.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GreenFrame.Concrete C2GlobalGreenBridge C2GreenPreStencilCanary

def baseTwoPhysicalCenterClockDefectPreStencil (t : ℝ) : PreStencilSpace :=
  preStencilLinearIsometry canonicalCarryInfinitePartition
    (baseTwoPhysicalCenterClockDefectGreenState t)

theorem baseTwoPhysicalCenterClockDefectPreStencil_components (t : ℝ) :
    (baseTwoPhysicalCenterClockDefectPreStencil t).fst =
      seedResidualAnalysis canonicalCarryInfinitePartition
        (baseTwoPhysicalCenterClockDefectGreenState t) ∧
    (baseTwoPhysicalCenterClockDefectPreStencil t).snd =
      directGreenAnalysis canonicalCarryInfinitePartition
        (baseTwoPhysicalCenterClockDefectGreenState t) := ⟨rfl,rfl⟩

theorem baseTwoPhysicalCenterClockDefectGreenState_seed_zero (t : ℝ) :
    baseTwoPhysicalCenterClockDefectGreenState t (1 : PNat) = 0 := by
  apply baseTwoPhysicalC2GreenIsometry_off_sector
  norm_num

theorem baseTwoPhysicalCenterClockDefectGreenState_three_ne_zero (t : ℝ) :
    baseTwoPhysicalCenterClockDefectGreenState t (3 : PNat) ≠ 0 := by
  have h := baseTwoPhysicalCenterClockDefectGreenState_apply t (0,0)
  change baseTwoPhysicalCenterClockDefectGreenState t (3 : PNat) =
    baseTwoPhysicalCenterClockDefect t (0,0) at h
  rw [h, baseTwoPhysicalCenterClockDefect_left]
  have hc : baseTwoCenter 0 = 4 := by simp [baseTwo_center_eq]
  rw [hc]
  norm_num only [Nat.reduceSub]
  apply mul_ne_zero
  · rw [← Complex.ofReal_sub]
    apply Complex.ofReal_ne_zero.mpr
    exact ne_of_gt (sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num)))
  · intro hz
    have hn := criticalMaterialSample_norm_sq t 4 (by decide)
    rw [hz, norm_zero] at hn
    norm_num at hn

theorem baseTwoPhysicalCenterClockDefectGreenState_ne_zero (t : ℝ) :
    baseTwoPhysicalCenterClockDefectGreenState t ≠ 0 := by
  intro h
  have hz := congrArg (fun f : State => f (3 : PNat)) h
  exact baseTwoPhysicalCenterClockDefectGreenState_three_ne_zero t hz

/-- The literal seed is zero, but the residual half of this sector is not. -/
theorem baseTwoPhysicalCenterClockDefect_seedResidual_ne_zero (t : ℝ) :
    seedResidualAnalysis canonicalCarryInfinitePartition
      (baseTwoPhysicalCenterClockDefectGreenState t) ≠ 0 := by
  intro hz
  have hb := (seedResidualAnalysis_norm_sq_bounds canonicalCarryInfinitePartition
    (baseTwoPhysicalCenterClockDefectGreenState t)).1
  rw [hz, norm_zero] at hb
  have hp : 0 < ‖baseTwoPhysicalCenterClockDefectGreenState t‖ :=
    norm_pos_iff.mpr (baseTwoPhysicalCenterClockDefectGreenState_ne_zero t)
  nlinarith

private theorem baseThree_eventNumber : eventNumber (1,1) = (3 : PNat) := by
  apply PNat.eq
  norm_num [eventNumber, basePNat, baseNat]

private theorem baseThree_greenAmplitude_pos :
    0 < greenAmplitude canonicalCarryInfinitePartition (1,1) := by
  apply Real.sqrt_pos.mpr
  rw [greenEventMass, baseThree_eventNumber, canonicalCarryInfinitePartition_weight]
  change 0 < carryCameraWeight 3 3 / (3 : ℝ)
  apply div_pos _ (by norm_num)
  rw [carryCameraWeight, if_pos (by decide : 1 < 3 ∧ 2 ≤ 3 ∧ 3 ≤ 3)]
  apply div_pos _ (allBaseNormalizer_pos (by decide))
  apply mul_pos (Nat.cast_pos.mpr
    ((positionalDepth_pos_iff_dvd (by decide) (by decide)).mpr (by decide)))
    (Real.log_pos (by norm_num))

/-- Camera code 1 is physical base 3, reaching the nonzero odd endpoint 3. -/
theorem baseTwoPhysicalCenterClockDefect_directGreen_ne_zero (t : ℝ) :
    directGreenAnalysis canonicalCarryInfinitePartition
      (baseTwoPhysicalCenterClockDefectGreenState t) ≠ 0 := by
  intro hz
  have h := congrArg (fun f : ℓ²(GreenEvent,ℂ) => f (1,1)) hz
  change directGreenCoordinate canonicalCarryInfinitePartition (1,1)
    (baseTwoPhysicalCenterClockDefectGreenState t) = 0 at h
  rw [directGreenCoordinate, baseThree_eventNumber] at h
  exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt baseThree_greenAmplitude_pos))
    (baseTwoPhysicalCenterClockDefectGreenState_three_ne_zero t)) h

/-- Both pre-stencil sectors are genuinely occupied at every real time. -/
theorem baseTwoPhysicalCenterClockDefectPreStencil_both_sectors (t : ℝ) :
    (baseTwoPhysicalCenterClockDefectPreStencil t).fst ≠ 0 ∧
    (baseTwoPhysicalCenterClockDefectPreStencil t).snd ≠ 0 := by
  rw [(baseTwoPhysicalCenterClockDefectPreStencil_components t).1,
    (baseTwoPhysicalCenterClockDefectPreStencil_components t).2]
  exact ⟨baseTwoPhysicalCenterClockDefect_seedResidual_ne_zero t,
    baseTwoPhysicalCenterClockDefect_directGreen_ne_zero t⟩

end GeometryOfNumbers.Analysis.BaseTwoCompletion
