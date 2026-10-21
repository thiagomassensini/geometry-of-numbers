import TraceFiber
import CarrySelfAdjointOperator.CompletedC3AllOrderChartResponseCorrection

/-! Apply the exact trace fibers to the SAME cutoff-free completed physical
source. The invisible component is not an arbitrary ambient perturbation:
it is present in the canonical source itself. -/
namespace CarryTraceFiber
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open CanonicalCompletedC3AllCutoffOnePointHilbert
open scoped InnerProductSpace ComplexConjugate
noncomputable section

abbrev nativeState (z : ℂ) (hz : operatorHeightParameter z ∈ genuineCriticalStrip) : Physical :=
  canonicalCompletedC3CompletedOnePointState z hz

theorem native_tail_zero (z : ℂ) (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    tailTrace (nativeState z hz)=0 := by
  simp [tailTrace, nativeState, canonicalCompletedC3CompletedOnePointState, logJetTail, valueTail]

theorem native_contrast_eq_trace (z : ℂ) (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    contrast (nativeState z hz)=projection (nativeState z hz) := by
  rw [contrast, projection_eq_add, native_tail_zero, sub_zero, add_zero]

/-- The actual source has nonvanishing trace-contrast; sending the cutoff to
infinity does not erase this part of the physical trace fiber. -/
theorem native_pairing_exact (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    inner ℝ (nativeState z hz) (nativeState w hw)=
      bulkPairing (nativeState z hz) (nativeState w hw)+
        inner ℝ (projection (nativeState z hz)) (projection (nativeState w hw)) := by
  rw [physical_inner_fiber, native_contrast_eq_trace, native_contrast_eq_trace]
  ring

theorem native_invisible_energy_exact (z : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    ‖invisible (nativeState z hz)‖^2=
      ‖(nativeState z hz).direct‖^2+‖(nativeState z hz).reflected‖^2+
        ‖(nativeState z hz).quarterTurnReflected‖^2+
          (1/2 : ℝ)*‖projection (nativeState z hz)‖^2 := by
  rw [invisible_norm_exact, native_contrast_eq_trace]

theorem native_center_trace_ne_zero :
    projection (nativeState 0 zero_mem_completedNativeHeightDomain) ≠ 0 := by
  intro h
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_completed_eq] at h
  have hv := congrArg (fun t : Trace => t.snd) h
  change canonicalCompletedC3RawHeightValue 0=0 at hv
  rw [canonicalCompletedC3RawHeightValue_eq_chart_mul_normalized
      zero_mem_completedNativeHeightDomain,
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
      zero_mem_completedNativeHeightDomain] at hv
  exact (mul_ne_zero (canonicalC3ChartFactorHeight_ne_zero zero_mem_completedNativeHeightDomain)
    nativeHeightScalar_zero_ne_zero) hv

theorem native_center_invisible_energy_positive :
    0 < ‖invisible (nativeState 0 zero_mem_completedNativeHeightDomain)‖^2 := by
  rw [native_invisible_energy_exact]
  have ht := sq_pos_of_pos (norm_pos_iff.mpr native_center_trace_ne_zero)
  positivity

theorem native_center_invisible_ne_zero :
    invisible (nativeState 0 zero_mem_completedNativeHeightDomain) ≠ 0 := by
  intro h
  have hpos := native_center_invisible_energy_positive
  rw [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hpos
  exact (lt_irrefl 0) hpos

/-- This is an actual source obstruction, stronger than an ambient-kernel example. -/
theorem native_center_not_minimum_energy_lift :
    nativeState 0 zero_mem_completedNativeHeightDomain ≠
      balancedLift (projection (nativeState 0 zero_mem_completedNativeHeightDomain)) := by
  intro h
  apply native_center_invisible_ne_zero
  unfold invisible
  exact sub_eq_zero.mpr h

/-- The missing Gram component has a physical vector limit. No positivity or
canonical Gram hypothesis is involved. -/
theorem native_invisible_tendsto (z : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ => invisible (canonicalCompletedC3AllCutoffOnePointState M z))
      Filter.atTop (nhds (invisible (nativeState z hz))) := by
  have hc : Continuous (fun x : Physical => invisible x) := by
    unfold invisible balancedLift
    fun_prop
  exact hc.continuousAt.tendsto.comp (canonicalCompletedC3AllCutoffOnePointState_tendsto_completed hz)


/-- The ordinary physical norm does not factor through this trace on its
whole ambient carrier. This says nothing about a different restricted
source-derived family or a different, justified physical form. -/
theorem not_physical_norm_factors_through_trace :
    ¬ ∃ q : Trace → ℝ, ∀ x : Physical, ‖x‖^2=q (projection x) := by
  rintro ⟨q,hq⟩
  have hzero := hq 0
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), map_zero] at hzero
  have hhidden := hq (invisible (nativeState 0 zero_mem_completedNativeHeightDomain))
  rw [projection_invisible, ← hzero] at hhidden
  exact (ne_of_gt native_center_invisible_energy_positive) hhidden

/-- Crossings of the invisible components converge as physical pairings,
not merely as scalar boundary observations. -/
theorem native_invisible_pairing_tendsto (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ => inner ℝ
        (invisible (canonicalCompletedC3AllCutoffOnePointState M z))
        (invisible (canonicalCompletedC3AllCutoffOnePointState M w)))
      Filter.atTop (nhds (inner ℝ (invisible (nativeState z hz)) (invisible (nativeState w hw)))) := by
  exact (native_invisible_tendsto z hz).inner (native_invisible_tendsto w hw)


theorem native_center_trace_energy_strict :
    (1/2 : ℝ)*‖projection (nativeState 0 zero_mem_completedNativeHeightDomain)‖^2 <
      ‖nativeState 0 zero_mem_completedNativeHeightDomain‖^2 := by
  rw [physical_norm_visible_invisible]
  linarith [native_center_invisible_energy_positive]

/-- Here M is the physical carrier cutoff, not the radial microscope index
or the vertical carry depth. The retained fiber energy stays separated from
zero along the original, unmodified cutoff states. -/
theorem native_center_invisible_energy_eventually :
    ∀ᶠ M : ℕ in Filter.atTop,
      (1/2 : ℝ)*‖invisible (nativeState 0 zero_mem_completedNativeHeightDomain)‖^2 <
        ‖invisible (canonicalCompletedC3AllCutoffOnePointState M 0)‖^2 := by
  have h := (native_invisible_tendsto 0 zero_mem_completedNativeHeightDomain).norm.pow 2
  apply (tendsto_order.mp h).1
  linarith [native_center_invisible_energy_positive]

end
end CarryTraceFiber
