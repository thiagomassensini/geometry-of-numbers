import StrongOrbit

namespace CarryNativePhase
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryMixedGreen Filter Topology
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

local notation "b" => (‖carryMaterialClockCentralForcing‖^(2:ℕ):ℝ)

/-- An actual Taylor observation of the original completed Hilbert vector,
not an assumed iterate of an unbounded operator. -/
def materialJetTwo : MaterialCarrier :=
  dslope (dslope baseTwoCompletedBoundaryHilbertState 0) 0 0

def secondCorrection (t : ℝ) : ℂ :=
  (2*Complex.I*carryScalarJetShift 2 sourceOverlap t -
    ((2*b:ℝ):ℂ)*carryScalarJetShift 1 sourceCenter t) / sourceCenter t

def phaseCoefficient : ℂ := secondCorrection 0

theorem source_center_derivative :
    HasDerivAt sourceCenter
      (-Complex.I*carryMaterialClockCentralCoefficient carryMaterialCentralClock) 0 := by
  have h := (carryMaterialClockCentralCoefficient.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (completedBoundaryState_hasDerivAt_clock 0)
  change HasDerivAt sourceCenter
    (carryMaterialClockCentralCoefficient (-Complex.I • carryMaterialCentralClock)) 0 at h
  simpa only [map_smul, smul_eq_mul] using h

theorem scalar_second_expansion (f : ℝ → ℂ) (t : ℝ) (ht : t ≠ 0) :
    f t = f 0 + (t:ℂ)*deriv f 0 + (t:ℂ)^2*carryScalarJetShift 2 f t := by
  change f t = f 0 + (t:ℂ)*deriv f 0 + (t:ℂ)^2*dslope (dslope f 0) 0 t
  rw [dslope_of_ne _ ht, slope_def_module, dslope_of_ne _ ht, slope_def_module]
  simp only [sub_zero, Complex.real_smul, Complex.ofReal_inv, dslope_same]
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast ht
  field_simp
  ring

theorem source_center_expansion (t : ℝ) :
    sourceCenter t = 1+(t:ℂ)*carryScalarJetShift 1 sourceCenter t := by
  have h := sub_smul_dslope sourceCenter 0 t
  simp only [sub_zero, Complex.real_smul, source_center_origin] at h
  change sourceCenter t = 1+(t:ℂ)*dslope sourceCenter 0 t
  linear_combination -h

theorem second_correction_analytic : AnalyticAt ℝ secondCorrection 0 :=
  (((analyticAt_const.mul (carryScalarJetShift_analytic (source_overlap_analytic 0) 2)).sub
    (analyticAt_const.mul (carryScalarJetShift_analytic (source_center_analytic 0) 1))).div
      (source_center_analytic 0) (by rw [source_center_origin]; exact one_ne_zero))

/-- Exact punctured source expansion; the remainder stays as an analytic
function, rather than a numerical truncation of the incident/return norms. -/
theorem native_quadratic_expansion :
    ∀ᶠ t : ℝ in nhdsWithin 0 ({0}ᶜ),
      valueRatio t = ((2*b:ℝ):ℂ)*(t:ℂ) + (t:ℂ)^2*secondCorrection t := by
  have hn := (source_center_analytic 0).continuousAt.eventually_ne
    (show sourceCenter 0 ≠ 0 by rw [source_center_origin]; exact one_ne_zero)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ha ht
  have ht' : t ≠ 0 := by simpa using ht
  rw [value_ratio_undressed t ha]
  change 2*Complex.I*sourceOverlap t/sourceCenter t = _
  have hb := scalar_second_expansion sourceOverlap t ht'
  rw [source_overlap_origin, source_overlap_derivative.deriv, zero_add] at hb
  have he := source_center_expansion t
  unfold secondCorrection
  rw [hb, he]
  have hd : 1+(t:ℂ)*carryScalarJetShift 1 sourceCenter t ≠ 0 := by rw [← he]; exact ha
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem second_coefficient_physical :
    phaseCoefficient = 2*Complex.I*
      (inner ℂ carryMaterialClockCentralForcing (carryMaterialCentralComplement materialJetTwo) +
        ((b:ℝ):ℂ)*carryMaterialClockCentralCoefficient carryMaterialCentralClock) := by
  let probe := ((innerSL ℂ carryMaterialClockCentralForcing).comp carryMaterialCentralComplement).restrictScalars ℝ
  have hy : AnalyticAt ℝ (dslope baseTwoCompletedBoundaryHilbertState 0) 0 := by
    obtain ⟨p,hp⟩ := material_state_analytic 0
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  have he : dslope sourceOverlap 0 = fun t => probe (dslope baseTwoCompletedBoundaryHilbertState 0 t) := by
    funext t
    exact probe.dslope_comp _ 0 t (fun _ => (material_state_analytic 0).differentiableAt)
  have h2 := probe.dslope_comp (dslope baseTwoCompletedBoundaryHilbertState 0) 0 0
    (fun _ => hy.differentiableAt)
  have hs : carryScalarJetShift 2 sourceOverlap 0 =
      inner ℂ carryMaterialClockCentralForcing (carryMaterialCentralComplement materialJetTwo) := by
    change dslope (dslope sourceOverlap 0) 0 0 = _
    rw [he]
    exact h2
  unfold phaseCoefficient secondCorrection
  rw [source_center_origin, div_one, hs]
  have hA : carryScalarJetShift 1 sourceCenter 0 = deriv sourceCenter 0 := dslope_same _ _
  rw [hA, source_center_derivative.deriv]
  push_cast
  ring

theorem phase_coefficient_im_physical :
    phaseCoefficient.im =
      2*(inner ℂ carryMaterialClockCentralForcing (carryMaterialCentralComplement materialJetTwo)).re +
        2*b*(carryMaterialClockCentralCoefficient carryMaterialCentralClock).re := by
  have he (z k : ℂ) (r : ℝ) :
      (2*Complex.I*(z+(r:ℂ)*k)).im = 2*z.re+2*r*k.re := by
    norm_num [Complex.mul_im, Complex.mul_re, Complex.add_re]
    ring
  rw [second_coefficient_physical]
  convert he
    (inner ℂ carryMaterialClockCentralForcing (carryMaterialCentralComplement materialJetTwo))
    (carryMaterialClockCentralCoefficient carryMaterialCentralClock) b using 1

/-- The first potentially non-real coefficient, including its physical
analytic remainder. No assertion that this coefficient is nonzero is made. -/
theorem phase_quadratic_tendsto :
    Tendsto (fun t : ℝ => (valueRatio t-conj (valueRatio t))/(t:ℂ)^2)
      (nhdsWithin 0 ({0}ᶜ)) (nhds (phaseCoefficient-conj phaseCoefficient)) := by
  have h := second_correction_analytic.continuousAt.tendsto
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp h
  have hs := (h.sub hc).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  change Tendsto _ _ (nhds (phaseCoefficient-conj phaseCoefficient)) at hs
  apply hs.congr'
  filter_upwards [native_quadratic_expansion, self_mem_nhdsWithin] with t ht hn
  have hn' : (t:ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by simpa using hn)
  rw [ht]
  simp only [Function.comp_def, map_add, map_mul, map_pow, Complex.conj_ofReal]
  field_simp
  ring

theorem phase_coefficient_is_native_jet : carryScalarJetShift 2 valueRatio 0 = phaseCoefficient := by
  have hs := (carryScalarJetShift_analytic native_ratio_analytic 2).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  have hc := second_correction_analytic.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  apply tendsto_nhds_unique hs
  apply hc.congr'
  filter_upwards [native_quadratic_expansion, self_mem_nhdsWithin] with t ht hn
  have ht' : t ≠ 0 := by simpa using hn
  have he := scalar_second_expansion valueRatio t ht'
  rw [value_ratio_origin, value_ratio_origin_derivative.deriv, zero_add] at he
  have hmul : (t:ℂ)^2*carryScalarJetShift 2 valueRatio t = (t:ℂ)^2*secondCorrection t := by
    linear_combination ht-he
  have htn : (t:ℂ)^2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht')
  exact (mul_left_cancel₀ htn hmul).symm

end
end CarryNativePhase
