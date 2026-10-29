import NormalizedJets

/-! The denominator and dressing below are the ORIGINAL completed ones.
Only an observation of the companion numerator is truncated. These are
approximations with explicit errors, never replacement native moments. -/
namespace CarryCellTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialParts CarrySelfAdjointOperator
open CarryMaterialMixedSchurComparison CarryMaterialThirdNullComparison
open Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def ordinaryHead (M : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range M, baseTwoCriticalCenterCell t k
def clockHead (M : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range M, clockCell k t
def ordinaryTail (M : ℕ) (t : ℝ) : ℂ := baseTwoCompletedBoundaryValue t-ordinaryHead M t
def clockTail (M : ℕ) (t : ℝ) : ℂ := carryValveKappa t-clockHead M t

theorem cell_real_analytic (k : ℕ) : AnalyticAt ℝ (fun t => baseTwoCriticalCenterCell t k) 0 := by
  have hC : AnalyticAt ℂ (complexCell k) (0:ℂ) := (complex_cell_entire k).analyticAt 0
  have h := AnalyticAt.comp_of_eq (g:=complexCell k) (f:=fun t : ℝ => (t:ℂ))
    (x:=(0:ℝ)) (hC.restrictScalars (𝕜:=ℝ)) (Complex.ofRealCLM.analyticAt (0:ℝ)) rfl
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, complex_cell_real] using h

theorem clock_cell_real_analytic (k : ℕ) : AnalyticAt ℝ (clockCell k) 0 :=
  ((cellJetCoordinate k).restrictScalars ℝ |>.analyticAt _).comp (material_clock_l1_analytic 0)

theorem beta_real_analytic : AnalyticAt ℝ baseTwoCompletedBoundaryValue 0 := by
  have he : baseTwoCompletedBoundaryValue = (cellReturnReadout.restrictScalars ℝ) ∘
      baseTwoCompletedMaterialGradient := funext (fun t => (cellReturnReadout_source t).symm)
  rw [he]
  exact ((cellReturnReadout.restrictScalars ℝ).analyticAt _).comp (material_l1_analytic 0)

theorem kappa_real_analytic : AnalyticAt ℝ carryValveKappa 0 := by
  have he : carryValveKappa = (cellReturnReadout.restrictScalars ℝ) ∘
      baseTwoCompletedMaterialClockL1 := funext (fun t => (cellReturnReadout_clock_source t).symm)
  rw [he]
  exact ((cellReturnReadout.restrictScalars ℝ).analyticAt _).comp (material_clock_l1_analytic 0)

theorem ordinary_head_analytic (M : ℕ) : AnalyticAt ℝ (ordinaryHead M) 0 :=
  (Finset.range M).analyticAt_fun_sum (fun k _ => cell_real_analytic k)
theorem clock_head_analytic (M : ℕ) : AnalyticAt ℝ (clockHead M) 0 :=
  (Finset.range M).analyticAt_fun_sum (fun k _ => clock_cell_real_analytic k)
theorem ordinary_tail_analytic (M : ℕ) : AnalyticAt ℝ (ordinaryTail M) 0 :=
  beta_real_analytic.sub (ordinary_head_analytic M)
theorem clock_tail_analytic (M : ℕ) : AnalyticAt ℝ (clockTail M) 0 :=
  kappa_real_analytic.sub (clock_head_analytic M)

def ordinaryBudget (m M : ℕ) : ℝ := 2^(m+1)/(4*(4*(M:ℝ)-1))
def clockBudget (m M : ℕ) : ℝ := ((m+1:ℕ):ℝ)*2^(m+2)/(4*(4*(M:ℝ)-1))

theorem ordinary_tail_jet_bound (m M : ℕ) (hM : 0 < M) :
    ‖rJet m (ordinaryTail M)‖ ≤ ordinaryBudget m M := by
  unfold ordinaryTail
  rw [rJet_sub beta_real_analytic (ordinary_head_analytic M)]
  unfold ordinaryHead
  rw [rJet_sum _ _ (fun k _ => cell_real_analytic k)]
  simp_rw [rJet, ← cell_jet_source]
  exact return_jet_quantitative m M hM

theorem clock_tail_jet_bound (m M : ℕ) (hM : 0 < M) :
    ‖rJet m (clockTail M)‖ ≤ clockBudget m M := by
  unfold clockTail
  rw [rJet_sub kappa_real_analytic (clock_head_analytic M)]
  unfold clockHead
  rw [rJet_sum _ _ (fun k _ => clock_cell_real_analytic k)]
  have hc (k : ℕ) : rJet m (clockCell k) = clockCellJet m k := by
    change carryScalarJetShift m ((cellJetCoordinate k).restrictScalars ℝ ∘ baseTwoCompletedMaterialClockL1) 0 = _
    rw [map_l1_jets _ (material_clock_l1_analytic 0)]
    rfl
  simp_rw [hc]
  exact clock_return_jet_quantitative m M hM

theorem original_response_center_ne : baseTwoCanonicalResponse 0 ≠ 0 := by
  rw [baseTwoCanonicalResponse_eq_dressing_mul_signal]
  exact mul_ne_zero (baseTwoCanonicalDressingScalar_ne_zero 0) carryMaterial_origin_signal_ne_zero

/-- Literal scalar coefficients of the two original return channels. -/
def ordinaryMultiplier (t : ℝ) : ℂ :=
  -deriv baseTwoCanonicalDressingScalar t/(2*baseTwoCanonicalResponse t)
def clockMultiplier (t : ℝ) : ℂ :=
  Complex.I*baseTwoCanonicalDressingScalar t/(2*baseTwoCanonicalResponse t)

theorem ordinary_multiplier_analytic : AnalyticAt ℝ ordinaryMultiplier 0 :=
  ((baseTwoCanonicalDressingScalar_analyticAt 0).deriv.neg).div
    (analyticAt_const.mul (baseTwoCanonicalResponse_analyticAt 0))
    (mul_ne_zero (by norm_num) original_response_center_ne)
theorem clock_multiplier_analytic : AnalyticAt ℝ clockMultiplier 0 :=
  (analyticAt_const.mul (baseTwoCanonicalDressingScalar_analyticAt 0)).div
    (analyticAt_const.mul (baseTwoCanonicalResponse_analyticAt 0))
    (mul_ne_zero (by norm_num) original_response_center_ne)

/-- Frozen ORIGINAL denominator; no finite-source log derivative is defined. -/
def responseObservation (M : ℕ) (t : ℝ) : ℂ :=
  ordinaryMultiplier t*(1+ordinaryHead M t)+clockMultiplier t*clockHead M t

theorem response_observation_analytic (M : ℕ) : AnalyticAt ℝ (responseObservation M) 0 :=
  (ordinary_multiplier_analytic.mul (analyticAt_const.add (ordinary_head_analytic M))).add
    (clock_multiplier_analytic.mul (clock_head_analytic M))

theorem normalized_response_channels (t : ℝ) :
    carryMaterialNormalizedResponse t = ordinaryMultiplier t*(1+baseTwoCompletedBoundaryValue t)+
      clockMultiplier t*carryValveKappa t := by
  rw [carryMaterialNormalizedResponse, carryMaterialResponseReadout,
    carryMaterialDressedCompanion_readout, carryMaterial_dressed_completed_readout,
    baseTwoCompletedBoundaryHilbertReadout_apply, carryMaterial_source_seed]
  change (Complex.I*baseTwoCanonicalDressingScalar t*carryValveKappa t-
    deriv baseTwoCanonicalDressingScalar t*(1+baseTwoCompletedBoundaryValue t))/
      (2*baseTwoCanonicalResponse t) = _
  simp only [ordinaryMultiplier, clockMultiplier]
  ring

/-- Both channels, the same completion, and its derivative survive exactly. -/
theorem response_tail_exact (M : ℕ) :
    (fun t => carryMaterialNormalizedResponse t-responseObservation M t) =
      fun t => ordinaryMultiplier t*ordinaryTail M t+clockMultiplier t*clockTail M t := by
  funext t
  rw [normalized_response_channels]
  simp only [responseObservation, ordinaryTail, clockTail]
  ring

def responseBudget (r M : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (r+1), ‖rJet j ordinaryMultiplier‖*ordinaryBudget (r-j) M)+
    ∑ j ∈ Finset.range (r+1), ‖rJet j clockMultiplier‖*clockBudget (r-j) M

theorem response_jet_error (r M : ℕ) (hM : 0 < M) :
    ‖rJet r carryMaterialNormalizedResponse-rJet r (responseObservation M)‖ ≤ responseBudget r M := by
  rw [← rJet_sub material_response_real_analytic (response_observation_analytic M),
    response_tail_exact]
  rw [rJet_add (f:=fun t => ordinaryMultiplier t*ordinaryTail M t)
    (g:=fun t => clockMultiplier t*clockTail M t)
    (ordinary_multiplier_analytic.mul (ordinary_tail_analytic M))
      (clock_multiplier_analytic.mul (clock_tail_analytic M))]
  exact (norm_add_le _ _).trans (add_le_add
    (rJet_mul_bound ordinary_multiplier_analytic (ordinary_tail_analytic M) _
      (fun j => ordinary_tail_jet_bound j M hM) r)
    (rJet_mul_bound clock_multiplier_analytic (clock_tail_analytic M) _
      (fun j => clock_tail_jet_bound j M hM) r))

def observedMoment (M n : ℕ) : ℝ := (rJet (2*n+1) (responseObservation M)).re

theorem native_moment_jet (n : ℕ) : rJet (2*n+1) carryMaterialNormalizedResponse =
    (canonicalCompletedNativeLogDerivativeMoment n:ℂ) := by
  change carryMaterialTaylorShift (2*n+1) 0 = _
  rw [material_taylor_shift_center, completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]

theorem native_moment_error (M : ℕ) (hM : 0 < M) (n : ℕ) :
    |canonicalCompletedNativeLogDerivativeMoment n-observedMoment M n| ≤ responseBudget (2*n+1) M := by
  have h := response_jet_error (2*n+1) M hM
  rw [native_moment_jet] at h
  exact (Complex.abs_re_le_norm _).trans h
end
end CarryCellTail
