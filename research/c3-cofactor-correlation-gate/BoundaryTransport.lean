import LeftJetMagnitude

namespace C3CofactorCorrelation

open CarrySelfAdjointOperator CarryC3Tail CarryC3Boxes CarryC3Gamma
open CarryTwoEvenJets C3Cofactor
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

theorem completed_tail48_jet_error_tight (r : Fin 13) :
    ‖sourceJet r.val (completedTailError48 48)‖ ≤ (2/10^24:ℝ) := by
  have h := completed_tail48_jet_bound 48 (by norm_num) r.val
  have hp : (4:ℝ)^r.val ≤ 4^12 := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ (96*(Nat.factorial 26:ℝ)/(729^2*(3*(48:ℝ)-1)^25))*4^r.val := h
    _ ≤ (96*(Nat.factorial 26:ℝ)/(729^2*(3*(48:ℝ)-1)^25))*4^12 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 2/10^24 := by norm_num

theorem completed_native_jet_reference_error48_tight (r : Fin 13) :
    ‖sourceJet r.val completedNativeOperatorCharacteristic -
      Complex.I^r.val * (finiteCompletedRealJet48 r:ℂ)‖ ≤
        (3/10^24:ℝ) := by
  have hhead : AnalyticAt ℂ (completedHead48 48) 0 := by
    change AnalyticAt ℂ (fun w => leftHead48 w*nativeGamma w) 0
    exact ((elementary_multiplier_analytic_at 0 (by norm_num)).mul
      (accelerated_c3_head48_analytic 48)).mul
        (native_gamma_analytic 0 (by norm_num))
  have htail : AnalyticAt ℂ (completedTailError48 48) 0 := by
    exact (value_multiplier_analytic_at 0 (by norm_num)).mul
      (accelerated_c3_tail48_analytic 48 0 (by norm_num))
  have he : completedNativeOperatorCharacteristic =ᶠ[nhds (0:ℂ)]
      (fun w => completedHead48 48 w + completedTailError48 48 w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (by simp : (0:ℂ)∈Metric.ball 0 (1:ℝ))] with w hw
    exact completed_native_head_tail48 48 w (by simpa using hw)
  have hj : sourceJet r.val completedNativeOperatorCharacteristic =
      sourceJet r.val (completedHead48 48) + sourceJet r.val (completedTailError48 48) := by
    unfold sourceJet
    rw [he.iteratedDeriv_eq]
    exact sourceJet_add _ _ _ hhead htail
  rw [hj, ← finite_completed_reference_jet_phase48 r]
  have hrw : sourceJet r.val (completedHead48 48) +
      sourceJet r.val (completedTailError48 48) - finiteCompletedReferenceJet48 r =
      (sourceJet r.val (completedHead48 48) - finiteCompletedReferenceJet48 r) +
        sourceJet r.val (completedTailError48 48) := by ring
  rw [hrw]
  calc
    _ ≤ ‖sourceJet r.val (completedHead48 48) - finiteCompletedReferenceJet48 r‖ +
        ‖sourceJet r.val (completedTailError48 48)‖ := norm_add_le _ _
    _ ≤ (∑ j ∈ Finset.range (r.val+1),
          (|leftRealJet48 j|)*(1/10^24:ℝ)) + 2/10^24 :=
      add_le_add (completed_characteristic_reference_jet_error48 r)
        (completed_tail48_jet_error_tight r)
    _ ≤ (3/10^24:ℝ) := by
      have hg := left_gamma_replacement_allowance_le_half r
      linarith

theorem native_even_coefficient_finite_reference_error (j : Fin 7) :
    |nativeC j.val - (-1:ℝ)^j.val *
      finiteCompletedRealJet48 ⟨2*j.val, by omega⟩| ≤ (3/10^24:ℝ) := by
  have hjet := completed_native_jet_reference_error48_tight
    (⟨2*j.val, by omega⟩ : Fin 13)
  have hphase : Complex.I^(2*j.val) = ((-1:ℝ)^j.val : ℂ) := by
    calc
      Complex.I^(2*j.val) = (Complex.I^2)^j.val := by rw [pow_mul]
      _ = ((-1:ℝ)^j.val : ℂ) := by simp [Complex.I_sq]
  have hcomplex :
      ‖((nativeC j.val - (-1:ℝ)^j.val *
          finiteCompletedRealJet48 ⟨2*j.val, by omega⟩ : ℝ) : ℂ)‖ ≤
        (3/10^24:ℝ) := by
    simpa [nativeC_eq_sourceJet, hphase] using hjet
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hcomplex

end
end C3CofactorCorrelation
