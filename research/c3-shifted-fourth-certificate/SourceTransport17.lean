import GammaCrosswalk17

namespace C3ShiftedFourth

open CarryC3Boxes CarryC3Tail CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets C3CofactorCorrelation
open Set Filter Topology
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

def finiteCompletedRealJetCrosswalk80 (r : Fin 17) : ℝ :=
  convolution leftRealJet80 (fun j => (gammaReferenceCrosswalk17 j : ℝ)) r.val

def finiteCompletedReferenceJetCrosswalk80 (r : Fin 17) : ℂ :=
  ∑ j ∈ Finset.range (r.val+1),
    sourceJet j leftHead80 *
      (Complex.I^(r.val-j) * (gammaReferenceCrosswalk17 (r.val-j):ℂ))

theorem finite_completed_reference_jet_phase_crosswalk80 (r : Fin 17) :
    finiteCompletedReferenceJetCrosswalk80 r =
      Complex.I^r.val * (finiteCompletedRealJetCrosswalk80 r:ℂ) := by
  unfold finiteCompletedReferenceJetCrosswalk80 finiteCompletedRealJetCrosswalk80
    convolution
  simp_rw [left_head80_jet_phase]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r.val := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show Complex.I^r.val = Complex.I^j * Complex.I^(r.val-j) by
    rw [← pow_add, Nat.add_sub_of_le hjr]]
  ring

theorem completed_head80_gamma_replacement_error_crosswalk (r : Fin 17) :
    ‖sourceJet r.val (completedHead48 80) -
      finiteCompletedReferenceJetCrosswalk80 r‖ ≤
      ∑ j ∈ Finset.range (r.val+1),
        |leftRealJet80 j| *
          (2*4^(r.val-j)/10^34+(2/10^29:ℝ)) := by
  have hl : AnalyticAt ℂ leftHead80 0 :=
    (elementary_multiplier_analytic_at 0 (by norm_num)).mul
      (accelerated_c3_head48_analytic 80)
  have hg : AnalyticAt ℂ nativeGamma 0 :=
    native_gamma_analytic 0 (by norm_num)
  change ‖sourceJet r.val (fun w => leftHead80 w * nativeGamma w) -
      finiteCompletedReferenceJetCrosswalk80 r‖ ≤ _
  rw [jet_mul hl hg, finiteCompletedReferenceJetCrosswalk80,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub, norm_mul, left_head80_jet_phase]
  have hgamma := native_gamma_crosswalk_boxes ⟨r.val-j, by omega⟩
  have hphase : ‖Complex.I^j * (leftRealJet80 j:ℂ)‖ = |leftRealJet80 j| := by
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hphase]
  exact mul_le_mul_of_nonneg_left hgamma (abs_nonneg _)

theorem completed_native_jet_crosswalk_error80 (r : Fin 17) :
    ‖sourceJet r.val completedNativeOperatorCharacteristic -
      Complex.I^r.val * (finiteCompletedRealJetCrosswalk80 r:ℂ)‖ ≤
        (∑ j ∈ Finset.range (r.val+1),
          |leftRealJet80 j| *
            (2*4^(r.val-j)/10^34+(2/10^29:ℝ))) + 2/10^27 := by
  have hhead : AnalyticAt ℂ (completedHead48 80) 0 := by
    change AnalyticAt ℂ (fun w => leftHead80 w*nativeGamma w) 0
    exact ((elementary_multiplier_analytic_at 0 (by norm_num)).mul
      (accelerated_c3_head48_analytic 80)).mul
        (native_gamma_analytic 0 (by norm_num))
  have htail : AnalyticAt ℂ (completedTailError48 80) 0 := by
    exact (value_multiplier_analytic_at 0 (by norm_num)).mul
      (accelerated_c3_tail48_analytic 80 0 (by norm_num))
  have he : completedNativeOperatorCharacteristic =ᶠ[nhds (0:ℂ)]
      (fun w => completedHead48 80 w + completedTailError48 80 w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (by simp : (0:ℂ)∈Metric.ball 0 (1:ℝ))] with w hw
    exact completed_native_head_tail48 80 w (by simpa using hw)
  have hj : sourceJet r.val completedNativeOperatorCharacteristic =
      sourceJet r.val (completedHead48 80) +
        sourceJet r.val (completedTailError48 80) := by
    unfold sourceJet
    rw [he.iteratedDeriv_eq]
    exact sourceJet_add _ _ _ hhead htail
  rw [hj, ← finite_completed_reference_jet_phase_crosswalk80 r]
  have hrw : sourceJet r.val (completedHead48 80) +
      sourceJet r.val (completedTailError48 80) -
        finiteCompletedReferenceJetCrosswalk80 r =
      (sourceJet r.val (completedHead48 80) -
        finiteCompletedReferenceJetCrosswalk80 r) +
          sourceJet r.val (completedTailError48 80) := by ring
  rw [hrw]
  calc
    _ ≤ ‖sourceJet r.val (completedHead48 80) -
          finiteCompletedReferenceJetCrosswalk80 r‖ +
        ‖sourceJet r.val (completedTailError48 80)‖ := norm_add_le _ _
    _ ≤ (∑ j ∈ Finset.range (r.val+1),
          |leftRealJet80 j| *
            (2*4^(r.val-j)/10^34+(2/10^29:ℝ))) + 2/10^27 :=
      add_le_add (completed_head80_gamma_replacement_error_crosswalk r)
        (completed_tail80_jet_error_through_sixteen r)

def normalizedLeftJet80 : ℕ → ℝ :=
  convolution (normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3))
    head80RealJet

theorem left_real_jet80_eq_normalized (r : ℕ) :
    leftRealJet80 r =
      C3CofactorCorrelation.leftJet48Scale * normalizedLeftJet80 r := by
  have hp : polynomialRealJet = fun j => (-1/8:ℝ)*normalizedPolynomialJet j :=
    funext polynomialRealJet_eq_normalized
  have hx : exponentialRealJet = fun j =>
      Real.exp (-Real.log Real.pi/4)*normalizedExponentialJet
        (Real.log Real.pi) j := funext exponentialRealJet_eq_normalized
  have hc : reciprocalJet chartRealJet = fun j =>
      chartScale⁻¹ * normalizedChartReciprocal chartRatio (Real.log 3) j :=
    funext reciprocalJet_chart_eq_normalized
  have hinner : convolution polynomialRealJet exponentialRealJet =
      fun j => ((-1/8:ℝ)*Real.exp (-Real.log Real.pi/4)) *
        convolution normalizedPolynomialJet
          (normalizedExponentialJet (Real.log Real.pi)) j := by
    funext j
    rw [hp, hx]
    exact convolution_scale_both normalizedPolynomialJet
      (normalizedExponentialJet (Real.log Real.pi)) (-1/8:ℝ)
      (Real.exp (-Real.log Real.pi/4)) j
  have hbase : convolution (convolution polynomialRealJet exponentialRealJet)
      (reciprocalJet chartRealJet) = fun j =>
        C3CofactorCorrelation.leftJet48Scale *
          normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3) j := by
    funext j
    rw [hinner, hc]
    exact convolution_scale_both
      (fun k => convolution normalizedPolynomialJet
        (normalizedExponentialJet (Real.log Real.pi)) k)
      (normalizedChartReciprocal chartRatio (Real.log 3))
      ((-1/8:ℝ)*Real.exp (-Real.log Real.pi/4)) chartScale⁻¹ j
  unfold leftRealJet80 normalizedLeftJet80
  rw [hbase]
  exact convolution_scale_left
    (normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3))
    head80RealJet C3CofactorCorrelation.leftJet48Scale r

def realJetSeries (a : ℕ → ℝ) : PowerSeries ℝ := PowerSeries.mk a

theorem convolution_eq_realJetSeries_coeff (a b : ℕ → ℝ) (n : ℕ) :
    convolution a b n = PowerSeries.coeff n (realJetSeries a * realJetSeries b) := by
  unfold convolution realJetSeries
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j) n,
    PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]

theorem realJetSeries_convolution (a b : ℕ → ℝ) :
    realJetSeries (convolution a b) = realJetSeries a * realJetSeries b := by
  ext n
  simpa [realJetSeries] using convolution_eq_realJetSeries_coeff a b n

theorem convolution_cross_through_sixteen (r : Fin 17)
    (a b c : ℕ → ℝ) :
    convolution (convolution a b) c r.val =
      convolution b (convolution a c) r.val := by
  calc
    convolution (convolution a b) c r.val =
        PowerSeries.coeff r.val (realJetSeries (convolution a b) * realJetSeries c) :=
      convolution_eq_realJetSeries_coeff (convolution a b) c r.val
    _ = PowerSeries.coeff r.val ((realJetSeries a * realJetSeries b) * realJetSeries c) := by
      rw [realJetSeries_convolution]
    _ = PowerSeries.coeff r.val (realJetSeries b * (realJetSeries a * realJetSeries c)) := by
      congr 1
      calc
        (realJetSeries a * realJetSeries b) * realJetSeries c =
            realJetSeries a * (realJetSeries b * realJetSeries c) := mul_assoc _ _ _
        _ = realJetSeries b * (realJetSeries a * realJetSeries c) := by
          rw [mul_left_comm]
    _ = convolution b (convolution a c) r.val := by
      rw [← realJetSeries_convolution a c]
      exact (convolution_eq_realJetSeries_coeff b (convolution a c) r.val).symm

theorem gamma_crosswalk_eq_scaled_normalized17 (r : ℕ) :
    (gammaReferenceCrosswalk17 r:ℝ) =
      (gammaRealReference13 ⟨0, by omega⟩:ℝ) * normalizedGammaJetCrosswalk17 r := by
  by_cases hl : r < 13
  · have h := C3CofactorCorrelation.gammaReferenceJet_eq_normalized r hl
    simpa [gammaReferenceCrosswalk17, normalizedGammaJetCrosswalk17,
      C3CofactorCorrelation.gammaReferenceJet, C3CofactorCorrelation.gammaReferenceScale,
      hl] using h
  · by_cases hh : r < 17
    · have h0 : (gammaRealReference13 ⟨0, by omega⟩:ℝ) ≠ 0 := by
        norm_num [gammaRealReference13]
      simp [gammaReferenceCrosswalk17, normalizedGammaJetCrosswalk17, hl, hh]
      exact (mul_div_cancel₀ _ h0).symm
    · simp [gammaReferenceCrosswalk17, normalizedGammaJetCrosswalk17, hl, hh]

theorem finite_completed_crosswalk_eq_normalized80 (r : Fin 17) :
    finiteCompletedRealJetCrosswalk80 r =
      C3CofactorCorrelation.leftJet48Scale *
        (gammaRealReference13 ⟨0, by omega⟩:ℝ) *
          normalizedCompletedReferenceJet80 r.val := by
  have hleft : leftRealJet80 = fun j =>
      C3CofactorCorrelation.leftJet48Scale * normalizedLeftJet80 j :=
    funext left_real_jet80_eq_normalized
  have hgamma : (fun j => (gammaReferenceCrosswalk17 j : ℝ)) = fun j =>
      (gammaRealReference13 ⟨0, by omega⟩:ℝ) * normalizedGammaJetCrosswalk17 j :=
    funext gamma_crosswalk_eq_scaled_normalized17
  unfold finiteCompletedRealJetCrosswalk80 normalizedCompletedReferenceJet80
  rw [hleft, hgamma, convolution_scale_both]
  rw [normalizedLeftJet80]
  rw [convolution_cross_through_sixteen r]
  rfl

end
end C3ShiftedFourth
