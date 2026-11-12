import CompletedBoxes48
import ElementaryJetFormula

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CarryC3Gamma
open CarryC3Boxes CarryC3Tail
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def leftHead48 (w : ℂ) : ℂ := c3ElementaryMultiplier w * acceleratedC3Head48 48 w

theorem left_head48_jet_phase (r : ℕ) :
    sourceJet r leftHead48 = Complex.I^r * (leftRealJet48 r : ℂ) := by
  have hp : AnalyticAt ℂ nativePolynomial 0 := by
    unfold nativePolynomial operatorHeightParameter
    fun_prop
  have he : AnalyticAt ℂ nativeExponential 0 := by
    unfold nativeExponential operatorHeightParameter
    fun_prop
  have hc : AnalyticAt ℂ nativeChart 0 :=
    canonicalC3ChartFactorHeight_analyticAt_zero
  have hcn : nativeChart 0 ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero zero_mem_completedNativeHeightDomain
  have hformula : leftHead48 = (fun w =>
      ((nativePolynomial w * nativeExponential w) * (nativeChart w)⁻¹) *
        acceleratedC3Head48 48 w) := by
    funext w
    rfl
  rw [hformula]
  change sourceJet r
      (fun w => ((nativePolynomial w * nativeExponential w) * (nativeChart w)⁻¹) *
        acceleratedC3Head48 48 w) =
      Complex.I^r *
        ((convolution (convolution (convolution polynomialRealJet exponentialRealJet)
          (reciprocalJet chartRealJet)) head48RealJet r : ℝ) : ℂ)
  exact phased_product ((hp.mul he).mul (hc.inv hcn))
    (accelerated_c3_head48_analytic 48)
    (convolution (convolution polynomialRealJet exponentialRealJet)
      (reciprocalJet chartRealJet)) head48RealJet
    (phased_product (hp.mul he) (hc.inv hcn) _ _
      (phased_product hp he _ _ polynomial_jet_formula exponential_jet_formula)
      (phased_reciprocal hc hcn _ chart_jet_formula))
    accelerated_head48_jet_formula r

def finiteCompletedReferenceJet48 (r : Fin 13) : ℂ :=
  ∑ j ∈ Finset.range (r.val + 1),
    sourceJet j leftHead48 *
      (Complex.I^(r.val-j) * (gammaRealReference13 ⟨r.val-j, by omega⟩ : ℂ))

theorem finite_completed_reference_jet_phase48 (r : Fin 13) :
    finiteCompletedReferenceJet48 r =
      Complex.I^r.val * (finiteCompletedRealJet48 r : ℂ) := by
  unfold finiteCompletedReferenceJet48 finiteCompletedRealJet48
  simp_rw [left_head48_jet_phase]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r.val := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show Complex.I^r.val = Complex.I^j * Complex.I^(r.val-j) by
    rw [← pow_add, Nat.add_sub_of_le hjr]]
  ring

theorem completed_head48_gamma_replacement_error (r : Fin 13) :
    ‖sourceJet r.val (completedHead48 48) - finiteCompletedReferenceJet48 r‖ ≤
      ∑ j ∈ Finset.range (r.val+1),
        |leftRealJet48 j| * (1/10^24:ℝ) := by
  have hl : AnalyticAt ℂ leftHead48 0 :=
    (elementary_multiplier_analytic_at 0 (by norm_num)).mul
      (accelerated_c3_head48_analytic 48)
  have hg : AnalyticAt ℂ nativeGamma 0 := native_gamma_analytic 0 (by norm_num)
  change ‖sourceJet r.val (fun w => leftHead48 w * nativeGamma w) -
      finiteCompletedReferenceJet48 r‖ ≤ _
  rw [jet_mul hl hg, finiteCompletedReferenceJet48, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub, norm_mul, left_head48_jet_phase]
  have hgbox := native_gamma_thirteen_boxes ⟨r.val-j, by omega⟩
  have hphase : ‖Complex.I^j * (leftRealJet48 j:ℂ)‖ = |leftRealJet48 j| := by
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hphase]
  calc
    |leftRealJet48 j| *
        ‖sourceJet (r.val-j) nativeGamma -
          Complex.I^(r.val-j) * (gammaRealReference13 ⟨r.val-j, by omega⟩:ℂ)‖
        ≤ |leftRealJet48 j| * (1/10^24:ℝ) := by
          exact mul_le_mul_of_nonneg_left hgbox (abs_nonneg _)
    _ = |leftRealJet48 j| * (1/10^24:ℝ) := rfl

theorem completed_characteristic_reference_jet_error48 (r : Fin 13) :
    ‖sourceJet r.val (completedHead48 48) - finiteCompletedReferenceJet48 r‖ ≤
      ∑ j ∈ Finset.range (r.val+1), (|leftRealJet48 j|)*(1/10^24:ℝ) :=
  completed_head48_gamma_replacement_error r

theorem completed_native_jet_reference_error48 (r : Fin 13) :
    ‖sourceJet r.val completedNativeOperatorCharacteristic -
      Complex.I^r.val * (finiteCompletedRealJet48 r:ℂ)‖ ≤
        (∑ j ∈ Finset.range (r.val+1), (|leftRealJet48 j|)*(1/10^24:ℝ)) +
          1/10^20 := by
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
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simp : (0:ℂ)∈Metric.ball 0 (1:ℝ))]
      with w hw
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
          (|leftRealJet48 j|)*(1/10^24:ℝ)) + 1/10^20 := by
      exact add_le_add (completed_characteristic_reference_jet_error48 r)
        (completed_tail48_jet_error_through_twelve r)

#print axioms left_head48_jet_phase
#print axioms completed_head48_gamma_replacement_error
#print axioms completed_characteristic_reference_jet_error48
#print axioms completed_native_jet_reference_error48

end
end CarryC3Tail
