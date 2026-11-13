import M80SourceTransport
import CompletedBoxes48
import GammaSeventeen

namespace C3ShiftedFourth
open CarryC3Tail CarryC3Boxes CarryC3Gamma CarrySelfAdjointOperator
  PhysicalSewing CarryTwoEvenJets
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- The completed left multiplier jets obtained from the original M=80
bracket head, the original completion factors, and the original C3/48 boarder. -/
def leftRealJet80 : ℕ → ℝ := convolution
  (convolution (convolution polynomialRealJet exponentialRealJet)
    (reciprocalJet chartRealJet)) head80RealJet

def leftJetBox80 : ℕ → Box := convolutionBox
  (convolutionBox (convolutionBox polynomialJetBox exponentialJetBox)
    (reciprocalJetBox chartJetBoxTight))
  (fun n => tightHead80JetBox n)

theorem left_jet_box80 (n : ℕ) :
    (leftJetBox80 n).Contains (leftRealJet80 n) := by
  exact (convolution_box _ _ _ _
    (convolution_box _ _ _ _
      (convolution_box _ _ _ _ polynomial_jet_box exponential_jet_box)
      (reciprocal_jet_box chartJetBoxTight chartRealJet chart_jet_box_tight
        (Or.inr chart_center_interval_negative_tight)))
    (fun j => tight_head80_jet_box j)) n

def leftHead80 (w : ℂ) : ℂ :=
  c3ElementaryMultiplier w * acceleratedC3Head48 80 w

theorem left_head80_jet_phase (r : ℕ) :
    sourceJet r leftHead80 = Complex.I^r * (leftRealJet80 r : ℂ) := by
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
  have hformula : leftHead80 = (fun w =>
      ((nativePolynomial w * nativeExponential w) * (nativeChart w)⁻¹) *
        acceleratedC3Head48 80 w) := by
    funext w
    rfl
  rw [hformula]
  change sourceJet r
      (fun w => ((nativePolynomial w * nativeExponential w) * (nativeChart w)⁻¹) *
        acceleratedC3Head48 80 w) =
      Complex.I^r *
        ((convolution (convolution (convolution polynomialRealJet exponentialRealJet)
          (reciprocalJet chartRealJet)) head80RealJet r : ℝ) : ℂ)
  exact phased_product ((hp.mul he).mul (hc.inv hcn))
    (accelerated_c3_head48_analytic 80)
    (convolution (convolution polynomialRealJet exponentialRealJet)
      (reciprocalJet chartRealJet))
    head80RealJet
    (phased_product (hp.mul he) (hc.inv hcn)
      (convolution polynomialRealJet exponentialRealJet)
      (reciprocalJet chartRealJet)
      (phased_product hp he polynomialRealJet exponentialRealJet
        polynomial_jet_formula exponential_jet_formula)
      (phased_reciprocal hc hcn chartRealJet chart_jet_formula))
    accelerated_head80_jet_formula r

def finiteCompletedRealJet80 (r : Fin 17) : ℝ :=
  ∑ j ∈ Finset.range (r.val+1),
    leftRealJet80 j * (gammaRealReference17 ⟨r.val-j, by omega⟩ : ℝ)

def finiteCompletedReferenceJet80 (r : Fin 17) : ℂ :=
  ∑ j ∈ Finset.range (r.val+1),
    sourceJet j leftHead80 *
      (Complex.I^(r.val-j) * (gammaRealReference17 ⟨r.val-j, by omega⟩ : ℂ))

theorem finite_completed_reference_jet_phase80 (r : Fin 17) :
    finiteCompletedReferenceJet80 r =
      Complex.I^r.val * (finiteCompletedRealJet80 r : ℂ) := by
  unfold finiteCompletedReferenceJet80 finiteCompletedRealJet80
  simp_rw [left_head80_jet_phase]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r.val := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show Complex.I^r.val = Complex.I^j * Complex.I^(r.val-j) by
    rw [← pow_add, Nat.add_sub_of_le hjr]]
  ring

theorem completed_head80_gamma_replacement_error (r : Fin 17) :
    ‖sourceJet r.val (completedHead48 80) - finiteCompletedReferenceJet80 r‖ ≤
      ∑ j ∈ Finset.range (r.val+1),
        |leftRealJet80 j| *
          (2*4^(r.val-j)/10^34+(1/10^29:ℝ)) := by
  have hl : AnalyticAt ℂ leftHead80 0 :=
    (elementary_multiplier_analytic_at 0 (by norm_num)).mul
      (accelerated_c3_head48_analytic 80)
  have hg : AnalyticAt ℂ nativeGamma 0 :=
    native_gamma_analytic 0 (by norm_num)
  change ‖sourceJet r.val (fun w => leftHead80 w * nativeGamma w) -
      finiteCompletedReferenceJet80 r‖ ≤ _
  rw [jet_mul hl hg, finiteCompletedReferenceJet80, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub, norm_mul, left_head80_jet_phase]
  have hgbox := native_gamma_seventeen_boxes ⟨r.val-j, by omega⟩
  have hphase : ‖Complex.I^j * (leftRealJet80 j:ℂ)‖ = |leftRealJet80 j| := by
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hphase]
  exact mul_le_mul_of_nonneg_left hgbox (abs_nonneg _)

theorem completed_tail80_jet_error_through_sixteen (r : Fin 17) :
    ‖sourceJet r.val (completedTailError48 80)‖ ≤ (2/10^27:ℝ) := by
  have h := completed_tail48_jet_bound 80 (by norm_num) r.val
  have hp : (4:ℝ)^r.val ≤ 4^16 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ (96*(Nat.factorial 26:ℝ)/(729^2*(3*(80:ℝ)-1)^25))*4^r.val := h
    _ ≤ (96*(Nat.factorial 26:ℝ)/(729^2*(3*(80:ℝ)-1)^25))*4^16 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 2/10^27 := by norm_num

theorem completed_native_jet_reference_error80 (r : Fin 17) :
    ‖sourceJet r.val completedNativeOperatorCharacteristic -
      Complex.I^r.val*(finiteCompletedRealJet80 r:ℂ)‖ ≤
        (∑ j ∈ Finset.range (r.val+1),
          (|leftRealJet80 j|)*
            (2*4^(r.val-j)/10^34+(1/10^29:ℝ))) + 2/10^27 := by
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
  rw [hj, ← finite_completed_reference_jet_phase80 r]
  have hrw : sourceJet r.val (completedHead48 80) +
      sourceJet r.val (completedTailError48 80) - finiteCompletedReferenceJet80 r =
      (sourceJet r.val (completedHead48 80) - finiteCompletedReferenceJet80 r) +
        sourceJet r.val (completedTailError48 80) := by ring
  rw [hrw]
  calc
    _ ≤ ‖sourceJet r.val (completedHead48 80) - finiteCompletedReferenceJet80 r‖ +
        ‖sourceJet r.val (completedTailError48 80)‖ := norm_add_le _ _
    _ ≤ (∑ j ∈ Finset.range (r.val+1),
          (|leftRealJet80 j|)*
            (2*4^(r.val-j)/10^34+(1/10^29:ℝ))) + 2/10^27 :=
      add_le_add (completed_head80_gamma_replacement_error r)
        (completed_tail80_jet_error_through_sixteen r)

#print axioms left_jet_box80
#print axioms accelerated_head80_jet_formula
#print axioms left_head80_jet_phase
#print axioms finite_completed_reference_jet_phase80
#print axioms completed_head80_gamma_replacement_error
#print axioms completed_native_jet_reference_error80

end
end C3ShiftedFourth
