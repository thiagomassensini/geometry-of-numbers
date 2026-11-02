import NativeFiniteHeadMargin
import NativeBudgetRate

/-!
# Limiar simbólico da margem finita na fonte C3 original

O limite é explícito em M e na constante de cauda da fonte, cuja existência
é demonstrada, mas cujo valor racional ainda não é certificado. O primeiro
par usa a margem finita independente da PR70; não se afirma lei de sinal geral.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator CarryUniformSource Filter Matrix
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

def evenTwoBudgetUpper (C : ℝ) (M : ℕ) : ℝ :=
  (4*(2:ℝ)^2*(2*sourceCoefficientMass 2*sourceTailRadius C M 2 +
    3*(sourceTailRadius C M 2)^2))*4

theorem literal_head_ne_of_tail_envelope (C : ℝ) (M : ℕ)
    (henv : ‖literalTail M 0‖ ≤ C / ((M:ℝ)+1))
    (hsmall : C / ((M:ℝ)+1) < nativeC 0) : literalHead M 0 ≠ 0 := by
  intro hz
  have hh := congrFun (literal_head_tail M) 0
  simp only [Pi.add_apply] at hh
  rw [hz, zero_add] at hh
  rw [← hh, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos native_source_c0_positive_from_boxes] at henv
  linarith

theorem c3_monic_margin_of_explicit_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      C / ((M:ℝ)+1) < nativeC 0 →
      21 * evenTwoBudgetUpper C M < (1/10^8-1/10^13:ℝ) →
      literalHead M 0 ≠ 0 ∧ ∀ t : ℝ, |t| ≤ 1 →
        20 * literalErrorBudget M M false 2 (twoMonic t) (twoMonic t) <
          (literalTerm M M true true false 2 (twoMonic t) (twoMonic t)).re := by
  obtain ⟨C,hC,henv,hbudget⟩ := literal_full_budget_explicit_order_rate
  refine ⟨C,hC,?_⟩
  intro M hunit hcut
  have htail0 : ‖literalTail M 0‖ ≤ C / ((M:ℝ)+1) := by
    simpa using henv M 0
  have hh : literalHead M 0 ≠ 0 := literal_head_ne_of_tail_envelope C M htail0 hunit
  refine ⟨hh, ?_⟩
  intro t ht
  let z := twoMonic t
  have hmass := twoMonic_coordMass_le t ht
  have hmass0 := coordMass_nonneg z
  have hsq : coordMass z * coordMass z ≤ 4 := by nlinarith
  have hfactor : 0 ≤ (4*(2:ℝ)^2*(2*sourceCoefficientMass 2*sourceTailRadius C M 2 +
      3*(sourceTailRadius C M 2)^2)) := by
    have hA := sourceCoefficientMass_nonneg 2
    have hρ : 0 ≤ sourceTailRadius C M 2 := by unfold sourceTailRadius; positivity
    positivity
  have hbound := hbudget M 2 false z z
  have hupper : literalErrorBudget M M false 2 z z ≤ evenTwoBudgetUpper C M := by
    unfold evenTwoBudgetUpper
    have hb' : literalErrorBudget M M false 2 z z ≤
        (4*(2:ℝ)^2*(2*sourceCoefficientMass 2*sourceTailRadius C M 2 +
          3*(sourceTailRadius C M 2)^2)) * (coordMass z * coordMass z) := by
      simpa only [Nat.cast_ofNat, mul_assoc] using hbound
    exact hb'.trans (mul_le_mul_of_nonneg_left hsq hfactor)
  have hnorm := literal_error_bound M M false 2 z z
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).2
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hlower := c3_original_pair_lower t ht
  change (1/10^8-1/10^13:ℝ) < matrixPair (coefficientBlock (sourceKernel nativeC false) 2) z z at hlower
  nlinarith

theorem evenTwoBudgetUpper_tendsto_zero (C : ℝ) :
    Tendsto (fun M : ℕ => evenTwoBudgetUpper C M) atTop (nhds 0) := by
  have hm : Tendsto (fun M : ℕ => (M:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hi := tendsto_inv_atTop_zero.comp hm
  have hr : Tendsto (fun M : ℕ => sourceTailRadius C M 2) atTop (nhds 0) := by
    simpa [sourceTailRadius, div_eq_mul_inv] using (hi.const_mul C).mul_const ((16:ℝ)^(2*2))
  have hA : Tendsto (fun _ : ℕ => sourceCoefficientMass 2) atTop (nhds (sourceCoefficientMass 2)) :=
    tendsto_const_nhds
  have hp := (((hA.mul hr).const_mul 2).add ((hr.pow 2).const_mul 3)).const_mul (4*(2:ℝ)^2)
  have hp' := hp.mul_const 4
  simpa [evenTwoBudgetUpper, mul_assoc] using hp'

theorem c3_explicit_cutoff_conditions_eventually (C : ℝ) :
    ∀ᶠ M : ℕ in atTop,
      C / ((M:ℝ)+1) < nativeC 0 ∧
      21 * evenTwoBudgetUpper C M < (1/10^8-1/10^13:ℝ) := by
  have hm : Tendsto (fun M : ℕ => (M:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hfirst : Tendsto (fun M : ℕ => C / ((M:ℝ)+1)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hm).const_mul C
  have hsecond : Tendsto (fun M : ℕ => 21 * evenTwoBudgetUpper C M) atTop (nhds 0) := by
    simpa using (evenTwoBudgetUpper_tendsto_zero C).const_mul 21
  filter_upwards [hfirst.eventually (Iio_mem_nhds native_source_c0_positive_from_boxes),
    hsecond.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/10^8-1/10^13))] with M h1 h2
  exact ⟨h1,h2⟩

theorem c3_explicit_source_cutoff_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      C / ((M:ℝ)+1) < nativeC 0 ∧
      21 * evenTwoBudgetUpper C M < (1/10^8-1/10^13:ℝ) ∧
      literalHead M 0 ≠ 0 ∧ ∀ t : ℝ, |t| ≤ 1 →
        20 * literalErrorBudget M M false 2 (twoMonic t) (twoMonic t) <
          (literalTerm M M true true false 2 (twoMonic t) (twoMonic t)).re := by
  obtain ⟨C,hC,hcriterion⟩ := c3_monic_margin_of_explicit_budget
  refine ⟨C,hC,?_⟩
  filter_upwards [c3_explicit_cutoff_conditions_eventually C] with M hM
  exact ⟨hM.1,hM.2,hcriterion M hM.1 hM.2⟩

#print axioms literal_head_ne_of_tail_envelope
#print axioms c3_monic_margin_of_explicit_budget
#print axioms c3_explicit_source_cutoff_exists
end
end CarrySourceBezout
