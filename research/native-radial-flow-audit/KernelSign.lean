import KernelTaylor
import FlowInterval

namespace CarryRadialFlow
open CarrySelfAdjointOperator Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem flowJetWitness_re_neg : flowJetWitness.re<0 := by
  simpa [flowJetWitness,mu] using actual_flow_jet_witness_neg

/-- Actual four-address kernel: strict sign AFTER all sixteen crossings and
the entire analytic remainder. No assertion about a canonical Hankel sign. -/
theorem fourFlowKernel_normalized_eventually_neg :
    ∀ᶠ k : ℕ in atTop,
      (fourFlowKernel (canonicalGreenJetStep k)/canonicalGreenJetStep k^7).re<0 := by
  have hn : (36*flowJetWitness).re<0 := by
    simpa [Complex.mul_re] using mul_neg_of_pos_of_neg (by norm_num : (0:ℝ)<36) flowJetWitness_re_neg
  exact Filter.Tendsto.eventually_lt
    (Complex.continuous_re.continuousAt.tendsto.comp fourFlowKernel_normalized_tendsto)
    tendsto_const_nhds hn

theorem fourFlowKernel_eventually_neg :
    ∀ᶠ k : ℕ in atTop, (fourFlowKernel (canonicalGreenJetStep k)).re<0 := by
  filter_upwards [fourFlowKernel_normalized_eventually_neg] with k hk
  have hr : canonicalGreenJetStep k=(((((k:ℝ)+1)⁻¹):ℝ):ℂ) := by
    unfold canonicalGreenJetStep
    push_cast
    rfl
  have hp : 0<(((k:ℝ)+1)⁻¹)^7 := by positivity
  rw [hr,← Complex.ofReal_pow,Complex.div_ofReal_re] at hk
  have hh := mul_lt_mul_of_pos_right hk hp
  simpa only [hr,div_mul_cancel₀ _ (ne_of_gt hp),zero_mul] using hh

def radialWeightReal (h : ℝ) : Fin 4 → ℝ :=
  ![-1-(21/500)*h^2,3+(21/500)*h^2,-3,1]

theorem radialWeight_ofReal (h : ℝ) (i : Fin 4) :
    radialWeight (h:ℂ) i=(radialWeightReal h i:ℂ) := by
  fin_cases i <;> norm_num [radialWeight,radialWeightReal]

/-- The real symmetric matrix being tested is the original two-argument
derived response kernel, with the same four addresses. -/
def realFlowMatrix (h : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
  (-Complex.I*(flowResponse (Complex.I*address i*(h:ℂ))+
    flowResponse (Complex.I*address j*(h:ℂ)))/(address i+address j)).re

theorem fourFlowKernel_real_form (h : ℝ) :
    (fourFlowKernel (h:ℂ)).re=
      ∑ i : Fin 4, ∑ j : Fin 4,
        radialWeightReal h i*radialWeightReal h j*realFlowMatrix h i j := by
  unfold fourFlowKernel realFlowMatrix
  simp_rw [radialWeight_ofReal]
  simp only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,sub_zero,add_zero]

/-- The independent candidate generator kernel is not positive on every
real source direction, even arbitrarily close to the original center. -/
theorem fourFlowMatrix_eventually_not_nonnegative :
    ∀ᶠ k : ℕ in atTop, ¬∀ v : Fin 4 → ℝ,
      0≤∑ i : Fin 4, ∑ j : Fin 4, v i*v j*realFlowMatrix (((k:ℝ)+1)⁻¹) i j := by
  filter_upwards [fourFlowKernel_eventually_neg] with k hk hall
  have hr : canonicalGreenJetStep k=(((((k:ℝ)+1)⁻¹):ℝ):ℂ) := by
    unfold canonicalGreenJetStep
    push_cast
    rfl
  rw [hr,fourFlowKernel_real_form] at hk
  exact (not_le_of_gt hk) (hall (radialWeightReal (((k:ℝ)+1)⁻¹)))

end
end CarryRadialFlow
