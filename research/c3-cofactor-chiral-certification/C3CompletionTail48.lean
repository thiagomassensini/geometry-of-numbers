import C3Boundary48Stencil
import FiniteEvaluationError

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CarryC3Gamma CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The C3/48 head retains the original finite bracket and replaces only its
boundary by the exactly verified doubled boundary. -/
def acceleratedC3Head48 (M : ℕ) (w : ℂ) : ℂ :=
  finiteBracketedDirichletChart 3 M (operatorHeightParameter w) +
    c3Boundary48 (fun n => c3Sample n w) (3*M+2)

/-- The complementary tail is the original cutoff tail minus that boundary. -/
def acceleratedC3Tail48 (M : ℕ) (w : ℂ) : ℂ :=
  realCpBracketCutoffTail 3 M (operatorHeightParameter w) -
    c3Boundary48 (fun n => c3Sample n w) (3*M+2)

theorem native_c3_head_tail48 (M : ℕ) (w : ℂ) (hw : ‖w‖ < (1:ℝ)) :
    fullC3Signal w = acceleratedC3Head48 M w + acceleratedC3Tail48 M w := by
  rw [fullC3Signal, bracketedDirichletChart_eq_finite_add_cutoffTail 3 M
    (by norm_num) (height_mem_bracket_half_plane w hw)]
  unfold acceleratedC3Head48 acceleratedC3Tail48
  ring

theorem c3_boundary48_analytic (M : ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun w => c3Boundary48 (fun n => c3Sample n w) (3*M+2)) w := by
  have he : (fun w => c3Boundary48 (fun n => c3Sample n w) (3*M+2)) =
      (fun w => ∑ k : Fin 24,
        (boundary48Weight k : ℂ)*c3Sample (3*M+2+k.val) w) := by
    funext w
    exact boundary48_stencil (fun n => c3Sample n w) (3*M+2)
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact analyticAt_const.mul
    ((c3_sample_entire (3*M+2+k.val) (by omega)).analyticAt w)

theorem accelerated_c3_head48_analytic (M : ℕ) :
    AnalyticAt ℂ (acceleratedC3Head48 M) 0 := by
  have hf : Differentiable ℂ (finiteBracketedDirichletChart 3 M) :=
    fun s => (hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet M s).differentiableAt
  have hp : AnalyticAt ℂ operatorHeightParameter 0 := by
    unfold operatorHeightParameter
    fun_prop
  exact ((hf.analyticAt _).comp hp).add (c3_boundary48_analytic M 0)

theorem accelerated_c3_tail48_analytic (M : ℕ) (w : ℂ) (hw : ‖w‖ < (1:ℝ)) :
    AnalyticAt ℂ (acceleratedC3Tail48 M) w := by
  exact (original_c3_tail_analytic M w hw).sub
    (c3_boundary48_analytic M w)

theorem accelerated_c3_tail48_bound (M : ℕ) (hM : 0 < M)
    (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖acceleratedC3Tail48 M w‖ ≤
      (Nat.factorial 26:ℝ)/(729^2*(3*(M:ℝ)-1)^25) := by
  rw [acceleratedC3Tail48, native_c3_tail_acceleration48 M w hw, add_sub_cancel_left,
    norm_mul]
  have hfactor : ‖(1/(729^2:ℂ))‖ = (1/(729^2:ℝ)) := by norm_num
  rw [hfactor]
  calc
    _ ≤ (1/(729^2:ℝ))*((Nat.factorial 26:ℝ)/(3*(M:ℝ)-1)^25) :=
      mul_le_mul_of_nonneg_left (c3_twenty_sixth_series_bound M hM w hw) (by positivity)
    _ = (Nat.factorial 26:ℝ)/(729^2*(3*(M:ℝ)-1)^25) := by
      field_simp

def completedTailError48 (M : ℕ) (w : ℂ) : ℂ :=
  valueMultiplier w * acceleratedC3Tail48 M w

def completedHead48 (M : ℕ) (w : ℂ) : ℂ :=
  (c3ElementaryMultiplier w * acceleratedC3Head48 M w) * nativeGamma w

theorem completed_native_head_tail48 (M : ℕ) (w : ℂ) (hw : ‖w‖ < (1:ℝ)) :
    completedNativeOperatorCharacteristic w = completedHead48 M w + completedTailError48 M w := by
  rw [characteristic_c3_formula, native_c3_head_tail48 M w hw,
    c3_value_multiplier_gamma_factorization]
  unfold completedHead48 completedTailError48 c3ElementaryMultiplier
  rw [c3_value_multiplier_gamma_factorization]
  ring

theorem completed_tail48_jet_bound (M : ℕ) (hM : 0 < M) (r : ℕ) :
    ‖sourceJet r (completedTailError48 M)‖ ≤
      (96*(Nat.factorial 26:ℝ)/(729^2*(3*(M:ℝ)-1)^25))*4^r := by
  refine cauchy_quarter (completedTailError48 M)
    (96*(Nat.factorial 26:ℝ)/(729^2*(3*(M:ℝ)-1)^25)) ?_ ?_ r
  · intro w hw
    exact (value_multiplier_analytic_at w (lt_of_le_of_lt hw (by norm_num))).mul
      (accelerated_c3_tail48_analytic M w (lt_of_le_of_lt hw (by norm_num)))
  · intro w hw
    rw [completedTailError48, norm_mul]
    calc
      _ ≤ 96 * ‖acceleratedC3Tail48 M w‖ :=
        mul_le_mul_of_nonneg_right (c3_value_multiplier_bound w hw) (norm_nonneg _)
      _ ≤ 96*((Nat.factorial 26:ℝ)/(729^2*(3*(M:ℝ)-1)^25)) :=
        mul_le_mul_of_nonneg_left
          (accelerated_c3_tail48_bound M hM w (hw.trans (by norm_num))) (by norm_num)
      _ = 96*(Nat.factorial 26:ℝ)/(729^2*(3*(M:ℝ)-1)^25) := by ring

/-- At M=48 the original completion multiplier and Cauchy factor still leave
the order-26 tail below 10^-20 through derivative order twelve. -/
theorem completed_tail48_jet_error_through_twelve (r : Fin 13) :
    ‖sourceJet r.val (completedTailError48 48)‖ ≤ (1/10^20:ℝ) := by
  have h := completed_tail48_jet_bound 48 (by norm_num) r.val
  have hp : (4:ℝ)^r.val ≤ 4^12 := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ (96*(Nat.factorial 26:ℝ)/(729^2*(3*(48:ℝ)-1)^25))*4^r.val := h
    _ ≤ (96*(Nat.factorial 26:ℝ)/(729^2*(3*(48:ℝ)-1)^25))*4^12 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 1/10^20 := by norm_num

#print axioms boundary48_stencil
#print axioms native_c3_head_tail48
#print axioms accelerated_c3_tail48_bound
#print axioms completed_native_head_tail48
#print axioms completed_tail48_jet_error_through_twelve

end
end CarryC3Tail
