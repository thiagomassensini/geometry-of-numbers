import InfiniteC3Tail
import DressingBounds

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CarryC3Gamma CPFormal.Analytic.Cp
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem height_parameter_crosswalk (w : ℂ) :
    operatorHeightParameter w=GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoDressingParameter w := rfl

theorem height_strip (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    operatorHeightParameter w ∈ genuineCriticalStrip := by
  have hi := Complex.abs_im_le_norm w
  norm_num [genuineCriticalStrip,operatorHeightParameter,Complex.mul_re]
  constructor <;> linarith [le_abs_self w.im,neg_abs_le w.im]

theorem c3_chart_inverse_bound (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖(cpChartFactor 3 (operatorHeightParameter w))⁻¹‖ ≤ 4 := by
  have hs := height_strip w hw
  have hi := Complex.im_le_norm w
  have hr : (1/4:ℝ) ≤ (1-operatorHeightParameter w).re := by
    norm_num [operatorHeightParameter,Complex.mul_re]
    have hh := neg_abs_le w.im
    have hb := Complex.abs_im_le_norm w
    linarith
  have hl : 1 ≤ Real.log 3 := by
    have h := CarryC3Gamma.log_three_box
    have hb := (abs_le.mp h).1
    norm_num [CarryC3Gamma.logReference] at hb
    linarith
  have hp : 5/4 ≤ ‖(3:ℂ)^(1-operatorHeightParameter w)‖ := by
    rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3),Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
    have hm : (1/4:ℝ) ≤ Real.log 3*(1-operatorHeightParameter w).re := by nlinarith
    have he := Real.add_one_le_exp (Real.log 3*(1-operatorHeightParameter w).re)
    linarith
  have hnorm : (1/4:ℝ) ≤ ‖cpChartFactor 3 (operatorHeightParameter w)‖ := by
    have h := norm_sub_norm_le ((3:ℂ)^(1-operatorHeightParameter w)) 1
    rw [norm_one,norm_sub_rev] at h
    exact le_trans (by linarith : (1/4:ℝ)≤‖(3:ℂ)^(1-operatorHeightParameter w)‖-1) h
  rw [norm_inv]
  exact (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by simpa using hnorm)

theorem c3_xi_without_gamma_bound (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖xiBeforeGamma w‖ ≤ 3 := by
  have he : xiBeforeGamma w=CarryReadoutBounds.polynomialFactor w*CarryReadoutBounds.exponentialFactor w := rfl
  rw [he,norm_mul]
  exact (mul_le_mul (CarryReadoutBounds.polynomial_factor_bounds w hw).1
    (CarryReadoutBounds.exponential_factor_bounds w hw).1 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

def c3ElementaryMultiplier (w : ℂ) : ℂ := xiBeforeGamma w/cpChartFactor 3 (operatorHeightParameter w)

theorem c3_elementary_bound (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖c3ElementaryMultiplier w‖ ≤ 12 := by
  rw [c3ElementaryMultiplier,div_eq_mul_inv,norm_mul]
  exact (mul_le_mul (c3_xi_without_gamma_bound w hw) (c3_chart_inverse_bound w hw)
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem c3_value_multiplier_bound (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖valueMultiplier w‖ ≤ 96 := by
  rw [c3_value_multiplier_gamma_factorization,norm_mul]
  have hg : ‖nativeGamma w‖ ≤ 8 := by
    have he : nativeGamma w=CarryReadoutBounds.gammaFactor w := rfl
    rw [he]
    exact CarryReadoutBounds.gamma_factor_bound w hw
  exact (mul_le_mul (c3_elementary_bound w hw) hg (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem native_boundary_at64_bound (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖c3Boundary (fun n => c3Sample n w) 194‖ ≤ 1 := by
  have h (n : ℕ) := native_fd_bound n 194 (by norm_num) w hw
  unfold c3Boundary
  have t1 : ‖(-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194‖ ≤ (1/3:ℝ)*(Nat.factorial 1:ℝ)/(194:ℝ)^1 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 1) (by norm_num)).trans_eq (by ring)
  have t2 : ‖(1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194‖ ≤ (1/3:ℝ)*(Nat.factorial 2:ℝ)/(194:ℝ)^2 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 2) (by norm_num)).trans_eq (by ring)
  have t3 : ‖(2/9:ℂ)*fd 3 (fun n => c3Sample n w) 194‖ ≤ (2/9:ℝ)*(Nat.factorial 3:ℝ)/(194:ℝ)^3 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 3) (by norm_num)).trans_eq (by ring)
  have t4 : ‖(1/9:ℂ)*fd 4 (fun n => c3Sample n w) 194‖ ≤ (1/9:ℝ)*(Nat.factorial 4:ℝ)/(194:ℝ)^4 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 4) (by norm_num)).trans_eq (by ring)
  have t5 : ‖(1/27:ℂ)*fd 5 (fun n => c3Sample n w) 194‖ ≤ (1/27:ℝ)*(Nat.factorial 5:ℝ)/(194:ℝ)^5 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 5) (by norm_num)).trans_eq (by ring)
  have t7 : ‖(1/81:ℂ)*fd 7 (fun n => c3Sample n w) 194‖ ≤ (1/81:ℝ)*(Nat.factorial 7:ℝ)/(194:ℝ)^7 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 7) (by norm_num)).trans_eq (by ring)
  have t8 : ‖(1/81:ℂ)*fd 8 (fun n => c3Sample n w) 194‖ ≤ (1/81:ℝ)*(Nat.factorial 8:ℝ)/(194:ℝ)^8 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 8) (by norm_num)).trans_eq (by ring)
  have t9 : ‖(2/243:ℂ)*fd 9 (fun n => c3Sample n w) 194‖ ≤ (2/243:ℝ)*(Nat.factorial 9:ℝ)/(194:ℝ)^9 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 9) (by norm_num)).trans_eq (by ring)
  have t10 : ‖(1/243:ℂ)*fd 10 (fun n => c3Sample n w) 194‖ ≤ (1/243:ℝ)*(Nat.factorial 10:ℝ)/(194:ℝ)^10 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 10) (by norm_num)).trans_eq (by ring)
  have t11 : ‖(1/729:ℂ)*fd 11 (fun n => c3Sample n w) 194‖ ≤ (1/729:ℝ)*(Nat.factorial 11:ℝ)/(194:ℝ)^11 := by
    rw [norm_mul]
    norm_num only [norm_neg,norm_div,norm_one,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (h 11) (by norm_num)).trans_eq (by ring)
  have s1 := (norm_add_le ((-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194) ((1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194)).trans (add_le_add t1 t2)
  have s2 := (norm_sub_le (((-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194)+((1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194)) ((2/9:ℂ)*fd 3 (fun n => c3Sample n w) 194)).trans (add_le_add s1 t3)
  have s3 := (norm_add_le ((((-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194)+((1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194))-((2/9:ℂ)*fd 3 (fun n => c3Sample n w) 194)) ((1/9:ℂ)*fd 4 (fun n => c3Sample n w) 194)).trans (add_le_add s2 t4)
  have s4 := (norm_sub_le (((((-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194)+((1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194))-((2/9:ℂ)*fd 3 (fun n => c3Sample n w) 194))+((1/9:ℂ)*fd 4 (fun n => c3Sample n w) 194)) ((1/27:ℂ)*fd 5 (fun n => c3Sample n w) 194)).trans (add_le_add s3 t5)
  have s5 := (norm_add_le ((((((-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194)+((1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194))-((2/9:ℂ)*fd 3 (fun n => c3Sample n w) 194))+((1/9:ℂ)*fd 4 (fun n => c3Sample n w) 194))-((1/27:ℂ)*fd 5 (fun n => c3Sample n w) 194)) ((1/81:ℂ)*fd 7 (fun n => c3Sample n w) 194)).trans (add_le_add s4 t7)
  have s6 := (norm_sub_le (((((((-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194)+((1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194))-((2/9:ℂ)*fd 3 (fun n => c3Sample n w) 194))+((1/9:ℂ)*fd 4 (fun n => c3Sample n w) 194))-((1/27:ℂ)*fd 5 (fun n => c3Sample n w) 194))+((1/81:ℂ)*fd 7 (fun n => c3Sample n w) 194)) ((1/81:ℂ)*fd 8 (fun n => c3Sample n w) 194)).trans (add_le_add s5 t8)
  have s7 := (norm_add_le ((((((((-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194)+((1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194))-((2/9:ℂ)*fd 3 (fun n => c3Sample n w) 194))+((1/9:ℂ)*fd 4 (fun n => c3Sample n w) 194))-((1/27:ℂ)*fd 5 (fun n => c3Sample n w) 194))+((1/81:ℂ)*fd 7 (fun n => c3Sample n w) 194))-((1/81:ℂ)*fd 8 (fun n => c3Sample n w) 194)) ((2/243:ℂ)*fd 9 (fun n => c3Sample n w) 194)).trans (add_le_add s6 t9)
  have s8 := (norm_sub_le (((((((((-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194)+((1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194))-((2/9:ℂ)*fd 3 (fun n => c3Sample n w) 194))+((1/9:ℂ)*fd 4 (fun n => c3Sample n w) 194))-((1/27:ℂ)*fd 5 (fun n => c3Sample n w) 194))+((1/81:ℂ)*fd 7 (fun n => c3Sample n w) 194))-((1/81:ℂ)*fd 8 (fun n => c3Sample n w) 194))+((2/243:ℂ)*fd 9 (fun n => c3Sample n w) 194)) ((1/243:ℂ)*fd 10 (fun n => c3Sample n w) 194)).trans (add_le_add s7 t10)
  have s9 := (norm_add_le ((((((((((-(1/3):ℂ)*fd 1 (fun n => c3Sample n w) 194)+((1/3:ℂ)*fd 2 (fun n => c3Sample n w) 194))-((2/9:ℂ)*fd 3 (fun n => c3Sample n w) 194))+((1/9:ℂ)*fd 4 (fun n => c3Sample n w) 194))-((1/27:ℂ)*fd 5 (fun n => c3Sample n w) 194))+((1/81:ℂ)*fd 7 (fun n => c3Sample n w) 194))-((1/81:ℂ)*fd 8 (fun n => c3Sample n w) 194))+((2/243:ℂ)*fd 9 (fun n => c3Sample n w) 194))-((1/243:ℂ)*fd 10 (fun n => c3Sample n w) 194)) ((1/729:ℂ)*fd 11 (fun n => c3Sample n w) 194)).trans (add_le_add s8 t11)
  have hb := s9
  norm_num at hb
  have hf := hb.trans (show (223531688023316339995:ℝ)/128754252555854474281554 ≤ 1 by norm_num)
  simpa only [neg_div,neg_mul] using hf

theorem c3_prefix_bound (M : ℕ) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖finiteBracketedDirichletChart 3 M (operatorHeightParameter w)‖ ≤ 3 := by
  have hm (m : ℕ) : (2:ℝ)/((3*m+2:ℕ):ℝ)^2 ≤ 2/((m+1:ℕ):ℝ)-2/((m+2:ℕ):ℝ) := by
    have he : 2/((m+1:ℕ):ℝ)-2/((m+2:ℕ):ℝ) = 2/(((m+1:ℕ):ℝ)*((m+2:ℕ):ℝ)) := by
      push_cast
      field_simp
      ring
    rw [he]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have hs : ∀ N : ℕ, (∑ m ∈ Finset.range N, (2:ℝ)/((3*m+2:ℕ):ℝ)^2) ≤ 2 := by
    have ht : ∀ N : ℕ, (∑ m ∈ Finset.range N, (2:ℝ)/((3*m+2:ℕ):ℝ)^2) ≤ 2-2/((N+1:ℕ):ℝ) := by
      intro N
      induction N with
      | zero => norm_num
      | succ N ih =>
        rw [Finset.sum_range_succ]
        have hh := hm N
        norm_num only [Nat.succ_eq_add_one,Nat.add_assoc] at *
        linarith
    intro N
    exact (ht N).trans (sub_le_self _ (by positivity))
  rw [finiteBracketedDirichletChart_three_eq_one_add_trace,finiteCanonicalBracketTrace]
  apply (norm_add_le _ _).trans
  rw [norm_one]
  have hh : ‖∑ m ∈ Finset.range M, realCpSaturatedBracket 3 m (operatorHeightParameter w)‖ ≤
      ∑ m ∈ Finset.range M, (2:ℝ)/((3*m+2:ℕ):ℝ)^2 := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro m hm
    rw [native_c3_cell_fd]
    simpa using native_fd_bound 2 (3*m+2) (by omega) w hw
  linarith [hs M]

theorem c3_accelerated_head_at64_bound (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖acceleratedC3Head 64 w‖ ≤ 4 := by
  unfold acceleratedC3Head
  have hb := native_boundary_at64_bound w hw
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at *
  exact (norm_add_le _ _).trans ((add_le_add (c3_prefix_bound 64 w hw) hb).trans_eq (by norm_num))

end
end CarryC3Tail
