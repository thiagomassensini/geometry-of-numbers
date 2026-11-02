import SourceGate
import FourNativeBoxes

/-!
# Prefixo da terceira direção par a partir da fonte C3

As quatro caixas já certificadas da fonte implicam a invertibilidade do prefixo
antigo 2×2, sem caixas theta e sem a hipótese de sinal do novo pivô.
-/
namespace CarrySourceDimensionThree
open CarrySourceBezout CarrySelfAdjointOperator Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem third_even_prefix_isUnit_from_c3 : IsUnit (sourceMomentMatrix nativeH 0 2) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  have hp := CarryC3Boxes.canonical_two_even_determinant_pos_from_c3
  have hd : (sourceMomentMatrix nativeH 0 2).det =
      nativeH 0 * nativeH 2 - (nativeH 1)^2 := by
    simp [Matrix.det_fin_two, sourceMomentMatrix, nativeH]
    ring
  rw [hd]
  exact ne_of_gt hp

theorem third_even_gate_no_prefix_assumption :
    0 < sourceMomentSchur nativeH 0 2 ↔
      nativeC 5 < evenSourceCeiling nativeC / (5*nativeC 0) :=
  native_even_gate third_even_prefix_isUnit_from_c3

theorem third_odd_prefix_first_entry_pos_from_c3 :
    0 < nativeC 1 ^ 2 - 2 * nativeC 0 * nativeC 2 := by
  have h0 := abs_le.mp (native_real_four_reference_bounds 0)
  have h1 := abs_le.mp (native_real_four_reference_bounds 1)
  have h2 := abs_le.mp (native_real_four_reference_bounds 2)
  norm_num [twoEvenReferenceReal] at h0 h1 h2
  have hc0 : 0 ≤ nativeC 0 ∧ nativeC 0 ≤ 1/2 := by constructor <;> linarith [h0.1,h0.2]
  have hc1 : nativeC 1 ≤ -(114/10000:ℝ) := by linarith [h1.2]
  have hc2 : 0 ≤ nativeC 2 ∧ nativeC 2 ≤ 124/1000000 := by constructor <;> linarith [h2.1,h2.2]
  have hm : nativeC 0 * nativeC 2 ≤ (1/2:ℝ)*(124/1000000) :=
    mul_le_mul hc0.2 hc2.2 hc2.1 (by norm_num)
  have hs : (114/10000:ℝ)^2 ≤ nativeC 1^2 := by nlinarith [sq_nonneg (nativeC 1 + 114/10000)]
  norm_num at hm hs ⊢
  nlinarith

theorem odd_prefix_det_shift (c : ℕ → ℝ) (d : ℝ) :
    (coefficientBlock (sourceKernel (perturb c 4 d) true) 2).det =
      (coefficientBlock (sourceKernel c true) 2).det -
        4*c 0*(c 1^2-2*c 0*c 2)*d := by
  rw [source_odd_two, source_odd_two, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [perturb]
  ring

theorem third_odd_prefix_four_coefficients_insufficient :
    ∃ c : ℕ → ℝ, (∀ j < 4, c j = nativeC j) ∧
      (coefficientBlock (sourceKernel c true) 2).det = 0 := by
  let a := 4*nativeC 0*(nativeC 1^2-2*nativeC 0*nativeC 2)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (mul_ne_zero (by norm_num) native_source_c0_positive_from_boxes.ne')
      third_odd_prefix_first_entry_pos_from_c3.ne'
  let d := (coefficientBlock (sourceKernel nativeC true) 2).det / a
  refine ⟨perturb nativeC 4 d, ?_, ?_⟩
  · intro j hj
    simp [perturb, Nat.ne_of_lt hj]
  · rw [odd_prefix_det_shift]
    change _ - a*d = 0
    dsimp [d]
    field_simp
    ring

#print axioms third_odd_prefix_first_entry_pos_from_c3
#print axioms odd_prefix_det_shift
#print axioms third_odd_prefix_four_coefficients_insufficient
#print axioms third_even_prefix_isUnit_from_c3
#print axioms third_even_gate_no_prefix_assumption
end
end CarrySourceDimensionThree
