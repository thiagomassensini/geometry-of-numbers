import TwelveCoordinates

namespace CarrySixthRelative
open CarrySelfAdjointOperator CarryDirectAnchor CarryIntegralCertificate CarryVariationalSchur
open CarryCriticalSource CarrySixthOdd
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

theorem transformed_diag_lower (i : Fin 5) : (1/4:ℝ) ≤ transformedOld i i := by
  rw [transformedOld_entry]
  have h := mem_of_contained (mem_trialPairingBox i.val i.val)
    (show (trialPairingBox i.val i.val).contained
      (.finite (25*10^58) (10*intervalScale))=true by fin_cases i <;> decide +kernel)
  norm_num [Box.Mem,intervalScale] at h
  nlinarith [h.1]

theorem transformed_offdiag_abs (i j : Fin 5) (hij : i ≠ j) :
    |transformedOld i j| ≤ (1/100:ℝ) := by
  rw [transformedOld_entry]
  have h := mem_of_contained (mem_trialPairingBox i.val j.val)
    (show (trialPairingBox i.val j.val).contained (.finite (-(10^58)) (10^58))=true by
      fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel)
  norm_num [Box.Mem,intervalScale] at h
  apply abs_le.mpr
  constructor <;> nlinarith [h.1,h.2]

theorem mixed_entry_lower (a x y : ℝ) (ha : |a| ≤ 1/100) :
    -(1/200:ℝ)*(x^2+y^2) ≤ x*a*y := by
  have hxy : |x*y| ≤ (x^2+y^2)/2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (x-y),sq_nonneg (x+y)]
  have hm := mul_le_mul ha hxy (abs_nonneg (x*y)) (by norm_num : (0:ℝ)≤1/100)
  have hbound : |x*a*y| ≤ (1/100:ℝ)*((x^2+y^2)/2) := by
    calc
      |x*a*y| = |a| * |x*y| := by simp [abs_mul,mul_comm,mul_left_comm]
      _ ≤ _ := hm
  have hl := (abs_le.mp hbound).1
  nlinarith

/-- Coercivity of the same old block in independently checked coordinates. -/
theorem transformed_old_coercive (y : Fin 5 → ℝ) :
    (1/5:ℝ)*(y ⬝ᵥ y) ≤ y ⬝ᵥ (transformedOld *ᵥ y) := by
  have hd0 := mul_le_mul_of_nonneg_right (transformed_diag_lower 0) (sq_nonneg (y 0))
  have hd1 := mul_le_mul_of_nonneg_right (transformed_diag_lower 1) (sq_nonneg (y 1))
  have hd2 := mul_le_mul_of_nonneg_right (transformed_diag_lower 2) (sq_nonneg (y 2))
  have hd3 := mul_le_mul_of_nonneg_right (transformed_diag_lower 3) (sq_nonneg (y 3))
  have hd4 := mul_le_mul_of_nonneg_right (transformed_diag_lower 4) (sq_nonneg (y 4))
  have h01 := mixed_entry_lower (transformedOld 0 1) (y 0) (y 1) (transformed_offdiag_abs 0 1 (by decide))
  have h02 := mixed_entry_lower (transformedOld 0 2) (y 0) (y 2) (transformed_offdiag_abs 0 2 (by decide))
  have h03 := mixed_entry_lower (transformedOld 0 3) (y 0) (y 3) (transformed_offdiag_abs 0 3 (by decide))
  have h04 := mixed_entry_lower (transformedOld 0 4) (y 0) (y 4) (transformed_offdiag_abs 0 4 (by decide))
  have h10 := mixed_entry_lower (transformedOld 1 0) (y 1) (y 0) (transformed_offdiag_abs 1 0 (by decide))
  have h12 := mixed_entry_lower (transformedOld 1 2) (y 1) (y 2) (transformed_offdiag_abs 1 2 (by decide))
  have h13 := mixed_entry_lower (transformedOld 1 3) (y 1) (y 3) (transformed_offdiag_abs 1 3 (by decide))
  have h14 := mixed_entry_lower (transformedOld 1 4) (y 1) (y 4) (transformed_offdiag_abs 1 4 (by decide))
  have h20 := mixed_entry_lower (transformedOld 2 0) (y 2) (y 0) (transformed_offdiag_abs 2 0 (by decide))
  have h21 := mixed_entry_lower (transformedOld 2 1) (y 2) (y 1) (transformed_offdiag_abs 2 1 (by decide))
  have h23 := mixed_entry_lower (transformedOld 2 3) (y 2) (y 3) (transformed_offdiag_abs 2 3 (by decide))
  have h24 := mixed_entry_lower (transformedOld 2 4) (y 2) (y 4) (transformed_offdiag_abs 2 4 (by decide))
  have h30 := mixed_entry_lower (transformedOld 3 0) (y 3) (y 0) (transformed_offdiag_abs 3 0 (by decide))
  have h31 := mixed_entry_lower (transformedOld 3 1) (y 3) (y 1) (transformed_offdiag_abs 3 1 (by decide))
  have h32 := mixed_entry_lower (transformedOld 3 2) (y 3) (y 2) (transformed_offdiag_abs 3 2 (by decide))
  have h34 := mixed_entry_lower (transformedOld 3 4) (y 3) (y 4) (transformed_offdiag_abs 3 4 (by decide))
  have h40 := mixed_entry_lower (transformedOld 4 0) (y 4) (y 0) (transformed_offdiag_abs 4 0 (by decide))
  have h41 := mixed_entry_lower (transformedOld 4 1) (y 4) (y 1) (transformed_offdiag_abs 4 1 (by decide))
  have h42 := mixed_entry_lower (transformedOld 4 2) (y 4) (y 2) (transformed_offdiag_abs 4 2 (by decide))
  have h43 := mixed_entry_lower (transformedOld 4 3) (y 4) (y 3) (transformed_offdiag_abs 4 3 (by decide))
  simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_succ,Fin.sum_univ_zero] at ⊢
  norm_num at *
  simp only [show (Fin.succ (2:Fin 4))=(3:Fin 5) from rfl,
    show (Fin.succ (Fin.succ (2:Fin 3)))=(4:Fin 5) from rfl] at *
  nlinarith

end
end CarrySixthRelative
