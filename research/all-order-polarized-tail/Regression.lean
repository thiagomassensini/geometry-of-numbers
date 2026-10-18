import BoundaryControl
import BudgetScale

namespace CarrySourceTail
open CarrySelfAdjointOperator CarryCriticalSource
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- Exact rational bounds, checked in the kernel, not decimal experiments. -/
theorem certified_five_cutoff_constants :
    cutoffError 0 5 < 1/240000 ∧ cutoffError 1 5 < 1/1900000 := by
  norm_num [cutoffError,rate]

theorem empty_tail_regression (s N : ℕ) (x : Fin N → ℂ) (a : Fin 0 → ℂ) :
    sourcePair s (Fin.append x a) (Fin.append x a) = sourcePair s x x := by
  rw [sourcePair_append]
  simp [sourcePair]

theorem diagonal_imaginary_regression {n : ℕ} (s : ℕ) (x : Fin n → ℂ) :
    (sourcePair s x x).im = 0 := by
  rw [sourcePair_im]
  have he : sourceRealPair s (fun i => (x i).re) (fun i => (x i).im) =
      sourceRealPair s (fun i => (x i).im) (fun i => (x i).re) := by
    unfold sourceRealPair
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show j.val+i.val+s=i.val+j.val+s by omega]
    ring
  rw [he,sub_self]

end
end CarrySourceTail
