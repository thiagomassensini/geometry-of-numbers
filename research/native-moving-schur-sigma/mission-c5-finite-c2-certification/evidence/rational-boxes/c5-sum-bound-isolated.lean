import Mathlib.Analysis.PSeries

open Finset

namespace CarrySigmaObstruction

private theorem c5_inv_sq_sum_range_le_isolated (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n, ((k + 1 : ℚ) ^ 2)⁻¹) ≤ 2 := by
  have hsum :
      (∑ k ∈ Finset.range n, ((k + 1 : ℚ) ^ 2)⁻¹) =
        1 + ∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℚ) ^ 2)⁻¹ := by
    have hIco :
        (∑ k ∈ Finset.range n, ((k + 1 : ℚ) ^ 2)⁻¹) =
          ∑ i ∈ Finset.Ico 1 (n + 1), ((i : ℚ) ^ 2)⁻¹ := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm]
    have hset : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ioo 1 (n + 1)) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Ioo]
      omega
    rw [hIco, hset, Finset.sum_insert]
    · norm_num
    · simp
  rw [hsum]
  have htail := sum_Ioo_inv_sq_le (α := ℚ) 1 (n + 1)
  have htail' :
      (∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℚ) ^ 2)⁻¹) ≤ 1 := by
    norm_num at htail
    simpa using htail
  calc
    1 + ∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℚ) ^ 2)⁻¹ =
        (∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℚ) ^ 2)⁻¹) + 1 := by ring
    _ ≤ 1 + 1 := add_le_add_left htail' (1 : ℚ)
    _ = 2 := by norm_num

end CarrySigmaObstruction
