import GeometryOfNumbers.Analysis.BaseTwoCenterCouplingRaw
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Sampled prefix bound for exactly the material cutoffs `4*k+3`. -/
noncomputable section
open scoped BigOperators
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

private theorem reciprocal_sqrt_step (j : ℕ) :
    (Real.sqrt (j+1 : ℝ))⁻¹ ≤ 2 * (Real.sqrt (j+1 : ℝ) - Real.sqrt (j : ℝ)) := by
  have hp : 0 < Real.sqrt (j+1 : ℝ) := by positivity
  have hq := Real.sqrt_nonneg (j : ℝ)
  have hs := Real.sqrt_le_sqrt (show (j : ℝ) ≤ j+1 by linarith)
  have ha := Real.sq_sqrt (show 0 ≤ (j+1 : ℝ) by positivity)
  have hb := Real.sq_sqrt (show 0 ≤ (j : ℝ) by positivity)
  rw [← one_div]
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (Real.sqrt (j+1 : ℝ) - Real.sqrt (j : ℝ))]

private theorem reciprocal_sqrt_prefix (m : ℕ) :
    (∑ j ∈ Finset.range m, (Real.sqrt (j+1 : ℝ))⁻¹) ≤ 2 * Real.sqrt (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h := reciprocal_sqrt_step m
    push_cast
    linarith

private theorem weighted_prefix (g : ℕ → ℂ) (m : ℕ) :
    ‖∑ j ∈ Finset.range m, g j‖^2 ≤
      2 * Real.sqrt (m : ℝ) *
        ∑ j ∈ Finset.range m, Real.sqrt (j+1 : ℝ) * ‖g j‖^2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range m)
    (r := fun j => ‖g j‖)
    (f := fun j => Real.sqrt (j+1 : ℝ) * ‖g j‖^2)
    (g := fun j => (Real.sqrt (j+1 : ℝ))⁻¹)
    (fun j _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
    (fun j _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
    (fun j _ => by
      have hp : Real.sqrt (j+1 : ℝ) ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring_nf
      exact le_rfl)
  have hn := norm_sum_le (Finset.range m) g
  have hw : 0 ≤ ∑ j ∈ Finset.range m, Real.sqrt (j+1 : ℝ) * ‖g j‖^2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
  have hb := mul_le_mul_of_nonneg_left (reciprocal_sqrt_prefix m) hw
  have hsq : ‖∑ j ∈ Finset.range m, g j‖^2 ≤ (∑ j ∈ Finset.range m, ‖g j‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    _ ≤ _ := hsq.trans h
    _ ≤ _ := by simpa [mul_comm, mul_left_comm, mul_assoc] using hb

private theorem sampled_reciprocal_step (m : ℝ) (hm : 3 ≤ m) :
    (m * Real.sqrt m)⁻¹ ≤
      2 * ((Real.sqrt m)⁻¹ - (Real.sqrt (m+4))⁻¹) := by
  have mp : 0 < m := by linarith
  have a : 0 < Real.sqrt m := Real.sqrt_pos.mpr mp
  have b : 0 < Real.sqrt (m+4) := by positivity
  have ha := Real.sq_sqrt mp.le
  have hb := Real.sq_sqrt (show 0 ≤ m+4 by positivity)
  have hba : Real.sqrt (m+4) ≤ 2 * Real.sqrt m := by
    nlinarith [Real.sqrt_nonneg m, Real.sqrt_nonneg (m+4)]
  have hdiff : 0 ≤ Real.sqrt (m+4) - Real.sqrt m :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hprod : Real.sqrt (m+4) * (Real.sqrt (m+4) + Real.sqrt m) ≤ 8*m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (Real.sqrt_nonneg m),
      mul_nonneg (sub_nonneg.mpr hba) (Real.sqrt_nonneg (m+4))]
  have he : (Real.sqrt m)⁻¹ - (Real.sqrt (m+4))⁻¹ =
      4 / (Real.sqrt m * Real.sqrt (m+4) * (Real.sqrt (m+4) + Real.sqrt m)) := by
    field_simp
    nlinarith
  rw [he]
  rw [show 2 * (4 / (Real.sqrt m * Real.sqrt (m+4) *
      (Real.sqrt (m+4) + Real.sqrt m))) =
      8 / (Real.sqrt m * Real.sqrt (m+4) *
      (Real.sqrt (m+4) + Real.sqrt m)) by ring]
  rw [← one_div]
  apply (div_le_div_iff₀ (mul_pos mp a) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod a.le]

private def tailPotential (j k : ℕ) : ℝ :=
  if j < 4*k+3 then (Real.sqrt (4*k+3 : ℝ))⁻¹ else (Real.sqrt (j+1 : ℝ))⁻¹

private theorem sampled_tail_step (j k : ℕ) :
    (if j < 4*k+3 then ((4*k+3 : ℝ) * Real.sqrt (4*k+3 : ℝ))⁻¹ else 0) ≤
      2 * (tailPotential j k - tailPotential j (k+1)) := by
  by_cases h : j < 4*k+3
  · have h' : j < 4*(k+1)+3 := by omega
    simp only [tailPotential, if_pos h, if_pos h']
    convert sampled_reciprocal_step (4*(k : ℝ)+3) (by have := Nat.cast_nonneg (α := ℝ) k; linarith) using 1
    push_cast
    ring_nf
  · simp only [if_neg h, tailPotential]
    by_cases h' : j < 4*(k+1)+3
    · rw [if_pos h']
      have hle : (j+1 : ℝ) ≤ 4*(k+1)+3 := by exact_mod_cast (show j+1 ≤ 4*(k+1)+3 by omega)
      have hi := (inv_le_inv₀ (by positivity : 0 < Real.sqrt (4*(k+1)+3 : ℝ))
        (by positivity : 0 < Real.sqrt (j+1 : ℝ))).mpr (Real.sqrt_le_sqrt hle)
      push_cast
      linarith
    · rw [if_neg h']; simp

/-- The sampled reciprocal tail, including its exact material-edge condition. -/
theorem baseTwoSampledHardy_tail (j N : ℕ) :
    (∑ k ∈ Finset.range N,
      if j < 4*k+3 then ((4*k+3 : ℝ) * Real.sqrt (4*k+3 : ℝ))⁻¹ else 0) ≤
      2 * (Real.sqrt (j+1 : ℝ))⁻¹ := by
  have ht : (∑ k ∈ Finset.range N,
      if j < 4*k+3 then ((4*k+3 : ℝ) * Real.sqrt (4*k+3 : ℝ))⁻¹ else 0) ≤
      2 * (tailPotential j 0 - tailPotential j N) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hs := sampled_tail_step j N
      linarith
  have hn : 0 ≤ tailPotential j N := by unfold tailPotential; split <;> positivity
  have h0 : tailPotential j 0 ≤ (Real.sqrt (j+1 : ℝ))⁻¹ := by
    unfold tailPotential
    split
    · rename_i h
      have hj : (j+1 : ℝ) ≤ 3 := by exact_mod_cast (show j+1 ≤ 3 by omega)
      simpa using (inv_le_inv₀ (by positivity : 0 < Real.sqrt (3 : ℝ))
        (by positivity : 0 < Real.sqrt (j+1 : ℝ))).mpr (Real.sqrt_le_sqrt hj)
    · exact le_rfl
  linarith

private theorem normalized_prefix (g : ℕ → ℂ) (m : ℕ) (hm : 0 < m) :
    ‖∑ j ∈ Finset.range m, g j‖^2 / (m : ℝ)^2 ≤
      2 * ((m : ℝ) * Real.sqrt (m : ℝ))⁻¹ *
        ∑ j ∈ Finset.range m, Real.sqrt (j+1 : ℝ) * ‖g j‖^2 := by
  have hp : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hp
  have he : 2 * ((m : ℝ) * Real.sqrt (m : ℝ))⁻¹ *
      (∑ j ∈ Finset.range m, Real.sqrt (j+1 : ℝ) * ‖g j‖^2) * (m : ℝ)^2 =
      2 * Real.sqrt (m : ℝ) *
      (∑ j ∈ Finset.range m, Real.sqrt (j+1 : ℝ) * ‖g j‖^2) := by
    have hh := Real.sq_sqrt hp.le
    field_simp
    rw [hh]
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  rw [he]
  exact weighted_prefix g m

/-- Uniform Hardy bound only at the geometric cutoffs `4*k+3`. -/
theorem baseTwoSampledHardy_finite (g : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      ‖∑ j ∈ Finset.range (4*k+3), g j‖^2 / (4*k+3 : ℝ)^2) ≤
      4 * ∑ j ∈ Finset.range (4*N+3), ‖g j‖^2 := by
  let w : ℕ → ℝ := fun j => Real.sqrt (j+1 : ℝ) * ‖g j‖^2
  let a : ℕ → ℝ := fun k => ((4*k+3 : ℝ) * Real.sqrt (4*k+3 : ℝ))⁻¹
  have hs (k : ℕ) (hk : k ∈ Finset.range N) :
      ∑ j ∈ Finset.range (4*k+3), w j =
      ∑ j ∈ Finset.range (4*N+3), if j < 4*k+3 then w j else 0 := by
    have hsub : Finset.range (4*k+3) ⊆ Finset.range (4*N+3) :=
      Finset.range_mono (by have := Finset.mem_range.mp hk; omega)
    symm
    calc
      _ = ∑ j ∈ Finset.range (4*k+3), if j < 4*k+3 then w j else 0 :=
        (Finset.sum_subset hsub (fun j _ hj => by simp [Finset.mem_range] at hj; simp [hj])).symm
      _ = _ := Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))
  calc
    _ ≤ ∑ k ∈ Finset.range N, 2 * a k * ∑ j ∈ Finset.range (4*k+3), w j := by
      apply Finset.sum_le_sum
      intro k _
      simpa [a,w] using normalized_prefix g (4*k+3) (by omega)
    _ = ∑ j ∈ Finset.range (4*N+3),
        2 * w j * ∑ k ∈ Finset.range N, if j < 4*k+3 then a k else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun k hk => by
        rw [← Finset.mul_sum, hs k hk, Finset.mul_sum])]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      split <;> simp_all
      ring
    _ ≤ ∑ j ∈ Finset.range (4*N+3), 4 * ‖g j‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      have hj := mul_le_mul_of_nonneg_left (baseTwoSampledHardy_tail j N)
        (show 0 ≤ 2*w j by dsimp [w]; positivity)
      have hp : Real.sqrt (j+1 : ℝ) ≠ 0 := ne_of_gt (by positivity)
      simpa [a,w, mul_assoc, mul_left_comm, mul_comm, hp, show (2:ℝ)*2=4 by norm_num] using hj
    _ = _ := (Finset.mul_sum ..).symm

end GeometryOfNumbers.Analysis.BaseTwoCompletion
