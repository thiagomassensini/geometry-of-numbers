import C3LinearSupport

/-!
Linear source jet response: the two crossed terms HT + TH form a
genuine linear functional of the ONE shared tail, not two independent
absolute error estimates.
-/
namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000

theorem responseCoefficient_scale (z : ℂ) (c : ℕ → ℂ) (b : Bool)
    (k : ℕ) :
    responseCoefficient (fun t => z * c t) b k =
      z * responseCoefficient c b k := by
  cases b with
  | true =>
    rw [response_odd_explicit, response_odd_explicit]
    ring
  | false =>
    cases k with
    | zero =>
      simp [response_even_zero]
    | succ k =>
      rw [response_even_succ, response_even_succ]
      ring

theorem mixed_kernel_scale_left (z : ℂ) (c d : ℕ → ℂ)
    (b : Bool) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i
       (mixedSourceKernel (fun t => z*c t) d b)) =
      z * PowerSeries.coeff j (PowerSeries.coeff i (mixedSourceKernel c d b)) := by
  rw [mixed_kernel_coefficient, mixed_kernel_coefficient]
  simp only [responseCoefficient_scale]
  calc
    (∑ k ∈ Finset.range (j+1),
        d (j-k) * (z * responseCoefficient c b (i+k+1))) -
      ∑ k ∈ Finset.range (j+1),
        (z * responseCoefficient c b (j-k)) * d (i+k+1) =
      (∑ k ∈ Finset.range (j+1),
        z * (d (j-k) * responseCoefficient c b (i+k+1))) -
      ∑ k ∈ Finset.range (j+1),
        z * (responseCoefficient c b (j-k) * d (i+k+1)) := by
          congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]; ring

theorem mixed_kernel_scale_right (z : ℂ) (c d : ℕ → ℂ)
    (b : Bool) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i
       (mixedSourceKernel c (fun t => z*d t) b)) =
      z * PowerSeries.coeff j (PowerSeries.coeff i (mixedSourceKernel c d b)) := by
  rw [mixed_kernel_coefficient, mixed_kernel_coefficient]
  calc
    (∑ k ∈ Finset.range (j+1),
        (z*d (j-k)) * responseCoefficient c b (i+k+1)) -
      ∑ k ∈ Finset.range (j+1),
        responseCoefficient c b (j-k) * (z*d (i+k+1)) =
      (∑ k ∈ Finset.range (j+1),
        z * (d (j-k) * responseCoefficient c b (i+k+1))) -
      ∑ k ∈ Finset.range (j+1),
        z * (responseCoefficient c b (j-k) * d (i+k+1)) := by
          congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]; ring


theorem coefficientPair_scale_left (z : ℂ) (c d : ℕ → ℂ)
    (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    coefficientPair (fun t => z*c t) d b r x y =
      z * coefficientPair c d b r x y := by
  have he : coefficientBlock (mixedSourceKernel (fun t => z*c t) d b) r =
      z • coefficientBlock (mixedSourceKernel c d b) r := by
    ext i j
    simpa [coefficientBlock, Matrix.smul_apply, smul_eq_mul] using
      mixed_kernel_scale_left z c d b i.val j.val
  unfold coefficientPair
  rw [he]
  simp [complexPair, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem coefficientPair_scale_right (z : ℂ) (c d : ℕ → ℂ)
    (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    coefficientPair c (fun t => z*d t) b r x y =
      z * coefficientPair c d b r x y := by
  have he : coefficientBlock (mixedSourceKernel c (fun t => z*d t) b) r =
      z • coefficientBlock (mixedSourceKernel c d b) r := by
    ext i j
    simpa [coefficientBlock, Matrix.smul_apply, smul_eq_mul] using
      mixed_kernel_scale_right z c d b i.val j.val
  unfold coefficientPair
  rw [he]
  simp [complexPair, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

end
end CarrySourceBezout
