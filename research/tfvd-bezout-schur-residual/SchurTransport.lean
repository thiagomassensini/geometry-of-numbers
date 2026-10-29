import SourceNative

namespace CarrySourceBezout
open CarrySelfAdjointOperator
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1600000

def matrixPair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ y)

theorem hankelMatrix_source (h : ℕ → ℝ) (s n : ℕ) :
    hankelMatrix h s n = sourceMomentMatrix h s n := by
  ext i j
  rfl

def criticalVector (h : ℕ → ℝ) (s n : ℕ) : Fin (n+1) → ℝ :=
  Fin.snoc (-((sourceMomentMatrix h s n)⁻¹ *ᵥ sourceMomentCoupling h s n)) 1

def sourceDirection (c h : ℕ → ℝ) (s n : ℕ) : Fin (n+1) → ℝ :=
  ((convolutionMatrix c (n+1)).transpose)⁻¹ *ᵥ criticalVector h s n

def monicSourceDirection (c h : ℕ → ℝ) (s n : ℕ) : Fin (n+1) → ℝ :=
  c 0 • sourceDirection c h s n

theorem convolutionMatrix_isUnit (c : ℕ → ℝ) (hc : c 0 ≠ 0) (r : ℕ) :
    IsUnit (convolutionMatrix c r) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [convolutionMatrix_det]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero r hc)

theorem sourceDirection_transport (c h : ℕ → ℝ) (hc : c 0 ≠ 0) (s n : ℕ) :
    (convolutionMatrix c (n+1)).transpose *ᵥ sourceDirection c h s n =
      criticalVector h s n := by
  have ht : IsUnit (convolutionMatrix c (n+1)).transpose := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (convolutionMatrix_isUnit c hc (n+1))
  letI := ht.invertible
  simp only [sourceDirection, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec]

theorem convolution_transpose_last (c : ℕ → ℝ) (n : ℕ) (y : Fin (n+1) → ℝ) :
    ((convolutionMatrix c (n+1)).transpose *ᵥ y) (Fin.last n) =
      c 0*y (Fin.last n) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, convolutionMatrix]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro b hb hne
    have hl : b.val < n := by
      have := b.isLt
      have hh : b.val ≠ n := by
        intro he
        apply hne
        exact Fin.ext he
      omega
    simp [show ¬n ≤ b.val by omega]
  · simp

theorem sourceDirection_last (c h : ℕ → ℝ) (hc : c 0 ≠ 0) (s n : ℕ) :
    sourceDirection c h s n (Fin.last n) = (c 0)⁻¹ := by
  have he := congrFun (sourceDirection_transport c h hc s n) (Fin.last n)
  rw [convolution_transpose_last] at he
  simp only [criticalVector, Fin.snoc_last] at he
  apply (mul_left_cancel₀ hc)
  rw [he, mul_inv_cancel₀ hc]

theorem monicSourceDirection_last (c h : ℕ → ℝ) (hc : c 0 ≠ 0) (s n : ℕ) :
    monicSourceDirection c h s n (Fin.last n) = 1 := by
  simp [monicSourceDirection, sourceDirection_last c h hc s n, hc]

theorem congruence_pair {n : ℕ} (A T : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    matrixPair (T*A*T.transpose) x y =
      matrixPair A (T.transpose *ᵥ x) (T.transpose *ᵥ y) := by
  unfold matrixPair
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_transpose]

theorem criticalVector_mulVec (h : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s n)) :
    sourceMomentMatrix h s (n+1) *ᵥ criticalVector h s n =
      Fin.snoc 0 (sourceMomentSchur h s n) := by
  let A := sourceMomentMatrix h s n
  let b := sourceMomentCoupling h s n
  let u := A⁻¹ *ᵥ b
  letI := hA.invertible
  have hv : A *ᵥ u = b := by
    dsimp [u, A]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
      criticalVector, Fin.snoc_castSucc, Fin.snoc_last, Pi.neg_apply,
      sourceMomentMatrix, Fin.val_last, Fin.val_castSucc, mul_one]
    change (∑ j : Fin n, h (n+j.val+s) * -u j) + h (n+n+s) = _
    simp only [sourceMomentSchur, sourceMomentCoupling, dotProduct]
    change _ = h (2*n+s) - ∑ j : Fin n, h (j.val+n+s)*u j
    rw [show n+n = 2*n by omega]
    simp [mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg, add_comm]
  · have hj := congrFun hv j
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
      criticalVector, Fin.snoc_castSucc, Fin.snoc_last, Pi.neg_apply,
      sourceMomentMatrix, Fin.val_castSucc, Fin.val_last, mul_one]
    change (∑ k : Fin n, h (j.val+k.val+s) * -u k) + h (j.val+n+s) = 0
    change (∑ k : Fin n, h (j.val+k.val+s) * u k) = h (j.val+n+s) at hj
    simp [mul_neg, Finset.sum_neg_distrib, hj]

theorem criticalVector_pair (h : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s n)) (x : Fin (n+1) → ℝ) :
    matrixPair (sourceMomentMatrix h s (n+1)) x (criticalVector h s n) =
      x (Fin.last n)*sourceMomentSchur h s n := by
  rw [matrixPair, criticalVector_mulVec h s n hA]
  simp [dotProduct, Fin.sum_univ_castSucc]

/-- Stationarity in every old direction, with its exact last-coordinate term. -/
theorem monicSourceDirection_pair (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if b then 1 else 0) n))
    (x : Fin (n+1) → ℝ) :
    matrixPair (coefficientBlock (sourceKernel c b) (n+1)) x
      (monicSourceDirection c h (if b then 1 else 0) n) =
      x (Fin.last n)*(c 0)^2 * sourceMomentSchur h (if b then 1 else 0) n := by
  rw [source_bezout_to_hankel_congruence c h hr, congruence_pair]
  simp only [monicSourceDirection, Matrix.mulVec_smul]
  rw [sourceDirection_transport c h hc]
  simp only [matrixPair, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  change c 0 * matrixPair (sourceMomentMatrix h (if b then 1 else 0) (n+1))
    ((convolutionMatrix c (n+1)).transpose *ᵥ x) (criticalVector h (if b then 1 else 0) n) = _
  rw [criticalVector_pair h _ n hA, convolution_transpose_last]
  ring

theorem sourceDirection_energy (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if b then 1 else 0) n)) :
    matrixPair (coefficientBlock (sourceKernel c b) (n+1))
      (sourceDirection c h (if b then 1 else 0) n)
      (sourceDirection c h (if b then 1 else 0) n) =
      sourceMomentSchur h (if b then 1 else 0) n := by
  rw [source_bezout_to_hankel_congruence c h hr, congruence_pair,
    sourceDirection_transport c h hc, hankelMatrix_source]
  have he := criticalVector_pair h (if b then 1 else 0) n hA
    (criticalVector h (if b then 1 else 0) n)
  simpa [criticalVector] using he

theorem monicSourceDirection_energy (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if b then 1 else 0) n)) :
    matrixPair (coefficientBlock (sourceKernel c b) (n+1))
      (monicSourceDirection c h (if b then 1 else 0) n)
      (monicSourceDirection c h (if b then 1 else 0) n) =
      (c 0)^2 * sourceMomentSchur h (if b then 1 else 0) n := by
  simp only [monicSourceDirection, matrixPair, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have he := sourceDirection_energy c h hc hr b n hA
  change _ = (c 0)^2 * _
  rw [show c 0 * (c 0 * (sourceDirection c h (if b then 1 else 0) n ⬝ᵥ
    (coefficientBlock (sourceKernel c b) (n+1) *ᵥ sourceDirection c h (if b then 1 else 0) n))) =
    c 0^2 * matrixPair (coefficientBlock (sourceKernel c b) (n+1))
      (sourceDirection c h (if b then 1 else 0) n)
      (sourceDirection c h (if b then 1 else 0) n) by simp [matrixPair]; ring]
  rw [he]

theorem native_sourceDirection_remainder (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    nativeC 0 * matrixPair (coefficientBlock (sourceKernel nativeC b) (n+1))
      (sourceDirection nativeC nativeH (if b then 1 else 0) n)
      (sourceDirection nativeC nativeH (if b then 1 else 0) n) =
      nativeSourceSchurRemainder (if b then 1 else 0) n := by
  rw [sourceDirection_energy nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero native_source_recurrence b n hA,
    nativeSourceSchurRemainder_eq]

theorem native_monicSourceDirection_remainder (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    matrixPair (coefficientBlock (sourceKernel nativeC b) (n+1))
      (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)
      (monicSourceDirection nativeC nativeH (if b then 1 else 0) n) =
      nativeC 0 * nativeSourceSchurRemainder (if b then 1 else 0) n := by
  rw [monicSourceDirection_energy nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero native_source_recurrence b n hA,
    nativeSourceSchurRemainder_eq]
  ring

end
end CarrySourceBezout
