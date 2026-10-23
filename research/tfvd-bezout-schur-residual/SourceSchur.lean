import SchurTransport

namespace CarrySourceBezout
open CarrySelfAdjointOperator
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000

def sourceCoupling (c : ℕ → ℝ) (b : Bool) (n : ℕ) : Fin n → ℝ :=
  fun i => coefficientBlock (sourceKernel c b) (n+1) i.castSucc (Fin.last n)

/-- The ordinary Schur formula for the source-defined Bezout block itself. -/
def sourceSchur (c : ℕ → ℝ) (b : Bool) (n : ℕ) : ℝ :=
  coefficientBlock (sourceKernel c b) (n+1) (Fin.last n) (Fin.last n) -
    sourceCoupling c b n ⬝ᵥ ((coefficientBlock (sourceKernel c b) n)⁻¹ *ᵥ sourceCoupling c b n)

def sourceCritical (c : ℕ → ℝ) (b : Bool) (n : ℕ) : Fin (n+1) → ℝ :=
  Fin.snoc (-((coefficientBlock (sourceKernel c b) n)⁻¹ *ᵥ sourceCoupling c b n)) 1

theorem source_prefix_isUnit (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if b then 1 else 0) n)) :
    IsUnit (coefficientBlock (sourceKernel c b) n) := by
  have ht := convolutionMatrix_isUnit c hc n
  have htt : IsUnit (convolutionMatrix c n).transpose := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp ht
  rw [source_bezout_to_hankel_congruence c h hr, hankelMatrix_source]
  exact (ht.mul hA).mul htt

theorem source_block_transpose (c h : ℕ → ℝ) (hr : SourceRecurrence c h) (b : Bool) (r : ℕ) :
    (coefficientBlock (sourceKernel c b) r).transpose = coefficientBlock (sourceKernel c b) r := by
  have hh : (hankelMatrix h (if b then 1 else 0) r).transpose =
      hankelMatrix h (if b then 1 else 0) r := by
    ext i j
    simp [hankelMatrix, Nat.add_comm]
  rw [source_bezout_to_hankel_congruence c h hr,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hh]
  exact Matrix.mul_assoc _ _ _ |>.symm

theorem monicSourceDirection_eq_sourceCritical (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if b then 1 else 0) n)) :
    monicSourceDirection c h (if b then 1 else 0) n = sourceCritical c b n := by
  let z := monicSourceDirection c h (if b then 1 else 0) n
  let A := coefficientBlock (sourceKernel c b) n
  let d := sourceCoupling c b n
  have hz : z (Fin.last n) = 1 := monicSourceDirection_last c h hc _ n
  have hzrows (i : Fin n) :
      (coefficientBlock (sourceKernel c b) (n+1) *ᵥ z) i.castSucc = 0 := by
    have hh := monicSourceDirection_pair c h hc hr b n hA (Pi.single i.castSucc 1)
    simpa [matrixPair] using hh
  have ha : A *ᵥ Fin.init z = -d := by
    ext i
    have hh := hzrows i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hz, mul_one] at hh
    change (∑ j : Fin n, A i j * z j.castSucc) + d i = 0 at hh
    change (∑ j : Fin n, A i j * z j.castSucc) = -d i
    linarith
  have hi := source_prefix_isUnit c h hc hr b n hA
  letI := hi.invertible
  have he : Fin.init z = -(A⁻¹ *ᵥ d) := by
    have hv := congrArg (fun v : Fin n → ℝ => A⁻¹ *ᵥ v) ha
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec,
      Matrix.mulVec_neg] at hv
    exact hv
  change z = _
  rw [← Fin.snoc_init_self z, he, hz]
  rfl

theorem sourceSchur_eq_scaled (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if b then 1 else 0) n)) :
    sourceSchur c b n = c 0^2 * sourceMomentSchur h (if b then 1 else 0) n := by
  have hh := monicSourceDirection_pair c h hc hr b n hA (Pi.single (Fin.last n) 1)
  rw [monicSourceDirection_eq_sourceCritical c h hc hr b n hA] at hh
  simp only [matrixPair, single_dotProduct, one_mul, Pi.single_eq_same] at hh
  rw [sourceCritical] at hh
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, Pi.neg_apply, mul_one] at hh
  have hsym := source_block_transpose c h hr b (n+1)
  have hcros (i : Fin n) :
      coefficientBlock (sourceKernel c b) (n+1) (Fin.last n) i.castSucc = sourceCoupling c b n i := by
    exact congrFun (congrFun hsym i.castSucc) (Fin.last n)
  simp only [hcros, mul_neg, Finset.sum_neg_distrib] at hh
  change _ = c 0^2 * sourceMomentSchur h (if b then 1 else 0) n at hh
  rw [sourceSchur, dotProduct]
  simp only [Matrix.mulVec, dotProduct]
  linarith

/-- Exact c0 factor linking two DIFFERENT residual constructions. -/
theorem native_sourceSchur_remainder (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    sourceSchur nativeC b n = nativeC 0*nativeSourceSchurRemainder (if b then 1 else 0) n := by
  rw [sourceSchur_eq_scaled nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero native_source_recurrence b n hA,
    nativeSourceSchurRemainder_eq]
  ring

end
end CarrySourceBezout
