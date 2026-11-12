import GeneralCofactorIdentity
import SourceSchur

namespace C3GeneralCofactor

open CarrySourceBezout CarrySelfAdjointOperator
open scoped Matrix

noncomputable section
set_option autoImplicit false

private theorem normalizedCofactor_eq_snoc {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (hD : A.det ≠ 0) :
    A.det⁻¹ • cofactorVector A b = Fin.snoc (-(A⁻¹ *ᵥ b)) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [cofactorVector, hD]
  · simp [cofactorVector, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, mul_neg]

/-- The normalized transpose of the source convolution sends the cofactor
vector to the canonical monic direction of the Hankel block. -/
def transportedCofactor (c : ℕ → ℝ) (s : Bool) (n : ℕ) : Fin (n + 1) → ℝ :=
  let A := coefficientBlock (sourceKernel c s) n
  (c 0 * A.det)⁻¹ •
    ((convolutionMatrix c (n + 1)).transpose *ᵥ cofactorVector A (sourceCoupling c s n))

theorem transportedCofactor_eq_criticalVector (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (s : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if s then 1 else 0) n)) :
    transportedCofactor c s n = criticalVector h (if s then 1 else 0) n := by
  let A := coefficientBlock (sourceKernel c s) n
  let b := sourceCoupling c s n
  let T := (convolutionMatrix c (n + 1)).transpose
  have hD : A.det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp (source_prefix_isUnit c h hc hr s n hA) |>.ne_zero
  calc
    transportedCofactor c s n = (c 0)⁻¹ • (T *ᵥ (A.det⁻¹ • cofactorVector A b)) := by
      simp [transportedCofactor, A, b, T, Matrix.mulVec_smul, smul_smul, mul_comm]
    _ = (c 0)⁻¹ • (T *ᵥ sourceCritical c s n) := by
      rw [normalizedCofactor_eq_snoc A b hD]
      rfl
    _ = criticalVector h (if s then 1 else 0) n := by
      rw [← monicSourceDirection_eq_sourceCritical c h hc hr s n hA]
      simp only [monicSourceDirection, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc,
        one_smul]
      exact sourceDirection_transport c h hc _ n

theorem transportedCofactor_last (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (s : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if s then 1 else 0) n)) :
    transportedCofactor c s n (Fin.last n) = 1 := by
  rw [transportedCofactor_eq_criticalVector c h hc hr s n hA]
  simp [criticalVector]

theorem hankel_mulVec_transportedCofactor (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (s : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if s then 1 else 0) n)) :
    hankelMatrix h (if s then 1 else 0) (n + 1) *ᵥ transportedCofactor c s n =
      Fin.snoc 0 (sourceMomentSchur h (if s then 1 else 0) n) := by
  rw [transportedCofactor_eq_criticalVector c h hc hr s n hA, hankelMatrix_source]
  exact criticalVector_mulVec h _ n hA

theorem hankel_transportedCofactor_energy (c h : ℕ → ℝ) (hc : c 0 ≠ 0)
    (hr : SourceRecurrence c h) (s : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h (if s then 1 else 0) n)) :
    matrixPair (hankelMatrix h (if s then 1 else 0) (n + 1))
      (transportedCofactor c s n) (transportedCofactor c s n) =
      sourceMomentSchur h (if s then 1 else 0) n := by
  rw [transportedCofactor_eq_criticalVector c h hc hr s n hA, hankelMatrix_source,
    criticalVector_pair h _ n hA]
  simp [criticalVector]

theorem sourceMomentSchur_pos_of_block_posDef (h : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix h s n))
    (hH : (sourceMomentMatrix h s (n + 1)).PosDef) :
    0 < sourceMomentSchur h s n := by
  let v := criticalVector h s n
  have hv : v (Fin.last n) = 1 := by simp [v, criticalVector]
  have hv₀ : v ≠ 0 := by
    intro he
    rw [he] at hv
    norm_num at hv
  have hp := hH.dotProduct_mulVec_pos hv₀
  change 0 < matrixPair (sourceMomentMatrix h s (n + 1)) v (criticalVector h s n) at hp
  rwa [criticalVector_pair h s n hA, hv, one_mul] at hp

#print axioms sourceMomentSchur_pos_of_block_posDef
#print axioms transportedCofactor_eq_criticalVector
#print axioms transportedCofactor_last
#print axioms hankel_mulVec_transportedCofactor
#print axioms hankel_transportedCofactor_energy

end
end C3GeneralCofactor
