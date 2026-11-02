import C3Critical256

namespace CarryC3DimensionThree
open CarryUniformSource CarrySourceBezout CarrySelfAdjointOperator CarryIntegralCertificate Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 65536

def pivotBox (s : ℕ) : Box :=
  (((logMomentBox (s+2)).mul (v0Box s)).add ((logMomentBox (s+3)).mul (v1Box s))).add (logMomentBox (s+4))
def scaledPivotBox (s : ℕ) : Box := ((characteristicBox 0).pow 2).mul (pivotBox s)

theorem pivot_expression (s : ℕ) (hA : IsUnit (sourceMomentMatrix nativeH s 2)) :
    sourceMomentSchur nativeH s 2 =
      nativeH (s+2)*criticalV0 s + nativeH (s+3)*criticalV1 s + nativeH (s+4) := by
  have hr := criticalVector_mulVec nativeH s 2 hA
  rw [critical_vector_explicit s hA] at hr
  have h := congrFun hr (2 : Fin 3)
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,sourceMomentMatrix, Nat.add_comm] at h
  have hl : (Fin.snoc (0 : Fin 2 → ℝ) (sourceMomentSchur nativeH s 2) : Fin 3 → ℝ) 2 = sourceMomentSchur nativeH s 2 := by
    change (Fin.snoc (0 : Fin 2 → ℝ) _ : Fin 3 → ℝ) (Fin.last 2) = _
    exact Fin.snoc_last _ _
  rw [hl] at h
  linarith

theorem pivotMem (s : ℕ) (hA : IsUnit (sourceMomentMatrix nativeH s 2)) :
    (pivotBox s).Mem (sourceMomentSchur nativeH s 2) := by
  rw [pivot_expression s hA]
  exact mem_add (mem_add (mem_mul (hMem (s+2)) (v0Mem s))
    (mem_mul (hMem (s+3)) (v1Mem s))) (hMem (s+4))

theorem scaledPivotMem (b : Bool) :
    (scaledPivotBox (if b then 1 else 0)).Mem
      ((nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) 2) :=
  mem_mul (mem_pow (cMem 0) 2) (pivotMem _ (oldMatrix_isUnit b))

/-- The sign input below comes from independent source coefficient boxes;
no theorem asserting a pivot sign is used. -/
theorem sourcePair_gt_six (b : Bool) :
    (6/10^18 : ℝ) < matrixPair (coefficientBlock (sourceKernel nativeC b) 3)
      (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)
      (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2) := by
  have h := mem_add (scaledPivotMem b) (mem_neg (mem_rat 6 (10^18)))
  have hp : ((scaledPivotBox (if b then 1 else 0)).add (Box.rat 6 (10^18)).neg).positive = true := by
    cases b <;> decide +kernel
  have ht := pos_of_mem h hp
  rw [native_monicSourceDirection_remainder b 2 (oldMatrix_isUnit b), nativeSourceSchurRemainder_eq]
  nlinarith

theorem sourceHead_gt_three (b : Bool) :
    (3/10^18:ℝ) < (coefficientPair (c3Head 256) (c3Head 256) b 3
      (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)
      (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)).re := by
  let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) 2
  have hs := sourcePair_gt_six b
  have he := c3_256_three_uniform_error b z z (critical_coordMass_bound b) (critical_coordMass_bound b)
  have hr := (Complex.abs_re_le_norm
    (((matrixPair (coefficientBlock (sourceKernel nativeC b) 3) z z : ℝ):ℂ) -
      coefficientPair (c3Head 256) (c3Head 256) b 3 z z)).trans he
  simp only [Complex.sub_re, Complex.ofReal_re, abs_le] at hr
  linarith [hr.2]

theorem pivot_positive_from_certified_boxes (b : Bool) :
    0 < sourceMomentSchur nativeH (if b then 1 else 0) 2 :=
  c3_256_positive_from_head b (sourceHead_gt_three b)

#print axioms pivot_expression
#print axioms sourcePair_gt_six
#print axioms sourceHead_gt_three
#print axioms pivot_positive_from_certified_boxes
end
end CarryC3DimensionThree
