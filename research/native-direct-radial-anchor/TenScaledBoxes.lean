import ScaledResidual
import TenTrial
import EightCritical

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryCriticalRadialMargin CarryIntegralCertificate CarryVariationalSchur
open CarrySummableRadial
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

def scaleInt : Fin 4 → ℤ := ![10000,1000000,100000000,10000000000]
def scaleReal (i : Fin 4) : ℝ := scaleInt i

def oldMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 4

def trialSolve : Fin 4 → ℝ := fun i => -trialCoefficient i.val

def oldResidual : Fin 4 → ℝ :=
  sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 4 trialSolve

def scaledMatrix : Matrix (Fin 4) (Fin 4) ℝ := scaledOldMatrix scaleReal oldMatrix

def scaledResidual : Fin 4 → ℝ := Matrix.diagonal scaleReal *ᵥ oldResidual

def entryBox (i j : Fin 4) : Box :=
  (Box.point (scaleInt i*scaleInt j)).mul (sourceMomentBox (i.val+j.val+1))

def residualBox (i : Fin 4) : Box :=
  (Box.point (scaleInt i)).mul ((sourceMomentBox (i.val+5)).add
    (Box.sum (fun j => (trialCoefficientBox j).mul (sourceMomentBox (i.val+j+1))) 4))

theorem scale_ne_zero (i : Fin 4) : scaleReal i ≠ 0 := by
  fin_cases i <;> norm_num [scaleReal,scaleInt]

theorem entry_box_mem (i j : Fin 4) : (entryBox i j).Mem (scaledMatrix i j) := by
  have hn : 1 ≤ i.val+j.val+1 ∧ i.val+j.val+1 ≤ 9 := by omega
  have h := mem_mul (mem_point (scaleInt i*scaleInt j))
    (ten_moment_box_mem (i.val+j.val+1) hn.1 hn.2)
  convert h using 1
  · rfl
  · simp [scaledMatrix,scaledOldMatrix,Matrix.mul_diagonal,Matrix.diagonal_mul,oldMatrix,
      sourceMomentMatrix,scaleReal]
    ring

theorem residual_box_mem (i : Fin 4) : (residualBox i).Mem (scaledResidual i) := by
  have hs := mem_sum (fun j => (trialCoefficientBox j).mul (sourceMomentBox (i.val+j+1)))
    (fun j => trialCoefficient j*canonicalCompletedNativeLogDerivativeMoment (i.val+j+1)) 4
    (by
      intro j hj
      exact mem_mul (trial_coefficient_box_mem j (by omega))
        (ten_moment_box_mem (i.val+j+1) (by omega) (by omega)))
  have hb := ten_moment_box_mem (i.val+5) (by omega) (by omega)
  have h := mem_mul (mem_point (scaleInt i)) (mem_add hb hs)
  convert h using 1
  · rfl
  · fin_cases i <;>
      norm_num [scaledResidual,oldResidual,sourceTrialResidual,oldMatrix,sourceMomentCoupling,
        sourceMomentMatrix,Matrix.mulVec,dotProduct,Matrix.diagonal,trialSolve,scaleReal,scaleInt,
        Fin.sum_univ_succ,Finset.sum_range_succ,Finset.sum_range_zero] <;> ring

def minorBox (i j : Fin 4) : Box := det3Box
  (entryBox (i.succAbove 0) (j.succAbove 0)) (entryBox (i.succAbove 0) (j.succAbove 1)) (entryBox (i.succAbove 0) (j.succAbove 2))
  (entryBox (i.succAbove 1) (j.succAbove 0)) (entryBox (i.succAbove 1) (j.succAbove 1)) (entryBox (i.succAbove 1) (j.succAbove 2))
  (entryBox (i.succAbove 2) (j.succAbove 0)) (entryBox (i.succAbove 2) (j.succAbove 1)) (entryBox (i.succAbove 2) (j.succAbove 2))

theorem minor_box_mem (i j : Fin 4) : (minorBox i j).Mem
    ((scaledMatrix.submatrix i.succAbove j.succAbove).det) := by
  have h := det3_box_mem
    (entry_box_mem (i.succAbove 0) (j.succAbove 0)) (entry_box_mem (i.succAbove 0) (j.succAbove 1)) (entry_box_mem (i.succAbove 0) (j.succAbove 2))
    (entry_box_mem (i.succAbove 1) (j.succAbove 0)) (entry_box_mem (i.succAbove 1) (j.succAbove 1)) (entry_box_mem (i.succAbove 1) (j.succAbove 2))
    (entry_box_mem (i.succAbove 2) (j.succAbove 0)) (entry_box_mem (i.succAbove 2) (j.succAbove 1)) (entry_box_mem (i.succAbove 2) (j.succAbove 2))
  convert h using 1
  · rfl
  · rw [Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply,det3]
    ring

def adjBox (i j : Fin 4) : Box :=
  if (i.val+j.val)%2=0 then minorBox j i else (minorBox j i).neg

theorem adj_box_mem (i j : Fin 4) : (adjBox i j).Mem (scaledMatrix.adjugate i j) := by
  have hm := minor_box_mem j i
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j <;> norm_num [adjBox] <;>
    first | simpa using hm | simpa using mem_neg hm

end
end CarryDirectAnchor
