import JetBudget
import Mathlib.Analysis.Matrix.Order

/-! A positive part obtained by EXACT cancellation of the two old camera
terms. The remaining variable defect is kept, with no sign assumption. -/
namespace CarryJetOverlap
open CarrySelfAdjointOperator CarryFiberTransport ChiralReturn CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
set_option autoImplicit false

/-- The old ambient responses, not states constructed from a moment matrix. -/
def ambientMatrix (k N : ℕ) (hs : strip k N) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ
    (ambientReadout (fiberPart (nativeSource (radialPoint k i) (hs i))))
    (ambientReadout (fiberPart (nativeSource (radialPoint k j) (hs j))))

theorem ambientMatrix_eq_kernel (k N : ℕ) (hs : strip k N) (i j : Fin N) :
    ambientMatrix k N hs i j=canonicalCompletedC3AmbientResponseKernel
      (radialPoint k i) (radialPoint k j) (hs i).1 (hs j).1 := rfl

def overlapMatrix (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => radialOverlap k i j

theorem overlapMatrix_eq_gram (k N : ℕ) :
    overlapMatrix k N=Matrix.gram ℂ (fun i : Fin N => observedCauchy k i) := by
  ext i j
  exact radialOverlap_inner k i j

theorem overlapMatrix_posSemidef (k N : ℕ) : (overlapMatrix k N).PosSemidef := by
  rw [overlapMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℂ _

theorem ambientMatrix_posSemidef (k N : ℕ) (hs : strip k N) :
    (ambientMatrix k N hs).PosSemidef := by
  change (Matrix.gram ℂ (fun i : Fin N =>
    ambientReadout (fiberPart (nativeSource (radialPoint k i) (hs i))))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- This Hadamard product is determined by two existing physical Grams. -/
def dampedCameraMatrix (k N : ℕ) (hs : strip k N) : Matrix (Fin N) (Fin N) ℂ :=
  (overlapMatrix k N).hadamard (ambientMatrix k N hs)

theorem dampedCameraMatrix_posSemidef (k N : ℕ) (hs : strip k N) :
    (dampedCameraMatrix k N hs).PosSemidef :=
  (overlapMatrix_posSemidef k N).hadamard (ambientMatrix_posSemidef k N hs)

/-- Sesquilinear evaluation uses the literal original source weights. -/
def dampedCameraBalance (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (hs : strip k N) : ℂ :=
  ∑ i, ∑ j, conj (sourceWeight k c i)*sourceWeight k d j*
    (dampedCameraMatrix k N hs i j)

theorem ambientMatrix_eq_camera (k N : ℕ) (hs : strip k N) (i j : Fin N) :
    ambientMatrix k N hs i j=inner ℂ
      (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter (radialPoint k i)) (hs i).1))
      (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter (radialPoint k j)) (hs j).1)) := by
  exact (inner_completedC3SymplecticCameraState_eq_ambientResponseKernel
    (radialPoint k i) (radialPoint k j) (hs i).1 (hs j).1).symm

theorem camera_pairing_eq_ambient_sum (k : ℕ) {N : ℕ} (c d : Fin N → ℂ)
    (hs : strip k N) :
    inner ℂ (coisometricSourceSynthesis k c 1 (fun i => (hs i).1))
      (coisometricSourceSynthesis k d 1 (fun i => (hs i).1))=
      ∑ i, ∑ j, conj (sourceWeight k c i)*sourceWeight k d j*ambientMatrix k N hs i j := by
  unfold coisometricSourceSynthesis
  simp only [Complex.ofReal_one,one_pow,mul_one]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_left,inner_smul_right,ambientMatrix_eq_camera]
  unfold sourceWeight
  ring

/-- Exact cancellation, not deletion: G-(1-O)G=OG, with BOTH sums intact. -/
theorem camera_sub_overlap_eq_damped (k : ℕ) {N : ℕ} (c d : Fin N → ℂ)
    (hs : strip k N) :
    inner ℂ (coisometricSourceSynthesis k c 1 (fun i => (hs i).1))
      (coisometricSourceSynthesis k d 1 (fun i => (hs i).1))-
        overlapCorrection k c d hs=dampedCameraBalance k c d hs := by
  rw [camera_pairing_eq_ambient_sum]
  unfold overlapCorrection dampedCameraBalance dampedCameraMatrix overlapMatrix
  simp only [Matrix.hadamard_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change conj (sourceWeight k c i)*sourceWeight k d j*ambientMatrix k N hs i j-
    conj (sourceWeight k c i)*sourceWeight k d j*
      ((1-radialOverlap k i j)*ambientMatrix k N hs i j)=_
  ring

/-- The complete original jet form is positive physical part PLUS the
computed variable defect. Its last term has not acquired a sign. -/
theorem jetBudget_eq_damped_add_defect (n k : ℕ) (x y : Fin (2*n) → ℂ)
    (hs : strip k (2*n)) :
    jetBudget n k x y hs=
      dampedCameraBalance k (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y) hs+
      variableDefect k (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y) hs := by
  rw [← camera_sub_overlap_eq_damped]
  unfold jetBudget
  ring

theorem dampedCameraBalance_self_nonneg (k : ℕ) {N : ℕ} (c : Fin N → ℂ)
    (hs : strip k N) : 0 ≤ (dampedCameraBalance k c c hs).re := by
  have h := (dampedCameraMatrix_posSemidef k N hs).dotProduct_mulVec_nonneg
    (sourceWeight k c)
  have he : star (sourceWeight k c) ⬝ᵥ
      (dampedCameraMatrix k N hs).mulVec (sourceWeight k c)=
        dampedCameraBalance k c c hs := by
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum,dampedCameraBalance]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [starRingEnd_apply]
    ring
  rw [he] at h
  exact (Complex.nonneg_iff.mp h).1

end
end CarryJetOverlap
