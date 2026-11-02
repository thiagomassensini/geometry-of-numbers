import UniformBudget
import Repartition

namespace CarryUniformSource
open CarrySourceBezout CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

def repHead (M : ℕ) (U : ℕ → ℂ) : ℕ → ℂ := literalHead M + U

def repTail (M : ℕ) (U : ℕ → ℂ) : ℕ → ℂ := literalTail M - U

def repError (M P : ℕ) (U V : ℕ → ℂ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) : ℝ :=
  directionalBudget (repHead M U) (repTail P V) b r x y +
  directionalBudget (repTail M U) (repHead P V) b r x y +
  directionalBudget (repTail M U) (repTail P V) b r x y

def repNormalizedError (M P : ℕ) (U V : ℕ → ℂ) (b : Bool) (r : ℕ) : ℝ :=
  repError M P U V b r (fun _ => 1) (fun _ => 1)

theorem repartition_original_four_terms (M P : ℕ) (U V : ℕ → ℂ)
    (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    (matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) =
      coefficientPair (repHead M U) (repHead P V) b r x y +
      coefficientPair (repHead M U) (repTail P V) b r x y +
      coefficientPair (repTail M U) (repHead P V) b r x y +
      coefficientPair (repTail M U) (repTail P V) b r x y := by
  calc
    _ = literalTerm M P true true b r x y + literalTerm M P true false b r x y +
      literalTerm M P false true b r x y + literalTerm M P false false b r x y :=
        literal_four_terms M P b r x y
    _ = _ := by
      simpa [literalTerm,coefficientPair,repHead,repTail] using
        coefficientPair_boundary_repartition (literalHead M) (literalTail M)
          (literalHead P) (literalTail P) U V b r x y

theorem repError_normed (M P : ℕ) (U V : ℕ → ℂ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    repError M P U V b r x y ≤ repNormalizedError M P U V b r * coordMass x * coordMass y := by
  unfold repNormalizedError repError
  have h1 := directionalBudget_normed (repHead M U) (repTail P V) b r x y
  have h2 := directionalBudget_normed (repTail M U) (repHead P V) b r x y
  have h3 := directionalBudget_normed (repTail M U) (repTail P V) b r x y
  nlinarith

theorem repartition_relative_bound (M P : ℕ) (U V : ℕ → ℂ)
    (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
      coefficientPair (repHead M U) (repHead P V) b r x y‖ ≤
        repNormalizedError M P U V b r * coordMass x * coordMass y := by
  have h1 := mixed_direction_bound (repHead M U) (repTail P V) b r x y
  have h2 := mixed_direction_bound (repTail M U) (repHead P V) b r x y
  have h3 := mixed_direction_bound (repTail M U) (repTail P V) b r x y
  have he : ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
      coefficientPair (repHead M U) (repHead P V) b r x y‖ ≤ repError M P U V b r x y := by
    rw [repartition_original_four_terms]
    rw [show coefficientPair (repHead M U) (repHead P V) b r x y +
      coefficientPair (repHead M U) (repTail P V) b r x y +
      coefficientPair (repTail M U) (repHead P V) b r x y +
      coefficientPair (repTail M U) (repTail P V) b r x y -
      coefficientPair (repHead M U) (repHead P V) b r x y =
      (coefficientPair (repHead M U) (repTail P V) b r x y +
       coefficientPair (repTail M U) (repHead P V) b r x y) +
       coefficientPair (repTail M U) (repTail P V) b r x y by ring]
    unfold repError
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
  exact he.trans (repError_normed M P U V b r x y)

theorem repNormalizedError_zero_boundary (M P : ℕ) (b : Bool) (r : ℕ) :
    repNormalizedError M P 0 0 b r = normalizedError M P b r := by
  simp [repNormalizedError,repError,repHead,repTail,normalizedError,literalErrorBudget]

theorem repNormalizedError_zero_tendsto (b : Bool) (r : ℕ) :
    Tendsto (fun M => repNormalizedError M M 0 0 b r) atTop (𝓝 0) := by
  simpa only [repNormalizedError_zero_boundary] using normalizedError_tendsto_zero b r

theorem repNormalizedError_nonneg (M P : ℕ) (U V : ℕ → ℂ) (b : Bool) (r : ℕ) :
    0 ≤ repNormalizedError M P U V b r := by
  unfold repNormalizedError repError
  exact add_nonneg (add_nonneg (directionalBudget_nonneg _ _ _ _ _ _)
    (directionalBudget_nonneg _ _ _ _ _ _)) (directionalBudget_nonneg _ _ _ _ _ _)

/-- The same PR41 critical direction and both independent PR70 boundaries. -/
theorem repartition_critical_error_bound (M P : ℕ) (U V : ℕ → ℂ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    |(nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) n -
      (coefficientPair (repHead M U) (repHead P V) b (n+1)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)).re| ≤
      repNormalizedError M P U V b (n+1) *
        (coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) n))^2 := by
  let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) n
  have he := repartition_relative_bound M P U V b (n+1) z z
  rw [native_monicSourceDirection_remainder b n hA,nativeSourceSchurRemainder_eq] at he
  have hr := (Complex.abs_re_le_norm
    (((nativeC 0 * (nativeC 0 * sourceMomentSchur nativeH (if b then 1 else 0) n) : ℝ):ℂ) -
      coefficientPair (repHead M U) (repHead P V) b (n+1) z z)).trans he
  simpa [Complex.sub_re, Complex.ofReal_re, pow_two, mul_assoc] using hr

/-- Sufficient source-only inequality on a bounded monic family. The head
estimate is an open obligation, not an asserted sign of the native source. -/
theorem critical_positive_of_repartition_head (M P : ℕ) (U V : ℕ → ℂ)
    (b : Bool) (n : ℕ) (R : ℝ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n))
    (hR : coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) n) ≤ R)
    (hhead : ∀ x : Fin (n+1) → ℝ, x (Fin.last n) = 1 → coordMass x ≤ R →
      repNormalizedError M P U V b (n+1) * R^2 <
        (coefficientPair (repHead M U) (repHead P V) b (n+1) x x).re) :
    0 < sourceMomentSchur nativeH (if b then 1 else 0) n := by
  let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) n
  have hz : z (Fin.last n) = 1 := monicSourceDirection_last nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero (if b then 1 else 0) n
  have hm := hhead z hz hR
  have hn : 0 ≤ coordMass z := coordMass_nonneg z
  have hsq : (coordMass z)^2 ≤ R^2 := by nlinarith
  have hErr := mul_le_mul_of_nonneg_left hsq (repNormalizedError_nonneg M P U V b (n+1))
  have hBound := (abs_le.mp (repartition_critical_error_bound M P U V b n hA)).1
  have hprod : 0 < (nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) n := by nlinarith
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero)).mp hprod

#print axioms repartition_critical_error_bound
#print axioms critical_positive_of_repartition_head

#print axioms repartition_original_four_terms
#print axioms repartition_relative_bound
#print axioms repNormalizedError_zero_tendsto
end
end CarryUniformSource
