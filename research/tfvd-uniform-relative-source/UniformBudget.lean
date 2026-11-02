import LiteralBudgetLimit

namespace CarryUniformSource
open CarrySourceBezout CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def coordMass {r : ℕ} (x : Fin r → ℝ) : ℝ := ∑ i, |x i|

theorem coordMass_nonneg {r : ℕ} (x : Fin r → ℝ) : 0 ≤ coordMass x := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem abs_le_coordMass {r : ℕ} (x : Fin r → ℝ) (i : Fin r) : |x i| ≤ coordMass x := by
  unfold coordMass
  exact Finset.single_le_sum (f := fun j : Fin r => |x j|) (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

theorem directionalBudget_normed (c d : ℕ → ℂ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    directionalBudget c d b r x y ≤
      directionalBudget c d b r (fun _ => 1) (fun _ => 1) * coordMass x * coordMass y := by
  simp only [directionalBudget, abs_one, one_mul, mul_one, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hc := coefficientBudget_nonneg c d b i.val j.val
  have hx := abs_le_coordMass x i
  have hy := abs_le_coordMass y j
  have hxy : |x i| * |y j| ≤ coordMass x * coordMass y :=
    mul_le_mul hx hy (abs_nonneg _) (coordMass_nonneg x)
  have hh := mul_le_mul_of_nonneg_left hxy hc
  nlinarith

def normalizedError (M P : ℕ) (b : Bool) (r : ℕ) : ℝ :=
  literalErrorBudget M P b r (fun _ => 1) (fun _ => 1)

theorem normalizedError_nonneg (M P : ℕ) (b : Bool) (r : ℕ) : 0 ≤ normalizedError M P b r := by
  unfold normalizedError literalErrorBudget
  exact add_nonneg (add_nonneg (directionalBudget_nonneg _ _ _ _ _ _)
    (directionalBudget_nonneg _ _ _ _ _ _)) (directionalBudget_nonneg _ _ _ _ _ _)

theorem literalErrorBudget_normed (M P : ℕ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    literalErrorBudget M P b r x y ≤ normalizedError M P b r * coordMass x * coordMass y := by
  unfold normalizedError literalErrorBudget
  have h1 := directionalBudget_normed (literalHead M) (literalTail P) b r x y
  have h2 := directionalBudget_normed (literalTail M) (literalHead P) b r x y
  have h3 := directionalBudget_normed (literalTail M) (literalTail P) b r x y
  nlinarith

theorem normalizedError_tendsto_zero (b : Bool) (r : ℕ) :
    Tendsto (fun M => normalizedError M M b r) atTop (𝓝 0) :=
  literal_error_budget_tendsto_zero b r (fun _ => 1) (fun _ => 1)

theorem original_kernel_relative_bound (M P : ℕ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
      literalTerm M P true true b r x y‖ ≤ normalizedError M P b r * coordMass x * coordMass y :=
  (literal_error_bound M P b r x y).trans (literalErrorBudget_normed M P b r x y)

theorem original_kernel_uniform_approx (b : Bool) (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ x y : Fin r → ℝ,
      ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
        literalTerm M M true true b r x y‖ ≤ ε * coordMass x * coordMass y := by
  have he : ∀ᶠ M in atTop, normalizedError M M b r ≤ ε :=
    (normalizedError_tendsto_zero b r).eventually (Iic_mem_nhds hε)
  filter_upwards [he] with M hM
  intro x y
  exact (original_kernel_relative_bound M M b r x y).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM (coordMass_nonneg x)) (coordMass_nonneg y))

/-- The identical monic PR41/PR70 source direction; no sign or positive-prefix
hypothesis is used. The factor c0² is retained exactly. -/
theorem critical_source_error_bound (M P : ℕ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    |(nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) n -
      (literalResidualTerm M P true true b n).re| ≤
        normalizedError M P b (n+1) *
          (coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) n))^2 := by
  let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) n
  have he := original_kernel_relative_bound M P b (n+1) z z
  change ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) (n+1)) z z : ℂ) -
    literalResidualTerm M P true true b n‖ ≤ normalizedError M P b (n+1)*coordMass z*coordMass z at he
  rw [native_monicSourceDirection_remainder b n hA, nativeSourceSchurRemainder_eq] at he
  have hr := (Complex.abs_re_le_norm
    (((nativeC 0 * (nativeC 0 * sourceMomentSchur nativeH (if b then 1 else 0) n) : ℝ):ℂ) -
      literalResidualTerm M P true true b n)).trans he
  simpa [Complex.sub_re, Complex.ofReal_re, pow_two, mul_assoc] using hr

theorem critical_source_uniform_cutoff (b : Bool) (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    ∀ᶠ M : ℕ in atTop,
      |(nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) n -
        (literalResidualTerm M M true true b n).re| ≤
          ε * (coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) n))^2 := by
  have he : ∀ᶠ M in atTop, normalizedError M M b (n+1) ≤ ε :=
    (normalizedError_tendsto_zero b (n+1)).eventually (Iic_mem_nhds hε)
  filter_upwards [he] with M hM
  refine (critical_source_error_bound M M b n hA).trans ?_
  exact mul_le_mul_of_nonneg_right hM (sq_nonneg _)

/-- A source-only bounded-family gate. Its head estimate is a genuine
remaining obligation, not a theorem that the original head has this sign. -/
theorem critical_positive_of_uniform_head (M P : ℕ) (b : Bool) (n : ℕ) (R : ℝ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n))
    (hR : coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) n) ≤ R)
    (hhead : ∀ x : Fin (n+1) → ℝ, x (Fin.last n) = 1 → coordMass x ≤ R →
      normalizedError M P b (n+1) * R^2 < (literalTerm M P true true b (n+1) x x).re) :
    0 < sourceMomentSchur nativeH (if b then 1 else 0) n := by
  let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) n
  have hz : z (Fin.last n) = 1 := monicSourceDirection_last nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero (if b then 1 else 0) n
  have hm := hhead z hz hR
  have hn : 0 ≤ coordMass z := coordMass_nonneg z
  have hsq : (coordMass z)^2 ≤ R^2 := by nlinarith
  have hErr := mul_le_mul_of_nonneg_left hsq (normalizedError_nonneg M P b (n+1))
  have hBound := (abs_le.mp (critical_source_error_bound M P b n hA)).1
  have hprod : 0 < (nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) n := by
    change normalizedError M P b (n+1)*R^2 < (literalResidualTerm M P true true b n).re at hm
    nlinarith
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero)).mp hprod

#print axioms critical_positive_of_uniform_head

#print axioms critical_source_error_bound
#print axioms critical_source_uniform_cutoff

#print axioms original_kernel_relative_bound
#print axioms original_kernel_uniform_approx
end
end CarryUniformSource
