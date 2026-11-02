import SourceRate
import NativeRepartition64

namespace CarryUniformSource
open CarrySourceBezout CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

def c3TailRadius (r : ℕ) : ℝ :=
  (96*(Nat.factorial 14:ℝ)/(729*191^13))*(4:ℝ)^(4*r)

theorem c3TailRadius_nonneg (r : ℕ) : 0 ≤ c3TailRadius r := by
  unfold c3TailRadius
  positivity

theorem c3_regrouped_tail_bound_order (r k : ℕ) (hk : k ≤ 2*r) :
    ‖regroupedTail64 k‖ ≤ c3TailRadius r := by
  rw [regrouped_tail64_jet]
  have h := CarryC3Tail.completed_tail_jet_error (2*k)
  have hk2 : 2*k ≤ 4*r := by omega
  have hp : (4:ℝ)^(2*k) ≤ (4:ℝ)^(4*r) := by
    gcongr
    norm_num
  unfold c3TailRadius
  exact h.trans (mul_le_mul_of_nonneg_left hp (by positivity))

theorem c3_regrouped_head_bound_order (r k : ℕ) (hk : k ≤ 2*r) :
    ‖regroupedHead64 k‖ ≤ sourceCoefficientMass r + c3TailRadius r := by
  have he : regroupedHead64 k = (nativeC k:ℂ)-regroupedTail64 k := by
    have hh := regrouped_source k
    linear_combination hh
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (sourceCoefficient_le_mass r k hk)
    (c3_regrouped_tail_bound_order r k hk))

/-- The already certified original C3 boundary yields an all-finite-order
explicit rational tail scale. It does not prove any positivity sign. -/
theorem c3_original_boundary_explicit_order_rate (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
      coefficientPair regroupedHead64 regroupedHead64 b r x y‖ ≤
      (4*(r:ℝ)^2*(2*sourceCoefficientMass r*c3TailRadius r +
        3*(c3TailRadius r)^2))*coordMass x*coordMass y := by
  have hρ := c3TailRadius_nonneg r
  have hA := sourceCoefficientMass_nonneg r
  have hh : ∀ k ≤ 2*r, ‖repHead 64 (originalBoundaryJet 64) k‖ ≤ sourceCoefficientMass r+c3TailRadius r := by
    intro k hk
    exact c3_regrouped_head_bound_order r k hk
  have ht : ∀ k ≤ 2*r, ‖repTail 64 (originalBoundaryJet 64) k‖ ≤ c3TailRadius r := by
    intro k hk
    exact c3_regrouped_tail_bound_order r k hk
  have he := repartition_explicit_order_bound 64 64 (originalBoundaryJet 64) (originalBoundaryJet 64) b r
    (sourceCoefficientMass r+c3TailRadius r) (c3TailRadius r)
    (sourceCoefficientMass r+c3TailRadius r) (c3TailRadius r)
    (add_nonneg hA hρ) hρ (add_nonneg hA hρ) hρ hh ht hh ht x y
  change ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
      coefficientPair regroupedHead64 regroupedHead64 b r x y‖ ≤ _ at he
  convert he using 1
  ring

theorem c3_critical_explicit_order_rate (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    |(nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) n -
      (coefficientPair regroupedHead64 regroupedHead64 b (n+1)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)).re| ≤
      (4*((n+1:ℕ):ℝ)^2*(2*sourceCoefficientMass (n+1)*c3TailRadius (n+1) +
        3*(c3TailRadius (n+1))^2))*
        (coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) n))^2 := by
  let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) n
  have he := c3_original_boundary_explicit_order_rate b (n+1) z z
  rw [native_monicSourceDirection_remainder b n hA,nativeSourceSchurRemainder_eq] at he
  have hr := (Complex.abs_re_le_norm
    (((nativeC 0 * (nativeC 0 * sourceMomentSchur nativeH (if b then 1 else 0) n) : ℝ):ℂ) -
      coefficientPair regroupedHead64 regroupedHead64 b (n+1) z z)).trans he
  simpa [Complex.sub_re,Complex.ofReal_re,pow_two,mul_assoc] using hr

#print axioms c3_original_boundary_explicit_order_rate
#print axioms c3_critical_explicit_order_rate
end
end CarryUniformSource
