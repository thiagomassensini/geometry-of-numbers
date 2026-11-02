import C3Tail256

namespace CarryC3DimensionThree
open CarryUniformSource CarrySourceBezout CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Original C3 source with all three crossed tail terms. The bound holds
for every pair of real vectors in the stated coefficient balls. -/
theorem c3_256_three_uniform_error (b : Bool) (x y : Fin 3 → ℝ)
    (hx : coordMass x ≤ 2) (hy : coordMass y ≤ 2) :
    ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) 3) x y : ℂ) -
      coefficientPair (c3Head 256) (c3Head 256) b 3 x y‖ ≤ (3/10^18:ℝ) := by
  have hh : ∀ k ≤ 2*3, ‖repHead 256 (originalBoundaryJet 256) k‖ ≤ (1:ℝ) := by
    intro k hk
    exact c3Head256_six_bound k hk
  have ht : ∀ k ≤ 2*3, ‖repTail 256 (originalBoundaryJet 256) k‖ ≤ (1/10^20:ℝ) := by
    intro k hk
    exact c3Tail256_six_bound k hk
  have he := repartition_explicit_order_bound 256 256 (originalBoundaryJet 256)
    (originalBoundaryJet 256) b 3 1 (1/10^20) 1 (1/10^20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh ht hh ht x y
  change ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) 3) x y : ℂ) -
      coefficientPair (c3Head 256) (c3Head 256) b 3 x y‖ ≤ _ at he
  have hm : coordMass x * coordMass y ≤ 4 :=
    (mul_le_mul hx hy (coordMass_nonneg y) (by norm_num : (0:ℝ)≤2)).trans_eq (by norm_num)
  norm_num at he ⊢
  nlinarith

/-- Transport to the identical critical source: the only premises are old
prefix invertibility and the stated coefficient-size bound. -/
theorem c3_256_critical_error (b : Bool)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) 2))
    (hz : coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2) ≤ 2) :
    |(nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) 2 -
      (coefficientPair (c3Head 256) (c3Head 256) b 3
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)).re| ≤ (3/10^18:ℝ) := by
  let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) 2
  have he := c3_256_three_uniform_error b z z hz hz
  rw [native_monicSourceDirection_remainder b 2 hA,nativeSourceSchurRemainder_eq] at he
  have hr := (Complex.abs_re_le_norm
    (((nativeC 0 * (nativeC 0 * sourceMomentSchur nativeH (if b then 1 else 0) 2) : ℝ):ℂ) -
      coefficientPair (c3Head 256) (c3Head 256) b 3 z z)).trans he
  simpa [Complex.sub_re,Complex.ofReal_re,pow_two,mul_assoc] using hr

theorem c3_256_critical_positive_of_head (b : Bool)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) 2))
    (hz : coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2) ≤ 2)
    (hhead : (3/10^18:ℝ) <
      (coefficientPair (c3Head 256) (c3Head 256) b 3
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)).re) :
    0 < sourceMomentSchur nativeH (if b then 1 else 0) 2 := by
  have he := (abs_le.mp (c3_256_critical_error b hA hz)).1
  have hp : 0 < (nativeC 0)^2*sourceMomentSchur nativeH (if b then 1 else 0) 2 := by linarith
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero)).mp hp

#print axioms c3_256_three_uniform_error
#print axioms c3_256_critical_error
#print axioms c3_256_critical_positive_of_head
end
end CarryC3DimensionThree
