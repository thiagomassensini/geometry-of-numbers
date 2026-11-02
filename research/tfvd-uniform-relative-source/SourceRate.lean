import OrderBound

namespace CarryUniformSource
open CarrySourceBezout CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

def sourceCoefficientMass (r : ℕ) : ℝ := ∑ k ∈ Finset.range (2*r+1), |nativeC k|

theorem sourceCoefficientMass_nonneg (r : ℕ) : 0 ≤ sourceCoefficientMass r := by
  unfold sourceCoefficientMass
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem sourceCoefficient_le_mass (r k : ℕ) (hk : k ≤ 2*r) :
    ‖(nativeC k:ℂ)‖ ≤ sourceCoefficientMass r := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  unfold sourceCoefficientMass
  exact Finset.single_le_sum (f := fun j : ℕ => |nativeC j|)
    (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))

def sourceTailRadius (C : ℝ) (M r : ℕ) : ℝ :=
  (C / ((M:ℝ)+1)) * (16:ℝ)^(2*r)

/-- Existing original TFVD tail envelope, now uniform over all coefficients
needed by both sectors of an r-by-r source block. -/
theorem tail_bound_all_coefficients (C : ℝ) (hC : 0 < C)
    (henv : ∀ M n : ℕ, ‖literalTail M n‖ ≤ (C / ((M:ℝ)+1))*16^n)
    (M r k : ℕ) (hk : k ≤ 2*r) : ‖literalTail M k‖ ≤ sourceTailRadius C M r := by
  have hp : (16:ℝ)^k ≤ (16:ℝ)^(2*r) := by
    gcongr
    norm_num
  unfold sourceTailRadius
  exact (henv M k).trans (mul_le_mul_of_nonneg_left hp (by positivity))

theorem head_bound_all_coefficients (C : ℝ) (hC : 0 < C)
    (henv : ∀ M n : ℕ, ‖literalTail M n‖ ≤ (C / ((M:ℝ)+1))*16^n)
    (M r k : ℕ) (hk : k ≤ 2*r) :
    ‖literalHead M k‖ ≤ sourceCoefficientMass r + sourceTailRadius C M r := by
  have he : literalHead M k = (nativeC k:ℂ)-literalTail M k := by
    have hh := congrFun (literal_head_tail M) k
    simp only [Pi.add_apply] at hh
    linear_combination -hh
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (sourceCoefficient_le_mass r k hk)
    (tail_bound_all_coefficients C hC henv M r k hk))

/-- A single source-derived C works for all finite orders, sectors, cutoffs
and directions. This is a coefficient-relative tail bound, not a sign law. -/
theorem original_source_explicit_order_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ (M r : ℕ) (b : Bool) (x y : Fin r → ℝ),
      ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) -
        literalTerm M M true true b r x y‖ ≤
      (4*(r:ℝ)^2*(2*sourceCoefficientMass r*sourceTailRadius C M r +
        3*(sourceTailRadius C M r)^2))*coordMass x*coordMass y := by
  obtain ⟨C,hC,henv⟩ := literal_tail_jet_envelope
  refine ⟨C,hC,?_⟩
  intro M r b x y
  have hρ : 0 ≤ sourceTailRadius C M r := by unfold sourceTailRadius; positivity
  have hA : 0 ≤ sourceCoefficientMass r := sourceCoefficientMass_nonneg r
  have hh : ∀ k ≤ 2*r, ‖repHead M 0 k‖ ≤ sourceCoefficientMass r + sourceTailRadius C M r := by
    intro k hk
    simpa [repHead] using head_bound_all_coefficients C hC henv M r k hk
  have ht : ∀ k ≤ 2*r, ‖repTail M 0 k‖ ≤ sourceTailRadius C M r := by
    intro k hk
    simpa [repTail] using tail_bound_all_coefficients C hC henv M r k hk
  have he := repartition_explicit_order_bound M M 0 0 b r
    (sourceCoefficientMass r+sourceTailRadius C M r) (sourceTailRadius C M r)
    (sourceCoefficientMass r+sourceTailRadius C M r) (sourceTailRadius C M r)
    (add_nonneg hA hρ) hρ (add_nonneg hA hρ) hρ hh ht hh ht x y
  have hsrc : coefficientPair (repHead M 0) (repHead M 0) b r x y = literalTerm M M true true b r x y := by
    simp [repHead,coefficientPair,literalTerm]
  rw [hsrc] at he
  convert he using 1
  ring

/-- The same global C controls the monic Schur direction in every finite
order and either sector. The bound does not assert that the pivot is positive. -/
theorem critical_source_explicit_order_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ (M n : ℕ) (b : Bool),
      IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n) →
      |(nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) n -
        (literalResidualTerm M M true true b n).re| ≤
      (4*((n+1:ℕ):ℝ)^2*(2*sourceCoefficientMass (n+1)*sourceTailRadius C M (n+1) +
        3*(sourceTailRadius C M (n+1))^2)) *
        (coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) n))^2 := by
  obtain ⟨C,hC,hbound⟩ := original_source_explicit_order_rate
  refine ⟨C,hC,?_⟩
  intro M n b hA
  let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) n
  have he := hbound M (n+1) b z z
  change ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) (n+1)) z z : ℂ) -
    literalResidualTerm M M true true b n‖ ≤ _ at he
  rw [native_monicSourceDirection_remainder b n hA,nativeSourceSchurRemainder_eq] at he
  have hr := (Complex.abs_re_le_norm
    (((nativeC 0 * (nativeC 0 * sourceMomentSchur nativeH (if b then 1 else 0) n) : ℝ):ℂ) -
      literalResidualTerm M M true true b n)).trans he
  simpa [Complex.sub_re,Complex.ofReal_re,pow_two,mul_assoc] using hr

#print axioms critical_source_explicit_order_rate

#print axioms original_source_explicit_order_rate
end
end CarryUniformSource
