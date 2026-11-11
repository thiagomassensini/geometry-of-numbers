import Repartition
import SchurThreshold

namespace CarrySourceBezout
open CarrySelfAdjointOperator
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false

/-- The exact coefficient normalization inherited from the completed literal
TFVD jet. The equality is in `ℂ` before taking real parts. -/
theorem nativeC_coefficient_eq_literal_head_tail (M m : ℕ) :
    nativeC m = (literalHead M m).re + (literalTail M m).re := by
  have h := congrFun (literal_head_tail M) m
  have hr := congrArg Complex.re h
  simpa using hr

/-- The last-coefficient determinant law transported exactly to the original
head and tail jets. Both summands retain their original real projections. -/
theorem nativeSource_borderedDet_literal_head_tail (M n : ℕ) (b : Bool) :
    (coefficientBlock (sourceKernel nativeC b) (n+1)).det =
      sourceBezoutLastCoefficientRemainderDet nativeC b n -
        (sourceBoundaryCoefficientIndex n b : ℝ) * nativeC 0 *
          (coefficientBlock (sourceKernel nativeC b) n).det *
            (literalHead M (sourceBoundaryCoefficientIndex n b)).re -
        (sourceBoundaryCoefficientIndex n b : ℝ) * nativeC 0 *
          (coefficientBlock (sourceKernel nativeC b) n).det *
            (literalTail M (sourceBoundaryCoefficientIndex n b)).re := by
  have hdet := sourceBezout_borderedDet_lastCoefficient_exact nativeC n b
  rw [nativeC_coefficient_eq_literal_head_tail M
    (sourceBoundaryCoefficientIndex n b)] at hdet
  calc
    _ = _ := hdet
    _ = _ := by ring

/-- Abstract coefficient-level compensation rule. A strict head margin exceeding
the full tail error forces the affine determinant expression to be positive. -/
theorem sourceBoundary_compensation_sufficient
    (m c₀ D J head tail ε : ℝ)
    (hm : 0 < m) (hc₀ : 0 < c₀) (hD : 0 < D) (hε : 0 ≤ ε)
    (htail : |tail| ≤ ε)
    (hhead : J - m*c₀*D*head > m*c₀*D*ε) :
    0 < J - m*c₀*D*head - m*c₀*D*tail := by
  have hfactor : 0 ≤ m*c₀*D := by positivity
  have htailUpper : tail ≤ ε := (abs_le.mp htail).2
  have hmul := mul_le_mul_of_nonneg_left htailUpper hfactor
  have hcostNonneg := mul_nonneg hfactor hε
  nlinarith [hmul, hcostNonneg]

/-- Sufficient condition for the original source determinant, using only the
original literal tail bound and the exact head coefficient. The hypotheses
expose the still-open geometric head margin. -/
theorem nativeSource_borderedDet_pos_of_boundary_margin
    (M n : ℕ) (b : Bool) (ε : ℝ)
    (hc₀ : 0 < nativeC 0)
    (hD : 0 < (coefficientBlock (sourceKernel nativeC b) n).det)
    (hε : 0 ≤ ε)
    (htail : |(literalTail M (sourceBoundaryCoefficientIndex n b)).re| ≤ ε)
    (hhead :
      sourceBezoutLastCoefficientRemainderDet nativeC b n -
        (sourceBoundaryCoefficientIndex n b : ℝ) * nativeC 0 *
          (coefficientBlock (sourceKernel nativeC b) n).det *
            (literalHead M (sourceBoundaryCoefficientIndex n b)).re >
        (sourceBoundaryCoefficientIndex n b : ℝ) * nativeC 0 *
          (coefficientBlock (sourceKernel nativeC b) n).det * ε) :
    0 < (coefficientBlock (sourceKernel nativeC b) (n+1)).det := by
  have hmNat : 0 < sourceBoundaryCoefficientIndex n b := by
    cases b <;> simp [sourceBoundaryCoefficientIndex]
  have hm : 0 < (sourceBoundaryCoefficientIndex n b : ℝ) := by exact_mod_cast hmNat
  have hcomp := sourceBoundary_compensation_sufficient
    (sourceBoundaryCoefficientIndex n b : ℝ) (nativeC 0)
    ((coefficientBlock (sourceKernel nativeC b) n).det)
    (sourceBezoutLastCoefficientRemainderDet nativeC b n)
    ((literalHead M (sourceBoundaryCoefficientIndex n b)).re)
    ((literalTail M (sourceBoundaryCoefficientIndex n b)).re) ε hm hc₀ hD hε htail hhead
  rw [nativeSource_borderedDet_literal_head_tail]
  exact hcomp

/-- Exact residual crosswalk retaining two independent TFVD cutoffs, all four
ordered crossings, the original complex bilinear pairing, and the boundary
repartition. This is an identity; it asserts no sign. -/
theorem native_residual_four_terms_boundary_repartition
    (M P : ℕ) (U V : ℕ → ℂ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    let z := monicSourceDirection nativeC nativeH (if b then 1 else 0) n
    coefficientPair (literalHead M) (literalHead P) b (n+1) z z +
      coefficientPair (literalHead M) (literalTail P) b (n+1) z z +
      coefficientPair (literalTail M) (literalHead P) b (n+1) z z +
      coefficientPair (literalTail M) (literalTail P) b (n+1) z z =
    (nativeC 0*nativeSourceSchurRemainder (if b then 1 else 0) n : ℝ) := by
  dsimp only
  calc
    _ = coefficientPair (literalHead M+U) (literalHead P+V) b (n+1) _ _ +
          coefficientPair (literalHead M+U) (literalTail P-V) b (n+1) _ _ +
          coefficientPair (literalTail M-U) (literalHead P+V) b (n+1) _ _ +
          coefficientPair (literalTail M-U) (literalTail P-V) b (n+1) _ _ := by
        exact coefficientPair_boundary_repartition
          (literalHead M) (literalTail M) (literalHead P) (literalTail P) U V b (n+1) _ _
    _ = _ := native_residual_repartition M P U V b n hA

#print axioms nativeC_coefficient_eq_literal_head_tail
#print axioms nativeSource_borderedDet_literal_head_tail
#print axioms sourceBoundary_compensation_sufficient
#print axioms nativeSource_borderedDet_pos_of_boundary_margin
#print axioms native_residual_four_terms_boundary_repartition

end
end CarrySourceBezout
