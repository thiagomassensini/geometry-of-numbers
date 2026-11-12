import C3Tail256
import TfvdBoundaryLaw

namespace CarrySourceBezout
open CarrySelfAdjointOperator CarryUniformSource CarryC3DimensionThree
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false

/-- Repartitioning by the original C3 boundary preserves the exact real
coefficient: `c3Head` and `c3Tail` are still the original source split. -/
theorem nativeC_coefficient_eq_c3_boundary_split (k : ℕ) :
    nativeC k = (c3Head 256 k).re + (c3Tail 256 k).re := by
  change nativeC k =
    (literalHead 256 k + originalBoundaryJet 256 k).re +
      (literalTail 256 k - originalBoundaryJet 256 k).re
  have h := nativeC_coefficient_eq_literal_head_tail 256 k
  simp only [Complex.add_re, Complex.sub_re]
  linarith [h]

/-- Exact third-direction determinant decomposition after the original C3
boundary is moved from tail to head. No coefficient is replaced by an interval
or by a theta-derived value. -/
theorem nativeSource_borderedDet_c3_boundary_split (n : ℕ) (b : Bool) :
    (coefficientBlock (sourceKernel nativeC b) (n+1)).det =
      sourceBezoutLastCoefficientRemainderDet nativeC b n -
        (sourceBoundaryCoefficientIndex n b : ℝ) * nativeC 0 *
          (coefficientBlock (sourceKernel nativeC b) n).det *
            (c3Head 256 (sourceBoundaryCoefficientIndex n b)).re -
        (sourceBoundaryCoefficientIndex n b : ℝ) * nativeC 0 *
          (coefficientBlock (sourceKernel nativeC b) n).det *
            (c3Tail 256 (sourceBoundaryCoefficientIndex n b)).re := by
  have hdet := sourceBezout_borderedDet_lastCoefficient_exact nativeC n b
  rw [nativeC_coefficient_eq_c3_boundary_split (sourceBoundaryCoefficientIndex n b)] at hdet
  calc
    _ = _ := hdet
    _ = _ := by ring

/-- The original C3/256 accelerated tail has a rigorous absolute coefficient
bound through the full index range required by both third-direction blocks. -/
theorem c3_original_tail_real_bound (k : ℕ) (hk : k ≤ 6) :
    |(c3Tail 256 k).re| ≤ (1/10^20:ℝ) := by
  exact (Complex.abs_re_le_norm _).trans (c3Tail256_six_bound k hk)

/-- Even third-direction source gate, conditional exactly on the remaining
head-margin inequality and the old prefix determinant. -/
theorem c3_even_third_determinant_positive_of_head_margin
    (hc₀ : 0 < nativeC 0)
    (hD : 0 < (coefficientBlock (sourceKernel nativeC false) 2).det)
    (hhead :
      sourceBezoutLastCoefficientRemainderDet nativeC false 2 -
        5*nativeC 0*(coefficientBlock (sourceKernel nativeC false) 2).det*
          (c3Head 256 5).re >
        5*nativeC 0*(coefficientBlock (sourceKernel nativeC false) 2).det*(1/10^20:ℝ)) :
    0 < (coefficientBlock (sourceKernel nativeC false) 3).det := by
  have hm : 0 < (5:ℝ) := by norm_num
  have htail := c3_original_tail_real_bound 5 (by norm_num)
  have hcomp := sourceBoundary_compensation_sufficient
    5 (nativeC 0) ((coefficientBlock (sourceKernel nativeC false) 2).det)
    (sourceBezoutLastCoefficientRemainderDet nativeC false 2)
    (c3Head 256 5).re (c3Tail 256 5).re (1/10^20)
    hm hc₀ hD (by norm_num) htail hhead
  have hdet := nativeSource_borderedDet_c3_boundary_split 2 false
  simpa [sourceBoundaryCoefficientIndex] using hdet ▸ hcomp

/-- Shifted third-direction source gate, conditional on its independent head
margin. The tail estimate is still the original C3 boundary estimate. -/
theorem c3_odd_third_determinant_positive_of_head_margin
    (hc₀ : 0 < nativeC 0)
    (hD : 0 < (coefficientBlock (sourceKernel nativeC true) 2).det)
    (hhead :
      sourceBezoutLastCoefficientRemainderDet nativeC true 2 -
        6*nativeC 0*(coefficientBlock (sourceKernel nativeC true) 2).det*
          (c3Head 256 6).re >
        6*nativeC 0*(coefficientBlock (sourceKernel nativeC true) 2).det*(1/10^20:ℝ)) :
    0 < (coefficientBlock (sourceKernel nativeC true) 3).det := by
  have hm : 0 < (6:ℝ) := by norm_num
  have htail := c3_original_tail_real_bound 6 (by norm_num)
  have hcomp := sourceBoundary_compensation_sufficient
    6 (nativeC 0) ((coefficientBlock (sourceKernel nativeC true) 2).det)
    (sourceBezoutLastCoefficientRemainderDet nativeC true 2)
    (c3Head 256 6).re (c3Tail 256 6).re (1/10^20)
    hm hc₀ hD (by norm_num) htail hhead
  have hdet := nativeSource_borderedDet_c3_boundary_split 2 true
  simpa [sourceBoundaryCoefficientIndex] using hdet ▸ hcomp

#print axioms nativeC_coefficient_eq_c3_boundary_split
#print axioms nativeSource_borderedDet_c3_boundary_split
#print axioms c3_original_tail_real_bound
#print axioms c3_even_third_determinant_positive_of_head_margin
#print axioms c3_odd_third_determinant_positive_of_head_margin

end
end CarrySourceBezout
