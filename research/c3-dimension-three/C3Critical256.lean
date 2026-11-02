import CriticalBoxes

namespace CarryC3DimensionThree
open CarryUniformSource CarrySourceBezout CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

/-- The original C3 head differs from the native critical Schur residual by
at most the certified sum of all three crossed tail terms. The old determinant
and the critical vector bound are obtained from existing theta integral boxes;
no sign of the new pivot is assumed. -/
theorem c3_256_critical_error_unconditional (b : Bool) :
    |(nativeC 0)^2 * sourceMomentSchur nativeH (if b then 1 else 0) 2 -
      (coefficientPair (c3Head 256) (c3Head 256) b 3
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)).re| ≤ (3/10^18:ℝ) :=
  c3_256_critical_error b (oldMatrix_isUnit b) (critical_coordMass_bound b)

/-- The only remaining sign input is the original finite C3 head, not an
assumption about the Schur pivot. -/
theorem c3_256_positive_from_head (b : Bool)
    (hhead : (3/10^18:ℝ) <
      (coefficientPair (c3Head 256) (c3Head 256) b 3
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)
        (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2)).re) :
    0 < sourceMomentSchur nativeH (if b then 1 else 0) 2 :=
  c3_256_critical_positive_of_head b (oldMatrix_isUnit b) (critical_coordMass_bound b) hhead

#print axioms c3_256_critical_error_unconditional
#print axioms c3_256_positive_from_head
end
end CarryC3DimensionThree
