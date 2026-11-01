import GeometryOfNumbers.Analysis

open GeometryOfNumbers.Analysis
open GeometryOfNumbers.Analysis.BaseTwoCompletion

noncomputable section

namespace CanonicalNativeBoundaryTransfer

/-- The canonical completion does define a genuine log-derivative moment sequence. -/
theorem canonicalMomentSequence_isLogDerivativeMoment :
    IsLogDerivativeMomentSequence
      (GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalPhi)
      (GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalLogMoment) :=
  GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalLogMoment_isSequence

/-- The leading canonical coefficient is strictly positive. This is the concrete finite
certificate that survives in the package; it is not a claim of all-order positivity. -/
theorem canonicalMomentZero_isPositive :
    0 < GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalPhi 0 :=
  GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalPhi_zero_pos

/-- The canonical completion at order zero is nonzero. -/
theorem canonicalMomentZero_isNonzero :
    GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalPhi 0 ≠ 0 :=
  GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalPhi_zero_ne_zero

end CanonicalNativeBoundaryTransfer
