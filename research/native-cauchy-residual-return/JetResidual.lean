import ResidualReturn
import SchurLimit

namespace CarryCauchyResidual
open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare
open Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false

/-- Extracted ONLY AFTER the complete original jet synthesis input has
been formed, including its amplitudes, phases and forward differences. -/
def jetTailCoefficients (n k : ℕ) (x : Fin (2*(n+1)) → ℂ) : Fin (2*n+1) → ℂ :=
  tailCoefficients (nativeSourceChiralJetInput (n+1) k x)

def reducedJetIncident (n k : ℕ) (x : Fin (2*(n+1)) → ℂ) : Physical :=
  tailSynthesis k (2*n+1) (incidentCoordinates k (2*n+1) (jetTailCoefficients n k x))
def reducedJetReturned (n k : ℕ) (x : Fin (2*(n+1)) → ℂ) : Physical :=
  tailSynthesis k (2*n+1) (returnedCoordinates k (2*n+1) (jetTailCoefficients n k x))
def reducedJetPair (n k : ℕ) (x y : Fin (2*(n+1)) → ℂ) : ℂ :=
  inner ℂ (reducedJetIncident n k x) (reducedJetIncident n k y)-
    inner ℂ (reducedJetReturned n k x) (reducedJetReturned n k y)

/-- Same full polarized physical residual as PR52, now with BOTH channels
expressed on the unchanged Cauchy tail frame. -/
theorem reducedJetPair_exact (n k : ℕ) (x y : Fin (2*(n+1)) → ℂ) :
    reducedJetPair n k x y = jetRemainingPair (n+1) k x y := by
  exact (residual_full_source k (2*n+1)
    (nativeSourceChiralJetInput (n+1) k x) (nativeSourceChiralJetInput (n+1) k y)).symm

theorem reducedJetPair_canonical_schur_limit (n : ℕ) (x y : Fin (2*(n+1)) → ℂ) :
    Tendsto (fun k => reducedJetPair n k x y/(oneDeficit k:ℂ)) atTop
      (nhds (2*(canonicalBoundaryPair (n+1) x y-
        conj (canonicalBoundaryPair (n+1) (headBoundary n) x)*
          canonicalBoundaryPair (n+1) (headBoundary n) y/
          (canonicalCompletedNativeLogDerivativeMoment 0:ℂ)))) := by
  simpa only [reducedJetPair_exact, jetSchurRemainder] using jet_remaining_schur_tendsto n x y

end
end CarryCauchyResidual
