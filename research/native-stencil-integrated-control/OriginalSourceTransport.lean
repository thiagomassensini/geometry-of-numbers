import OddPairBridge
import OddFiniteEnergy

namespace CarryCenteredStirling
open CarrySelfAdjointOperator CarrySpatialCorrection CarryOddEnergy CarryEnergyCorrection
open CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary NativeLaguerre CarryCommutatorControl
open Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def lambdaCoefficient (m n : ℕ) : ℂ :=
  ((m:ℂ)+1)*((m:ℂ)+2)*(2*(m:ℂ)+3)/12 +
  ((n:ℂ)+1)*((n:ℂ)+2)*(2*(n:ℂ)+3)/12 +
  ((((m:ℂ)+1)*((m:ℂ)+2)/2)-(((n:ℂ)+1)*((n:ℂ)+2)/2))^2/2

/-- The previously transported coefficient is literally the Lambda of the
new centered combinatorial derivation, for both indices arbitrary. -/
theorem existing_spatial_coefficient_eq_lambda (m n : ℕ) :
    spatialCorrection m n=lambdaCoefficient m n := by
  unfold spatialCorrection curvature CarrySpatialCorrection.slope lambdaCoefficient
  ring

/-- The complete two-input native pair, with both phases and the original
analytic tail, has the Lambda first correction in every odd order. -/
theorem original_odd_pair_expansion_lambda (r s : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      normalizedOddPair r s k=(h (r+s+1):ℂ)-(radialStep k:ℂ)^2*
        lambdaCoefficient (2*r+1) (2*s+1)*(h (r+s+2):ℂ)+(radialStep k:ℂ)^4*
          oddPairKernel (remainderSamples (r+s+3) (radialStep k)) r s := by
  filter_upwards [normalized_odd_pair_expansion r s] with k hk
  rw [existing_spatial_coefficient_eq_lambda] at hk
  exact hk

/-- Arbitrary finite combinations of original jets retain all the ordered
crosses in the full signed physical energy; no sign is assumed. -/
theorem original_finite_odd_energy_correction_lambda (S : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (fullEnergy k (finiteOddJetSource S c k)-oddCanonicalForm S c)) atTop
      (nhds (∑ r ∈ S, ∑ s ∈ S, -(c r*c s)*
        (lambdaCoefficient (2*r+1) (2*s+1)).re*h (r+s+2))) := by
  have he : oddCanonicalCorrection S c =
      ∑ r ∈ S, ∑ s ∈ S, -(c r*c s)*(lambdaCoefficient (2*r+1) (2*s+1)).re*h (r+s+2) := by
    unfold oddCanonicalCorrection
    simp only [existing_spatial_coefficient_eq_lambda]
  rw [← he]
  exact finite_odd_energy_correction_tendsto S c


/-- The coefficient in the original two-leg Cauchy stencil is the very
same Lambda appearing in the completed physical pair expansion. -/
theorem original_stencil_coefficient_eq_lambda (r s : ℕ) :
    stencilPair (2*r+1) (2*s+1) ((2*r+1)+(2*s+1)+3) =
      -lambdaCoefficient (2*r+1) (2*s+1) := by
  simpa only [lambdaCoefficient] using odd_stencil_correction_all_order r s


def lambdaReal (m n : ℕ) : ℝ :=
  ((m:ℝ)+1)*((m:ℝ)+2)*(2*(m:ℝ)+3)/12 +
  ((n:ℝ)+1)*((n:ℝ)+2)*(2*(n:ℝ)+3)/12 +
  ((((m:ℝ)+1)*((m:ℝ)+2)/2)-(((n:ℝ)+1)*((n:ℝ)+2)/2))^2/2

/-- Each geometric coefficient is strictly positive; the sign of the full
critical quadratic combination still depends on its mixed coefficients. -/
theorem lambda_real_positive (m n : ℕ) : 0 < lambdaReal m n := by
  unfold lambdaReal
  positivity

theorem lambda_complex_eq_real (m n : ℕ) :
    lambdaCoefficient m n=(lambdaReal m n:ℂ) := by
  unfold lambdaCoefficient lambdaReal
  push_cast
  ring


/-- Strictly positive individual coefficients do not make their matrix
positive: the mixed crossing gives a negative quadratic direction. -/
theorem lambda_crossing_negative :
    lambdaReal 1 1 - 2*lambdaReal 1 3 + lambdaReal 3 3 = -49 ∧
      lambdaReal 1 1 - 2*lambdaReal 1 3 + lambdaReal 3 3 < 0 := by
  norm_num [lambdaReal]

end
end CarryCenteredStirling
