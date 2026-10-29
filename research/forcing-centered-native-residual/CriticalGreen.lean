import ForcingCenter
import ResidualTest
import JetResidual

namespace CarryForcingResidual
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator NativeMomentOrthogonalization
open CarryMaterialMixedSchurComparison CarryReturnDeflation CarryCauchyResidual
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
local notation "h" => canonicalCompletedNativeLogDerivativeMoment

/-- Confluent observations of the SAME source residual in PR37. These
are signed bilinear forms; no higher Hilbert-valued jet or Gram is asserted. -/
def greenPolynomialForm (s : Fin 2) (N : ℕ) (a b : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, carryMaterialResidualJet (2*i.val+s.val) (2*j.val+s.val)*a i*b j
def centralMean {N : ℕ} (a : Fin N → ℝ) : ℝ := ∑ i, a i*h i

theorem centralMean_functional {N : ℕ} (a : Fin N → ℝ) :
    centralMean a = momentFunctional h (coefficientPolynomial a) := by
  simp [centralMean, coefficientPolynomial]

/-- Full polarized even-sector pullback, with the exact central Schur
subtraction retained. No sign or nondegeneracy hypothesis. -/
theorem green_even_bilinear (N : ℕ) (a b : Fin N → ℝ) :
    greenPolynomialForm 0 N a b = momentForm h (coefficientPolynomial a) (coefficientPolynomial b)-
      centralMean a*centralMean b/h 0 := by
  have hm : centralMean a*centralMean b/h 0 =
      ∑ i : Fin N, ∑ j : Fin N, (h i*h j/h 0)*a i*b j := by
    unfold centralMean
    rw [Finset.sum_mul, Finset.sum_div]
    simp_rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [momentForm_coefficients, hm]
  simp only [greenPolynomialForm, Fin.val_zero, Nat.add_zero,
    material_residual_jet_even_even, carryPairingBilinear]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem green_odd_bilinear (N : ℕ) (a b : Fin N → ℝ) :
    greenPolynomialForm 1 N a b =
      momentForm (fun k => h (k+1)) (coefficientPolynomial a) (coefficientPolynomial b) := by
  rw [momentForm_coefficients]
  simp only [greenPolynomialForm, Fin.val_one, material_residual_jet_odd_odd,
    carryPairingBilinear]

def criticalCoefficients (s : Fin 2) (n : ℕ) : Fin (n+1) → ℝ :=
  fun i => (orthogonalPolynomial (fun k => h (k+s.val)) n).coeff i

theorem criticalPolynomial_exact (s : Fin 2) (n : ℕ) :
    coefficientPolynomial (criticalCoefficients s n) =
      orthogonalPolynomial (fun k => h (k+s.val)) n :=
  orthogonalPolynomial_from_coefficients _ _

theorem exact_even_centralMean_zero (n : ℕ) (hn : 0 < n)
    (hp : ∀ r < n, carryPairingPivot (hankelPairing h) r ≠ 0) :
    centralMean (criticalCoefficients 0 n) = 0 := by
  rw [centralMean_functional, criticalPolynomial_exact]
  change momentFunctional h (orthogonalPolynomial h n) = 0
  have hh := orthogonalPolynomial_orthogonal h n hp 0 hn
  have hz : orthogonalPolynomial h 0 = 1 := by simp [orthogonalPolynomial, residualPolynomial]
  rw [hz] at hh
  simpa only [momentForm, one_mul] using hh

theorem exact_even_green_residual (n : ℕ) (hn : 0 < n)
    (hp : ∀ r < n, carryPairingPivot (hankelPairing h) r ≠ 0) :
    greenPolynomialForm 0 (n+1) (criticalCoefficients 0 n) (criticalCoefficients 0 n) =
      carryPairingPivot (hankelPairing h) n := by
  rw [green_even_bilinear, exact_even_centralMean_zero n hn hp]
  rw [zero_mul, zero_div, sub_zero, criticalPolynomial_exact]
  exact orthogonalPolynomial_self h n

theorem exact_odd_green_residual (n : ℕ) :
    greenPolynomialForm 1 (n+1) (criticalCoefficients 1 n) (criticalCoefficients 1 n) =
      carryPairingPivot (hankelPairing (fun k => h (k+1))) n := by
  rw [green_odd_bilinear]
  rw [criticalPolynomial_exact]
  exact orthogonalPolynomial_self _ n

/-- Native boundary coefficients are exactly PR41's, not a trial column. -/
theorem even_green_boundary_energy (n : ℕ) (hn : 0 < n)
    (hp : ∀ r < n, carryPairingPivot (hankelPairing h) r ≠ 0) :
    nativeSourceFiniteBoundaryEnergy (2*(n+1)) (nativeResidualBoundary 0 n) =
      4*greenPolynomialForm 0 (n+1) (criticalCoefficients 0 n) (criticalCoefficients 0 n) := by
  rw [exact_even_green_residual n hn hp, nativeResidualBoundary_energy]
  rfl

theorem odd_green_boundary_energy (n : ℕ) :
    nativeSourceFiniteBoundaryEnergy (2*(n+1)) (nativeResidualBoundary 1 n) =
      4*greenPolynomialForm 1 (n+1) (criticalCoefficients 1 n) (criticalCoefficients 1 n) := by
  rw [exact_odd_green_residual, nativeResidualBoundary_energy]
  rfl

/-- The physical Cauchy comparison of PR53 reaches the very same Green
residual. This identifies readouts; it does not assert an isometry between
the material and Cauchy carriers or manufacture a positive state. -/
theorem even_cauchy_green_limit (n : ℕ) (hn : 0 < n)
    (hp : ∀ r < n, carryPairingPivot (hankelPairing h) r ≠ 0) :
    Tendsto (fun k => (reducedJetPair n k (nativeResidualBoundary 0 n)
      (nativeResidualBoundary 0 n)/(CarryPositiveSquare.oneDeficit k:ℂ)).re) atTop
      (nhds (2*greenPolynomialForm 0 (n+1) (criticalCoefficients 0 n) (criticalCoefficients 0 n))) := by
  rw [exact_even_green_residual n hn hp]
  simpa only [reducedJetPair_exact, jetSchurRemainder] using pr41_even_remaining_energy_tendsto n hn hp

theorem odd_cauchy_green_limit (n : ℕ) :
    Tendsto (fun k => (reducedJetPair n k (nativeResidualBoundary 1 n)
      (nativeResidualBoundary 1 n)/(CarryPositiveSquare.oneDeficit k:ℂ)).re) atTop
      (nhds (2*greenPolynomialForm 1 (n+1) (criticalCoefficients 1 n) (criticalCoefficients 1 n))) := by
  rw [exact_odd_green_residual]
  simpa only [reducedJetPair_exact, jetSchurRemainder] using pr41_odd_remaining_energy_tendsto n

end
end CarryForcingResidual
