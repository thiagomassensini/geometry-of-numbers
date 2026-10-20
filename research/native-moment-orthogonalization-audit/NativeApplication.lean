import JacobiLogic
import PolynomialCoordinates
import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundaryStieltjesGate

namespace NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate
noncomputable section

/-- The real polarization with both original quadratures, after synthesis. -/
def complexMomentForm (h : ℕ → ℝ) {N : ℕ} (u v : Fin N → ℂ) : ℝ :=
  momentForm h (coefficientPolynomial (fun i => (u i).re))
      (coefficientPolynomial (fun i => (v i).re)) +
    momentForm h (coefficientPolynomial (fun i => (u i).im))
      (coefficientPolynomial (fun i => (v i).im))

theorem complexMomentForm_crossings (h : ℕ → ℝ) {N : ℕ} (u v : Fin N → ℂ) :
    complexMomentForm h u v =
      ∑ i : Fin N, ∑ j : Fin N, h (i + j) * (conj (u i) * v j).re := by
  simp only [complexMomentForm, momentForm_coefficients, carryPairingBilinear,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact application to the original completed source. This is an equality
of signed energies, not a positivity theorem or a newly chosen norm. -/
theorem native_boundary_polynomial_energy (n : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceFiniteBoundaryEnergy (2*n) x = 4 *
      (complexMomentForm canonicalCompletedNativeLogDerivativeMoment
        (nativeSourceEvenBoundaryPhase n x) (nativeSourceEvenBoundaryPhase n x) +
       complexMomentForm (fun k => canonicalCompletedNativeLogDerivativeMoment (k+1))
        (nativeSourceOddBoundaryPhase n x) (nativeSourceOddBoundaryPhase n x)) := by
  rw [nativeSourceFiniteBoundaryEnergy_even_split, primeDepthGeometricMoment_eq_canonical,
    complexMomentForm_crossings, complexMomentForm_crossings]

/-- The polynomial residual identity applies to the untouched native moments
in both sectors and at every order; no sign has been inserted. -/
theorem native_residual_self (s n : ℕ) :
    momentForm (fun k => canonicalCompletedNativeLogDerivativeMoment (k+s))
      (orthogonalPolynomial (fun k => canonicalCompletedNativeLogDerivativeMoment (k+s)) n)
      (orthogonalPolynomial (fun k => canonicalCompletedNativeLogDerivativeMoment (k+s)) n) =
    carryPairingPivot
      (hankelPairing (fun k => canonicalCompletedNativeLogDerivativeMoment (k+s))) n :=
  orthogonalPolynomial_self _ n

theorem complexMomentForm_ofReal (h : ℕ → ℝ) {N : ℕ} (u : Fin N → ℝ) :
    complexMomentForm h (fun i => (u i : ℂ)) (fun i => (u i : ℂ)) =
      momentForm h (coefficientPolynomial u) (coefficientPolynomial u) := by
  simp [complexMomentForm, coefficientPolynomial, momentForm]

@[simp] theorem complexMomentForm_zero (h : ℕ → ℝ) (N : ℕ) :
    complexMomentForm h (0 : Fin N → ℂ) 0 = 0 := by
  simp [complexMomentForm, coefficientPolynomial, momentForm]

theorem native_boundary_real_even (N : ℕ) (u : Fin N → ℝ) :
    nativeSourceFiniteBoundaryEnergy (2*N)
      (nativeSourceBoundaryFromParity N (fun i => (u i : ℂ)) 0) =
      4 * momentForm canonicalCompletedNativeLogDerivativeMoment
        (coefficientPolynomial u) (coefficientPolynomial u) := by
  rw [native_boundary_polynomial_energy, nativeSourceEvenBoundaryPhase_fromParity,
    nativeSourceOddBoundaryPhase_fromParity, complexMomentForm_ofReal,
    complexMomentForm_zero, add_zero]

theorem native_boundary_real_odd (N : ℕ) (u : Fin N → ℝ) :
    nativeSourceFiniteBoundaryEnergy (2*N)
      (nativeSourceBoundaryFromParity N 0 (fun i => (u i : ℂ))) =
      4 * momentForm (fun k => canonicalCompletedNativeLogDerivativeMoment (k+1))
        (coefficientPolynomial u) (coefficientPolynomial u) := by
  rw [native_boundary_polynomial_energy, nativeSourceEvenBoundaryPhase_fromParity,
    nativeSourceOddBoundaryPhase_fromParity, complexMomentForm_zero,
    complexMomentForm_ofReal, zero_add]

/-- Original boundary coordinates of the residual polynomial; the parity
map is the existing invertible signed reindexing, not a new physical source. -/
def nativeResidualBoundary (s : Fin 2) (n : ℕ) : Fin (2*(n+1)) → ℂ :=
  let h := fun k => canonicalCompletedNativeLogDerivativeMoment (k+s.val)
  let u : Fin (n+1) → ℂ := fun i => ((orthogonalPolynomial h n).coeff i : ℂ)
  if s = 0 then nativeSourceBoundaryFromParity (n+1) u 0
  else nativeSourceBoundaryFromParity (n+1) 0 u

/-- Exact signed energy on the same native boundary and same coefficients.
This locates the remaining sign; it does not identify it with a norm. -/
theorem nativeResidualBoundary_energy (s : Fin 2) (n : ℕ) :
    nativeSourceFiniteBoundaryEnergy (2*(n+1)) (nativeResidualBoundary s n) =
      4 * carryPairingPivot
        (hankelPairing (fun k => canonicalCompletedNativeLogDerivativeMoment (k+s.val))) n := by
  fin_cases s
  · change nativeSourceFiniteBoundaryEnergy (2*(n+1))
      (nativeSourceBoundaryFromParity (n+1)
        (fun i => ((orthogonalPolynomial canonicalCompletedNativeLogDerivativeMoment n).coeff i : ℂ)) 0) =
      4 * carryPairingPivot (hankelPairing canonicalCompletedNativeLogDerivativeMoment) n
    rw [native_boundary_real_even, orthogonalPolynomial_from_coefficients,
      orthogonalPolynomial_self]
  · change nativeSourceFiniteBoundaryEnergy (2*(n+1))
      (nativeSourceBoundaryFromParity (n+1) 0
        (fun i => ((orthogonalPolynomial (fun k => canonicalCompletedNativeLogDerivativeMoment (k+1)) n).coeff i : ℂ))) =
      4 * carryPairingPivot (hankelPairing (fun k => canonicalCompletedNativeLogDerivativeMoment (k+1))) n
    rw [native_boundary_real_odd, orthogonalPolynomial_from_coefficients,
      orthogonalPolynomial_self]

theorem native_shifted_transport_isSymm (N : ℕ) (B : Matrix (Fin N) (Fin N) ℝ) :
    (GeometryOfNumbers.Analysis.finiteJacobiTransport B
      (GeometryOfNumbers.Analysis.shiftedHankel canonicalCompletedNativeLogDerivativeMoment N)).IsSymm :=
  shifted_transport_isSymm _ N B

end
end NativeMomentOrthogonalization
