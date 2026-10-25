import QuarticLimits
import SchurLogic

namespace CarryPolarizedFour
open CarryGreenFinitePart CarryInteriorGreen CarryRadialGreen CarrySelfAdjointOperator Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The existing functional of the ORIGINAL moments, with two independent
polynomials. No positive measure or Hilbert interpretation is assumed. -/
theorem moment_pairing_original_functional (m : ℕ → ℝ) (u v : Fin 3 → ℝ) :
    momentPairing m u v=NativeMomentOrthogonalization.momentForm m
      (NativeMomentOrthogonalization.coefficientPolynomial u)
      (NativeMomentOrthogonalization.coefficientPolynomial v) := by
  rw [NativeMomentOrthogonalization.momentForm_coefficients]
  unfold momentPairing GeometryOfNumbers.Analysis.carryPairingBilinear
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem moment_pairing_quadratic (m : ℕ → ℝ) (u : Fin 3 → ℝ) :
    momentPairing m u u=sourceMomentQuadratic m 0 3 u := by
  norm_num [momentPairing,sourceMomentQuadratic,sourceMomentMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

def inverseCoefficients (m : ℕ → ℝ) : Fin 2 → ℝ :=
  (sourceMomentMatrix m 0 2)⁻¹ *ᵥ sourceMomentCoupling m 0 2

def criticalPolynomial (m : ℕ → ℝ) : Fin 3 → ℝ :=
  ![-inverseCoefficients m 0,-inverseCoefficients m 1,1]

theorem critical_polynomial_snoc (m : ℕ → ℝ) :
    criticalPolynomial m=Fin.snoc (-inverseCoefficients m) 1 := by
  ext i
  fin_cases i <;> rfl

theorem critical_coefficients_solve (m : ℕ → ℝ) (hA : IsUnit (sourceMomentMatrix m 0 2)) :
    sourceMomentMatrix m 0 2 *ᵥ inverseCoefficients m=sourceMomentCoupling m 0 2 := by
  letI := hA.invertible
  unfold inverseCoefficients
  rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]

/-- Exact reuse of PR41: invertibility of the OLD prefix, no sign of the
old or new section, and no whitening hypothesis. -/
theorem critical_moment_pairing (m : ℕ → ℝ) (hA : IsUnit (sourceMomentMatrix m 0 2)) :
    momentPairing m (criticalPolynomial m) (criticalPolynomial m)=sourceMomentSchur m 0 2 := by
  rw [moment_pairing_quadratic,critical_polynomial_snoc]
  exact NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit m 0 2 hA

/-- Algebraic orthogonality to the ENTIRE old polynomial space. This is not
an assertion that the signed form is a positive norm. -/
theorem critical_old_pairing_zero (m : ℕ → ℝ) (hA : IsUnit (sourceMomentMatrix m 0 2))
    (x : Fin 2 → ℝ) : momentPairing m (criticalPolynomial m) ![x 0,x 1,0]=0 := by
  have hs := critical_coefficients_solve m hA
  have h0 := congrFun hs (0 : Fin 2)
  have h1 := congrFun hs (1 : Fin 2)
  norm_num [sourceMomentMatrix,sourceMomentCoupling,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1
  have hz0 : m 2-m 0*inverseCoefficients m 0-m 1*inverseCoefficients m 1=0 := by linarith
  have hz1 : m 3-m 1*inverseCoefficients m 0-m 2*inverseCoefficients m 1=0 := by linarith
  calc
    _ = x 0*(m 2-m 0*inverseCoefficients m 0-m 1*inverseCoefficients m 1)+
        x 1*(m 3-m 1*inverseCoefficients m 0-m 2*inverseCoefficients m 1) := by
      norm_num [momentPairing,criticalPolynomial,Fin.sum_univ_succ]
      ring
    _ = 0 := by rw [hz0,hz1]; ring

theorem inverse_schur_source_original (k : ℕ) (m : ℕ → ℝ) :
    completedSource k (quarticInput k (criticalPolynomial m))=
      CarryRadialRefinement.physicalJet k 4-
      (inverseCoefficients m 1 : ℂ) • CarryRadialRefinement.physicalJet k 2-
      (inverseCoefficients m 0 : ℂ) • CarryRadialRefinement.physicalJet k 0 := by
  rw [quartic_source_original]
  have h0 : criticalPolynomial m 0 = -inverseCoefficients m 0 := rfl
  have h1 : criticalPolynomial m 1 = -inverseCoefficients m 1 := rfl
  have h2 : criticalPolynomial m 2 = 1 := rfl
  rw [h0,h1,h2]
  push_cast
  module

theorem critical_green_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 2)) :
    Tendsto (quarticBalance η (criticalPolynomial canonicalCompletedNativeLogDerivativeMoment)
      (criticalPolynomial canonicalCompletedNativeLogDerivativeMoment)) atTop
      (nhds (sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 2)) := by
  have h := quartic_finite_limit η hη0 hη1
    (criticalPolynomial canonicalCompletedNativeLogDerivativeMoment) (criticalPolynomial canonicalCompletedNativeLogDerivativeMoment)
  simpa only [finiteTerm,critical_moment_pairing _ hA] using h

/-- The same physical Green source becomes orthogonal to every old
polynomial in the limit, BEFORE any pivot sign is proved. -/
theorem critical_green_old_limit_zero (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 2)) (x : Fin 2 → ℝ) :
    Tendsto (quarticBalance η (criticalPolynomial canonicalCompletedNativeLogDerivativeMoment) ![x 0,x 1,0])
      atTop (nhds 0) := by
  have h := quartic_finite_limit η hη0 hη1
    (criticalPolynomial canonicalCompletedNativeLogDerivativeMoment) ![x 0,x 1,0]
  simpa only [finiteTerm,critical_old_pairing_zero _ hA] using h

theorem critical_green_correction_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 2)) :
    let c := criticalPolynomial canonicalCompletedNativeLogDerivativeMoment
    Tendsto (fun (k : ℕ) => ((k : ℝ)+1)^2*(quarticBalance η c c k-
      sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 2)) atTop
      (nhds (correctionTerm c c)) := by
  dsimp only
  have h := quartic_correction_limit η hη0 hη1
    (criticalPolynomial canonicalCompletedNativeLogDerivativeMoment) (criticalPolynomial canonicalCompletedNativeLogDerivativeMoment)
  simpa only [finiteTerm,critical_moment_pairing _ hA] using h

end
end CarryPolarizedFour
