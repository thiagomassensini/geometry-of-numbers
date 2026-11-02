import DirectBound
import VariationalSchur
import SchurLogic

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial CarryVariationalSchur NativeMomentOrthogonalization NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

def coefficientFromFin {N : ℕ} (v : Fin N → ℝ) (i : ℕ) : ℝ :=
  if hi : i<N then v ⟨i,hi⟩ else 0

theorem finite_odd_form_eq_quadratic (N : ℕ) (v : Fin N → ℝ) :
    oddCanonicalForm (Finset.range N) (coefficientFromFin v) =
      sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 N v := by
  unfold oddCanonicalForm sourceMomentQuadratic
  simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,sourceMomentMatrix,Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [coefficientFromFin]
  ring

/-- The original n+1 odd jets corresponding to a finite coefficient vector. -/
def finiteSourceEnergy (N : ℕ) (v : Fin N → ℝ) (k : ℕ) : ℝ :=
  fullEnergy k (finiteOddJetSource (Finset.range N) (coefficientFromFin v) k)

def criticalFin (n : ℕ) : Fin (n+1) → ℝ :=
  Fin.snoc (-((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
    sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment 1 n)) 1

def trialFin (n : ℕ) (z : Fin n → ℝ) : Fin (n+1) → ℝ := Fin.snoc (-z) 1

def physicalFiniteError (N : ℕ) (v : Fin N → ℝ) (k : ℕ) : ℝ :=
  (radialFourSourceStep k)^2*familyConstant (Finset.range N) (coefficientFromFin v)

theorem finite_source_error (N : ℕ) (v : Fin N → ℝ) (k : ℕ)
    (hk : oddGridCutoff (Finset.range N) ≤ k) :
    |finiteSourceEnergy N v k - sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 N v| ≤
      physicalFiniteError N v k := by
  simpa only [finiteSourceEnergy,physicalFiniteError,finite_odd_form_eq_quadratic] using
    finite_energy_direct_error (Finset.range N) (coefficientFromFin v) k hk

/-- The trial and critical states are the ORIGINAL source; the signed
identity is exact and needs only invertibility of the old block. -/
theorem finite_critical_transfer (n k : ℕ) (z : Fin n → ℝ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n))
    (hk : oddGridCutoff (Finset.range (n+1)) ≤ k) :
    finiteSourceEnergy (n+1) (trialFin n z) k -
      (sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 n z ⬝ᵥ
        ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
          sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 n z)) -
      physicalFiniteError (n+1) (trialFin n z) k -
      physicalFiniteError (n+1) (criticalFin n) k ≤
      finiteSourceEnergy (n+1) (criticalFin n) k := by
  have ht := finite_source_error (n+1) (trialFin n z) k hk
  have hc := finite_source_error (n+1) (criticalFin n) k hk
  have hi := sourceTrialEnergy_eq_schur_add_residual_of_isUnit
    canonicalCompletedNativeLogDerivativeMoment 1 n hA z
  have hq := sourceMomentSchur_critical_direction_of_isUnit
    canonicalCompletedNativeLogDerivativeMoment 1 n hA
  change sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 (n+1)
      (trialFin n z) = _ at hi
  change sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 (n+1)
      (criticalFin n) = _ at hq
  have ht' := (abs_le.mp ht).1
  have hc' := (abs_le.mp hc).1
  have ht'' := (abs_le.mp ht).2
  linarith

end
end CarryDirectAnchor
