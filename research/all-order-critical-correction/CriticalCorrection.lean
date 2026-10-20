import FiniteCorrection
import AllOrderEuler

namespace CarryAllOrderCorrection
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCriticalRelative CarrySourceLaw Filter Topology
open scoped BigOperators InnerProductSpace Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

theorem boundaryPairing_eq_quadratic (s N : ℕ) (v : Fin N → ℝ) :
    boundaryPairing s N v v = sourceMomentQuadratic CarryCriticalSource.h s N v := by
  simp only [boundaryPairing,sourceMomentQuadratic,sourceMomentMatrix,dotProduct,
    Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem critical_boundary_pairing (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix CarryCriticalSource.h s.val n)) :
    boundaryPairing s.val (n+1) (criticalCoefficients s n) (criticalCoefficients s n) =
      sourceMomentSchur CarryCriticalSource.h s.val n := by
  rw [boundaryPairing_eq_quadratic]
  exact NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit
    CarryCriticalSource.h s.val n hA

/-- Explicit coefficient of the same physical critical test, not a new
source condition or an assumed norm. -/
def criticalCorrection (s : Fin 2) (n : ℕ) : ℝ :=
  canonicalCorrection s.val (n+1) (criticalCoefficients s n)

/-- GENERAL critical correction law. Only old-prefix invertibility is used
to identify the leading coefficient with Schur. Neither old nor new pivot
positivity is an assumption. -/
theorem critical_second_correction (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix CarryCriticalSource.h s.val n)) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2 *
      (criticalBalance s n k-2*sourceMomentSchur CarryCriticalSource.h s.val n))
      atTop (nhds (criticalCorrection s n)) := by
  have ht := finite_balance_second_correction s (n+1) (criticalCoefficients s n)
  rw [critical_boundary_pairing s n hA] at ht
  simpa only [criticalBalance_eq_storage,criticalInput,criticalCoordinates,criticalCorrection] using ht

/-- Removing the exact Euler contribution changes the constant term, never
the second correction. The ORIGINAL nonlinear readout is retained. -/
theorem critical_nonlinear_second_correction (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix CarryCriticalSource.h s.val n)) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2 *
      (nonlinearReadout (n+1) k (criticalCoordinates s n) -
        (2*sourceMomentSchur CarryCriticalSource.h s.val n -
          2*canonicalCompletedNativeLogDerivativeMoment 0*
            Complex.normSq (criticalCoordinates s n ⟨0,by omega⟩))))
      atTop (nhds (criticalCorrection s n)) := by
  apply (critical_second_correction s n hA).congr'
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*(n+1))]
    with k hk
  rw [criticalBalance_eq_storage,criticalInput,
    all_order_euler_exact (n+1) k (by omega) (criticalCoordinates s n)
      (fun r => (hk r).2.1) (fun r => (hk r).2.2)]
  ring

/-- CONDITIONAL orientation: the explicit source coefficient, not a new
pivot hypothesis, determines the side whenever its sign is known. -/
theorem critical_eventually_above_of_correction_pos (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix CarryCriticalSource.h s.val n))
    (hc : 0 < criticalCorrection s n) :
    ∀ᶠ k : ℕ in atTop, 2*sourceMomentSchur CarryCriticalSource.h s.val n < criticalBalance s n k := by
  have hp := (tendsto_order.mp (critical_second_correction s n hA)).1 0 hc
  filter_upwards [hp] with k hk
  have hK : 0 < ((k:ℝ)+1)^2 := by positivity
  nlinarith

theorem critical_eventually_below_of_correction_neg (s : Fin 2) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix CarryCriticalSource.h s.val n))
    (hc : criticalCorrection s n < 0) :
    ∀ᶠ k : ℕ in atTop, criticalBalance s n k < 2*sourceMomentSchur CarryCriticalSource.h s.val n := by
  have hp := (tendsto_order.mp (critical_second_correction s n hA)).2 0 hc
  filter_upwards [hp] with k hk
  have hK : 0 < ((k:ℝ)+1)^2 := by positivity
  nlinarith

end
end CarryAllOrderCorrection
