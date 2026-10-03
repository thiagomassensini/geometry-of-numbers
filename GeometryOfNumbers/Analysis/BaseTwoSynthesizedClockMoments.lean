import GeometryOfNumbers.Analysis.BaseTwoSynthesizedClockCompletion
import GeometryOfNumbers.Analysis.FiniteClockHeightLedger

/-! Specialize the existing formal response and moment ledger to coefficients
of the synthesized base-two signal. The tail is derived. Camera factor and
completion remain explicit inputs; the nonzero constant gate is not hidden.
No Gram, positivity or height theorem is used in these proofs. -/

noncomputable section
open scoped BigOperators
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GeometryOfNumbers.Analysis.FiniteClockJets
open GeometryOfNumbers.Analysis.FiniteClockHeightLedger

/-- Existing ledger with the derived tail; no free tail argument. -/
def baseTwoClosedResponseSeries (M : ℕ)
    (cameraFactor completion : PowerSeries ℂ) : PowerSeries ℂ :=
  closedResponseSeries (historicalCameraWeights 2 M)
    (baseTwoSynthesizedTailSeries M) cameraFactor completion

/-- Dressing is applied only to the already-synthesized coefficient series. -/
def baseTwoSynthesizedResponseSeries
    (cameraFactor completion : PowerSeries ℂ) : PowerSeries ℂ :=
  completion * (baseTwoCompletedClockSeries * cameraFactor⁻¹)

theorem baseTwoClosedResponseSeries_eq_synthesized (M : ℕ)
    (cameraFactor completion : PowerSeries ℂ) :
    baseTwoClosedResponseSeries M cameraFactor completion =
      baseTwoSynthesizedResponseSeries cameraFactor completion := by
  unfold baseTwoClosedResponseSeries closedResponseSeries headSeries
  rw [baseTwoHeadSeries_add_synthesizedTailSeries]
  rfl

theorem baseTwoClosedResponseSeries_cutoff_independent (M N : ℕ)
    (cameraFactor completion : PowerSeries ℂ) :
    baseTwoClosedResponseSeries M cameraFactor completion =
      baseTwoClosedResponseSeries N cameraFactor completion := by
  rw [baseTwoClosedResponseSeries_eq_synthesized, baseTwoClosedResponseSeries_eq_synthesized]

theorem baseTwoClosedResponseSeries_camera_quotient (M : ℕ)
    (cameraFactor completion : PowerSeries ℂ)
    (hB : PowerSeries.constantCoeff cameraFactor ≠ 0) :
    baseTwoClosedResponseSeries M cameraFactor completion * cameraFactor =
      completion * baseTwoCompletedClockSeries := by
  rw [baseTwoClosedResponseSeries_eq_synthesized]
  simp only [baseTwoSynthesizedResponseSeries, mul_assoc,
    PowerSeries.inv_mul_cancel cameraFactor hB, mul_one]

/-- Same historical real-even convention u=t², with the derived tail. -/
def baseTwoHistoricalPhi (M : ℕ) (cameraFactor completion : PowerSeries ℂ) : ℕ → ℝ :=
  historicalPhi (historicalCameraWeights 2 M)
    (baseTwoSynthesizedTailSeries M) cameraFactor completion

/-- Cutoff-free canonical phi of the fixed synthesized and dressed series. -/
def baseTwoSynthesizedPhi (cameraFactor completion : PowerSeries ℂ) (r : ℕ) : ℝ :=
  (PowerSeries.coeff (2*r) (baseTwoSynthesizedResponseSeries cameraFactor completion)).re

theorem baseTwoHistoricalPhi_eq_synthesized (M : ℕ)
    (cameraFactor completion : PowerSeries ℂ) :
    baseTwoHistoricalPhi M cameraFactor completion =
      baseTwoSynthesizedPhi cameraFactor completion := by
  funext r
  change (PowerSeries.coeff (2*r) (baseTwoClosedResponseSeries M cameraFactor completion)).re = _
  rw [baseTwoClosedResponseSeries_eq_synthesized]
  rfl

theorem baseTwoHistoricalPhi_cutoff_independent (M N : ℕ)
    (cameraFactor completion : PowerSeries ℂ) :
    baseTwoHistoricalPhi M cameraFactor completion =
      baseTwoHistoricalPhi N cameraFactor completion := by
  rw [baseTwoHistoricalPhi_eq_synthesized, baseTwoHistoricalPhi_eq_synthesized]

theorem baseTwoSynthesizedPhi_coefficient_formula
    (cameraFactor completion : PowerSeries ℂ) (r : ℕ) :
    baseTwoSynthesizedPhi cameraFactor completion r =
      (∑ p ∈ Finset.antidiagonal (2*r), PowerSeries.coeff p.1 completion *
        ∑ q ∈ Finset.antidiagonal p.2,
          baseTwoCompletedClockCoefficient q.1 * PowerSeries.coeff q.2 cameraFactor⁻¹).re := by
  simp only [baseTwoSynthesizedPhi, baseTwoSynthesizedResponseSeries,
    PowerSeries.coeff_mul, baseTwoCompletedClockSeries_coeff]

/-- This is the existing scalar recurrence applied AFTER synthesis and dressing. -/
def baseTwoSynthesizedLogMoment (cameraFactor completion : PowerSeries ℂ) : ℕ → ℝ :=
  finiteLogMoment (baseTwoSynthesizedPhi cameraFactor completion)

def baseTwoHistoricalLogMoment (M : ℕ)
    (cameraFactor completion : PowerSeries ℂ) : ℕ → ℝ :=
  finiteLogMoment (baseTwoHistoricalPhi M cameraFactor completion)

theorem baseTwoHistoricalLogMoment_eq_synthesized (M : ℕ)
    (cameraFactor completion : PowerSeries ℂ) :
    baseTwoHistoricalLogMoment M cameraFactor completion =
      baseTwoSynthesizedLogMoment cameraFactor completion := by
  unfold baseTwoHistoricalLogMoment baseTwoSynthesizedLogMoment
  rw [baseTwoHistoricalPhi_eq_synthesized]

theorem baseTwoSynthesizedLogMoment_cutoff_independent (M N : ℕ)
    (cameraFactor completion : PowerSeries ℂ) :
    baseTwoHistoricalLogMoment M cameraFactor completion =
      baseTwoHistoricalLogMoment N cameraFactor completion := by
  rw [baseTwoHistoricalLogMoment_eq_synthesized, baseTwoHistoricalLogMoment_eq_synthesized]

theorem baseTwoSynthesizedLogMoment_isSequence
    (cameraFactor completion : PowerSeries ℂ)
    (hphi : baseTwoSynthesizedPhi cameraFactor completion 0 ≠ 0) :
    IsLogDerivativeMomentSequence (baseTwoSynthesizedPhi cameraFactor completion)
      (baseTwoSynthesizedLogMoment cameraFactor completion) :=
  finiteLogMoment_isSequence _ hphi

theorem baseTwoSynthesizedLogMoment_unique
    (cameraFactor completion : PowerSeries ℂ)
    (hphi : baseTwoSynthesizedPhi cameraFactor completion 0 ≠ 0) (h : ℕ → ℝ)
    (hrel : IsLogDerivativeMomentSequence (baseTwoSynthesizedPhi cameraFactor completion) h) :
    baseTwoSynthesizedLogMoment cameraFactor completion = h :=
  finiteLogMoment_eq_existing hphi hrel

theorem baseTwoSynthesizedLogMoment_formal_logDerivative
    (cameraFactor completion : PowerSeries ℂ)
    (hphi : baseTwoSynthesizedPhi cameraFactor completion 0 ≠ 0) :
    PowerSeries.mk (baseTwoSynthesizedLogMoment cameraFactor completion) *
      PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion) =
        -(PowerSeries.derivative ℝ (PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion))) :=
  finiteLogMoment_formal_logDerivative _ hphi

theorem baseTwoSynthesizedLogMoment_formal_quotient
    (cameraFactor completion : PowerSeries ℂ)
    (hphi : baseTwoSynthesizedPhi cameraFactor completion 0 ≠ 0) :
    PowerSeries.mk (baseTwoSynthesizedLogMoment cameraFactor completion) =
      -(PowerSeries.derivative ℝ (PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion))) *
        (PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion))⁻¹ :=
  finiteLogMoment_formal_quotient _ hphi

/-- A formal product identity supplies exactly the preexisting coefficient relation. -/
theorem baseTwoLogMoment_relation_of_formal_identity
    (cameraFactor completion : PowerSeries ℂ) (h : ℕ → ℝ)
    (hformal : PowerSeries.mk h * PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion) =
      -(PowerSeries.derivative ℝ (PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion)))) :
    IsLogDerivativeMomentSequence (baseTwoSynthesizedPhi cameraFactor completion) h := by
  intro r
  have hc := congrArg (PowerSeries.coeff r) hformal
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, map_neg,
    PowerSeries.coeff_derivative] at hc
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] at hc
  simp only [Nat.sub_self, Nat.cast_add, Nat.cast_one] at hc ⊢
  linarith

theorem baseTwoSynthesizedLogMoment_unique_of_formal_identity
    (cameraFactor completion : PowerSeries ℂ)
    (hphi : baseTwoSynthesizedPhi cameraFactor completion 0 ≠ 0) (h : ℕ → ℝ)
    (hformal : PowerSeries.mk h * PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion) =
      -(PowerSeries.derivative ℝ (PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion)))) :
    baseTwoSynthesizedLogMoment cameraFactor completion = h :=
  baseTwoSynthesizedLogMoment_unique cameraFactor completion hphi h
    (baseTwoLogMoment_relation_of_formal_identity cameraFactor completion h hformal)

theorem baseTwoLogMoment_two_formal_constructions_eq
    (cameraFactor completion : PowerSeries ℂ)
    (hphi : baseTwoSynthesizedPhi cameraFactor completion 0 ≠ 0) (h g : ℕ → ℝ)
    (hh : PowerSeries.mk h * PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion) =
      -(PowerSeries.derivative ℝ (PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion))))
    (hg : PowerSeries.mk g * PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion) =
      -(PowerSeries.derivative ℝ (PowerSeries.mk (baseTwoSynthesizedPhi cameraFactor completion)))) :
    h = g :=
  (baseTwoLogMoment_relation_of_formal_identity cameraFactor completion h hh).unique hphi
    (baseTwoLogMoment_relation_of_formal_identity cameraFactor completion g hg)

theorem baseTwoSynthesizedLogMoment_depends_only_on_phi
    (cameraFactor completion cameraFactor' completion' : PowerSeries ℂ)
    (hphi : baseTwoSynthesizedPhi cameraFactor completion =
      baseTwoSynthesizedPhi cameraFactor' completion') :
    baseTwoSynthesizedLogMoment cameraFactor completion =
      baseTwoSynthesizedLogMoment cameraFactor' completion' := by
  unfold baseTwoSynthesizedLogMoment
  rw [hphi]

end GeometryOfNumbers.Analysis.BaseTwoCompletion
