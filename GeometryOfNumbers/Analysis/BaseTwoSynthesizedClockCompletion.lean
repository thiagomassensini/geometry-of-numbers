import GeometryOfNumbers.Analysis.BaseTwoExactHeadTailCompletion
import Mathlib.RingTheory.PowerSeries.Basic

/-! Synthesize the exact signal first; its normalized iterated-derivative
coefficients then determine the tail coefficients by subtraction. No free
tail germ is an input and no derivative/sum interchange is used here.
This module does not assert analytic recovery from the coefficient tower. -/

noncomputable section
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GeometryOfNumbers.Analysis.FiniteClockJets

/-- The already-proved exact head/tail synthesis, before taking any jet. -/
def baseTwoSynthesizedSignal (M : ℕ) : ℝ → ℂ :=
  fun t => baseTwoFiniteHead M t + baseTwoCriticalCompleteTail M t

theorem baseTwoSynthesizedSignal_eq_complete (M : ℕ) :
    baseTwoSynthesizedSignal M = baseTwoCriticalCompleteSignal :=
  funext (baseTwoFiniteHead_add_completeTail M)

/-- Same factorial convention as the existing normalized finite clock jets. -/
def baseTwoCompletedClockCoefficient (r : ℕ) : ℂ :=
  (r.factorial : ℂ)⁻¹ * iteratedDeriv r baseTwoCriticalCompleteSignal 0

def baseTwoSynthesizedClockCoefficient (M r : ℕ) : ℂ :=
  (r.factorial : ℂ)⁻¹ * iteratedDeriv r (baseTwoSynthesizedSignal M) 0

theorem baseTwoSynthesizedSignal_iteratedDeriv (M r : ℕ) (t : ℝ) :
    iteratedDeriv r (baseTwoSynthesizedSignal M) t =
      iteratedDeriv r baseTwoCriticalCompleteSignal t := by
  rw [baseTwoSynthesizedSignal_eq_complete]

theorem baseTwoSynthesizedClockCoefficient_eq_complete (M r : ℕ) :
    baseTwoSynthesizedClockCoefficient M r = baseTwoCompletedClockCoefficient r := by
  simp only [baseTwoSynthesizedClockCoefficient, baseTwoCompletedClockCoefficient,
    baseTwoSynthesizedSignal_eq_complete]

theorem baseTwoCompletedClockJet_cutoff_independent (M N r : ℕ) :
    baseTwoSynthesizedClockCoefficient M r = baseTwoSynthesizedClockCoefficient N r := by
  rw [baseTwoSynthesizedClockCoefficient_eq_complete,
    baseTwoSynthesizedClockCoefficient_eq_complete]

/-- Derived residual AFTER exact synthesis and jet extraction; not an input. -/
def baseTwoSynthesizedTailCoefficient (M r : ℕ) : ℂ :=
  baseTwoCompletedClockCoefficient r -
    historicalFiniteHeadCoefficient (historicalCameraWeights 2 M) r

theorem baseTwoHeadCoefficient_add_synthesizedTailCoefficient (M r : ℕ) :
    historicalFiniteHeadCoefficient (historicalCameraWeights 2 M) r +
      baseTwoSynthesizedTailCoefficient M r = baseTwoCompletedClockCoefficient r := by
  unfold baseTwoSynthesizedTailCoefficient
  abel

/-- Exact jet residual; an iterated derivative of the tail requires smoothness. -/
theorem baseTwoSynthesizedTailCoefficient_eq_jetResidual (M r : ℕ) :
    baseTwoSynthesizedTailCoefficient M r = (r.factorial : ℂ)⁻¹ *
      (iteratedDeriv r baseTwoCriticalCompleteSignal 0 -
        iteratedDeriv r (baseTwoFiniteHead M) 0) := by
  rw [baseTwoSynthesizedTailCoefficient, baseTwoFiniteHead_normalizedClockJet]
  exact (mul_sub _ _ _).symm

theorem baseTwoSynthesizedTailCoefficient_cutoff_balance (M N r : ℕ) :
    baseTwoSynthesizedTailCoefficient M r - baseTwoSynthesizedTailCoefficient N r =
      historicalFiniteHeadCoefficient (historicalCameraWeights 2 N) r -
        historicalFiniteHeadCoefficient (historicalCameraWeights 2 M) r := by
  unfold baseTwoSynthesizedTailCoefficient
  abel

def baseTwoCompletedClockSeries : PowerSeries ℂ :=
  PowerSeries.mk baseTwoCompletedClockCoefficient

def baseTwoSynthesizedTailSeries (M : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (baseTwoSynthesizedTailCoefficient M)

@[simp] theorem baseTwoCompletedClockSeries_coeff (r : ℕ) :
    PowerSeries.coeff r baseTwoCompletedClockSeries = baseTwoCompletedClockCoefficient r :=
  PowerSeries.coeff_mk _ _

@[simp] theorem baseTwoSynthesizedTailSeries_coeff (M r : ℕ) :
    PowerSeries.coeff r (baseTwoSynthesizedTailSeries M) =
      baseTwoSynthesizedTailCoefficient M r := PowerSeries.coeff_mk _ _

theorem baseTwoHeadSeries_add_synthesizedTailSeries (M : ℕ) :
    PowerSeries.mk (historicalFiniteHeadCoefficient (historicalCameraWeights 2 M)) +
      baseTwoSynthesizedTailSeries M = baseTwoCompletedClockSeries := by
  apply PowerSeries.ext
  intro r
  simp only [map_add, PowerSeries.coeff_mk, baseTwoSynthesizedTailSeries_coeff,
    baseTwoCompletedClockSeries_coeff]
  exact baseTwoHeadCoefficient_add_synthesizedTailCoefficient M r

theorem baseTwoSynthesizedTailSeries_unique (M : ℕ) (tail : PowerSeries ℂ)
    (h : PowerSeries.mk (historicalFiniteHeadCoefficient (historicalCameraWeights 2 M)) +
      tail = baseTwoCompletedClockSeries) :
    tail = baseTwoSynthesizedTailSeries M := by
  exact add_left_cancel (h.trans (baseTwoHeadSeries_add_synthesizedTailSeries M).symm)

@[simp] theorem baseTwoCompletedClockCoefficient_zero :
    baseTwoCompletedClockCoefficient 0 = baseTwoCriticalCompleteSignal 0 := by
  simp [baseTwoCompletedClockCoefficient]

theorem baseTwoSynthesizedTailCoefficient_zero (M : ℕ) :
    baseTwoSynthesizedTailCoefficient M 0 = baseTwoCriticalCompleteTail M 0 := by
  rw [baseTwoSynthesizedTailCoefficient, baseTwoCompletedClockCoefficient_zero,
    baseTwoFiniteHead_normalizedClockJet]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDeriv_zero]
  exact (eq_sub_iff_add_eq.mpr (by
    simpa [add_comm] using baseTwoFiniteHead_add_completeTail M 0)).symm

end GeometryOfNumbers.Analysis.BaseTwoCompletion
