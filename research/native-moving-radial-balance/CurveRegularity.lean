import MovingDerivative
import CompletionCancellation
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace CarryMovingRadial
open CarrySelfAdjointOperator Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem amplitude_analytic (z : ℂ)
    (hf : AnalyticAt ℂ completedNativeOperatorCharacteristic z)
    (hne : completedNativeOperatorCharacteristic z≠0) :
    AnalyticAt ℂ completedNativeNormalizedPositiveChiralAmplitude z := by
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  unfold completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization completedNativePositiveHermiteBiehlerCoordinate
  exact ((analyticAt_const.fun_mul hf).inv (mul_ne_zero hs hne)).fun_mul
    (hf.deriv.neg.fun_add (analyticAt_const.fun_mul hf))

theorem quotient_analytic (z : ℂ)
    (hf : AnalyticAt ℂ completedNativeOperatorCharacteristic z)
    (hp : completedNativePositiveHermiteBiehlerCoordinate z≠0) :
    AnalyticAt ℂ completedNativeHermiteBiehlerChiralQuotient z := by
  unfold completedNativeHermiteBiehlerChiralQuotient
    completedNativePositiveHermiteBiehlerCoordinate completedNativeNegativeHermiteBiehlerCoordinate
  exact (hf.deriv.neg.fun_sub (analyticAt_const.fun_mul hf)).div
    (hf.deriv.neg.fun_add (analyticAt_const.fun_mul hf)) hp

theorem radial_differentiable (f : ℂ → ℂ) (t : ℝ) (r : ℕ)
    (hf : AnalyticAt ℂ f (point t r)) :
    DifferentiableAt ℝ (fun h => f (point h r)) t := by
  have he : AnalyticAt ℂ (fun z => f (Complex.I*((r:ℂ)+1)*z)) (t:ℂ) :=
    hf.fun_comp_of_eq (by fun_prop) rfl
  exact he.differentiableAt.hasDerivAt.comp_ofReal.differentiableAt

theorem scale_differentiable (t : ℝ) (ht : 0<t) : DifferentiableAt ℝ scale t := by
  have hi := (hasDerivAt_id t).inv ht.ne'
  have hs := hi.sqrt (inv_ne_zero ht.ne')
  exact hs.ofReal_comp.differentiableAt

/-- All differentiability gates for the ACTUAL scale/amplitude/return are
discharged from original source regularity. Only raw-input regularity remains. -/
theorem curve_differentiable (N : ℕ) (x : ℝ → Fin N → ℂ) (t : ℝ) (ht : 0<t)
    (hx : ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hD : ∀ i : Fin N, point t i∈completedNativeHeightDomain)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (point t i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (point t i)≠0) :
    (∀ i : Fin N, DifferentiableAt ℝ (fun h => curveQuotient h i) t) ∧
      ∀ i : Fin N, DifferentiableAt ℝ (fun h => curveCoefficients N h (x h) i) t := by
  constructor
  · intro i
    exact radial_differentiable _ t i
      (quotient_analytic _ (completedNativeOperatorCharacteristic_analyticAt (hD i)) (hP i))
  · intro i
    exact ((scale_differentiable t ht).mul (radial_differentiable _ t i
      (amplitude_analytic _ (completedNativeOperatorCharacteristic_analyticAt (hD i)) (hF i)))).mul (hx i)

def coefficientVelocity (N : ℕ) (x : ℝ → Fin N → ℂ) (t : ℝ) : Fin N → ℂ :=
  fun i => deriv (fun h => curveCoefficients N h (x h) i) t

def returnVelocity (N : ℕ) (t : ℝ) : Fin N → ℂ := fun i => deriv (fun h => curveQuotient h i) t

/-- The requested moving-source derivative: two coefficient-motion terms
PLUS the return-flow term. It acts on the COMPLETE original two-leg state. -/
theorem physical_moving_derivative (N : ℕ) (x : ℝ → Fin N → ℂ) (t : ℝ) (ht : 0<t)
    (hx : ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hD : ∀ i : Fin N, point t i∈completedNativeHeightDomain)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (point t i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (point t i)≠0) :
    deriv (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
      (curveState N h (x h)) (curveState N h (x h))) t=
      fullPair N (fun i => curveQuotient t i) (coefficientVelocity N x t) (curveCoefficients N t (x t))+
      fullPair N (fun i => curveQuotient t i) (curveCoefficients N t (x t)) (coefficientVelocity N x t)+
      returnVariation N (fun i => curveQuotient t i) (returnVelocity N t)
        (curveCoefficients N t (x t)) (curveCoefficients N t (x t)) := by
  obtain ⟨hq,hc⟩ := curve_differentiable N x t ht hx hD hF hP
  have he : (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
      (curveState N h (x h)) (curveState N h (x h)))=
      fun h => fullPair N (fun i => curveQuotient h i)
        (curveCoefficients N h (x h)) (curveCoefficients N h (x h)) := by
    funext h; exact curve_full_pair N h _ _
  rw [he]
  exact fullPair_derivative N (fun h i => curveQuotient h i)
    (fun h => curveCoefficients N h (x h)) t hq hc

end
end CarryMovingRadial
