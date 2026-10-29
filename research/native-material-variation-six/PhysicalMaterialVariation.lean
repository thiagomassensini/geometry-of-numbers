import MaterialVariation
import CriticalPhysicalBridge

namespace CarryMaterialVariation
open CarrySelfAdjointOperator CarryMovingRadial NativeLaguerre Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem rho_differentiable (t : ℝ) (i : ℕ)
    (hD : point t i∈completedNativeHeightDomain)
    (hF : completedNativeOperatorCharacteristic (point t i)≠0) :
    DifferentiableAt ℝ (fun h => CarryMovingRadial.rho h i) t := by
  have hf := completedNativeOperatorCharacteristic_analyticAt hD
  have hq : AnalyticAt ℂ completedNativeOperatorLogDerivative (point t i) :=
    hf.deriv.neg.div hf hF
  have hd := radial_differentiable _ t i hq
  have he : (fun h : ℝ => CarryMovingRadial.rho h i)=fun h =>
      -Complex.I*(completedNativeOperatorLogDerivative (point h i)/2) := by
    funext h
    unfold CarryMovingRadial.rho CarryCriticalTfvd.responseReadout
    rw [CarryRadialFlow.source_normalized_response]
    simp only [point,mul_assoc]
  rw [he]
  exact (differentiableAt_const (-Complex.I)).mul (hd.div_const 2)

/-- Source regularity persists locally at a regular point, uniformly over
the fixed finite prefix. This is independent of any energy sign. -/
theorem source_regular_local (N : ℕ) (t : ℝ)
    (hD : ∀ i : Fin N, point t i∈completedNativeHeightDomain)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (point t i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (point t i)≠0) :
    ∀ᶠ h : ℝ in nhds t, ∀ i : Fin N,
      point h i∈completedNativeHeightDomain ∧
      completedNativeOperatorCharacteristic (point h i)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (point h i)≠0 := by
  apply Filter.eventually_all.mpr
  intro i
  have hp : ContinuousAt (fun h : ℝ => point h i) t := by unfold point; fun_prop
  have hf := completedNativeOperatorCharacteristic_analyticAt (hD i)
  have hfc : ContinuousAt (fun h : ℝ => completedNativeOperatorCharacteristic (point h i)) t :=
    hf.continuousAt.comp (f := fun h : ℝ => point h i) hp
  have hpc : ContinuousAt (fun h : ℝ => completedNativePositiveHermiteBiehlerCoordinate (point h i)) t := by
    unfold completedNativePositiveHermiteBiehlerCoordinate
    exact (hf.deriv.neg.continuousAt.add (continuousAt_const.mul hf.continuousAt)).comp (f := fun h : ℝ => point h i) hp
  have hd := hp.tendsto.eventually (isOpen_completedNativeHeightDomain.mem_nhds (hD i))
  filter_upwards [hd,hfc.eventually_ne (hF i),hpc.eventually_ne (hP i)] with h hd hf hp
  exact ⟨hd,hf,hp⟩

def rawVelocity (N : ℕ) (x : ℝ → Fin N → ℂ) (t : ℝ) : Fin N → ℂ :=
  fun i => deriv (fun h => x h i) t

def rhoVelocity (N : ℕ) (t : ℝ) : Fin N → ℂ := fun i => deriv (fun h => CarryMovingRadial.rho h i) t

/-- Closed variation of the ORIGINAL complete physical curve, in two
independent MATERIAL inputs. No projected, fixed-amplitude source is used. -/
theorem physical_material_derivative (N : ℕ) (x y : ℝ → Fin N → ℂ) (t : ℝ) (ht : 0<t)
    (hx : ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hy : ∀ i, DifferentiableAt ℝ (fun h => y h i) t)
    (hD : ∀ i : Fin N, point t i∈completedNativeHeightDomain)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (point t i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (point t i)≠0) :
    deriv (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
      (curveState N h (x h)) (curveState N h (y h))) t=
      materialVariation N t (fun i => CarryMovingRadial.rho t i) (rhoVelocity N t)
        (x t) (rawVelocity N x t) (y t) (rawVelocity N y t) := by
  have he : (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
      (curveState N h (x h)) (curveState N h (y h))) =ᶠ[nhds t]
      (fun h => responsePair N h (x h) (y h)) := by
    filter_upwards [source_regular_local N t hD hF hP,lt_mem_nhds ht] with h hh hp
    exact (curve_full_pair N h _ _).trans (fullPair_eq_response N h hp.le _ _
      (fun i => (hh i).2.1) (fun i => (hh i).2.2))
  rw [he.deriv_eq]
  exact (scaled_material_hasDerivAt N (fun h i => CarryMovingRadial.rho h i) x y _ _ _ t ht.ne'
    (fun i => (rho_differentiable t i (hD i) (hF i)).hasDerivAt)
    (fun i => (hx i).hasDerivAt) (fun i => (hy i).hasDerivAt)).deriv

end
end CarryMaterialVariation
