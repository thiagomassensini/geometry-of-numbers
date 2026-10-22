import AcceleratedCritical

/-! Explicit finite-stencil provenance of the normalized jets. The sample
coefficients are observations of the original material wave, never moments
chosen from a target positive Gram. -/
namespace CarryFourthTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem rJet_left_constant {f : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) (c : ℂ) (m : ℕ) :
    rJet m (fun t => c*f t) = c*rJet m f := by
  rw [rJet_derivative (f:=fun t => c*f t) (analyticAt_const.mul hf), rJet_derivative hf,
    iteratedDeriv_const_mul_field]
  ring

theorem native_sample_analytic (a : ℕ) (ha : 0 < a) :
    AnalyticAt ℝ (fun t => criticalMaterialSample t a) 0 := by
  have hc : AnalyticAt ℂ (complexSample a) (0:ℂ) := (complex_sample_entire a ha).analyticAt 0
  have h := AnalyticAt.comp_of_eq (g:=complexSample a) (f:=fun t : ℝ => (t:ℂ))
    (x:=(0:ℝ)) (hc.restrictScalars (𝕜:=ℝ)) (Complex.ofRealCLM.analyticAt (0:ℝ)) rfl
  simpa only [Function.comp_def, complex_sample_real a ha] using h

def sampleJet (m a : ℕ) : ℂ := rJet m (fun t => criticalMaterialSample t a)
def fourthWeights : Fin 5 → ℂ := ![1,-4,6,-4,1]
def boundaryWeights : Fin 3 → ℂ := ![(5/8:ℂ),-1,(3/8:ℂ)]

theorem fourth_weight_stencil (f : ℕ → ℂ) (a : ℕ) :
    (∑ i : Fin 5, fourthWeights i*f (a+i.val)) = delta4 f a := by
  simp [fourthWeights, Fin.sum_univ_succ, delta4]
  ring

theorem boundary_weight_stencil (f : ℕ → ℂ) (a : ℕ) :
    (∑ i : Fin 3, boundaryWeights i*f (a+i.val)) = tailBoundary f a := by
  simp [boundaryWeights, Fin.sum_univ_succ, tailBoundary]
  ring

/-- Taylor extraction commutes with the FULL original five-point stencil. -/
theorem fourth_jet_stencil (m a : ℕ) (ha : 0 < a) :
    fourthJet m a = delta4 (sampleJet m) a := by
  have he : nativeFourth a = fun t => ∑ i : Fin 5, fourthWeights i*criticalMaterialSample t (a+i.val) := by
    funext t
    exact (fourth_weight_stencil (criticalMaterialSample t) a).symm
  rw [fourthJet, he, rJet_sum Finset.univ
    (fun i : Fin 5 => fun t => fourthWeights i*criticalMaterialSample t (a+i.val))
    (fun i _ => analyticAt_const.mul (native_sample_analytic _ (by omega))),
    ← fourth_weight_stencil (sampleJet m) a]
  apply Finset.sum_congr rfl
  intro i _
  rw [rJet_left_constant (native_sample_analytic (a+i.val) (by omega))]
  rfl

/-- The endpoint keeps the same three source addresses and coefficients. -/
theorem boundary_jet_stencil (m a : ℕ) (ha : 0 < a) :
    boundaryJet m a = tailBoundary (sampleJet m) a := by
  have he : nativeBoundary a = fun t => ∑ i : Fin 3, boundaryWeights i*criticalMaterialSample t (a+i.val) := by
    funext t
    exact (boundary_weight_stencil (criticalMaterialSample t) a).symm
  rw [boundaryJet, he, rJet_sum Finset.univ
    (fun i : Fin 3 => fun t => boundaryWeights i*criticalMaterialSample t (a+i.val))
    (fun i _ => analyticAt_const.mul (native_sample_analytic _ (by omega))),
    ← boundary_weight_stencil (sampleJet m) a]
  apply Finset.sum_congr rfl
  intro i _
  rw [rJet_left_constant (native_sample_analytic (a+i.val) (by omega))]
  rfl

theorem normalized_material_fourth_bound (m a : ℕ) (ha : 0 < a) :
    ‖delta4 (sampleJet m) a‖ ≤ 24*2^m/(a:ℝ)^4 := by
  rw [← fourth_jet_stencil m a ha]
  exact fourth_jet_bound m a ha
end
end CarryFourthTail
