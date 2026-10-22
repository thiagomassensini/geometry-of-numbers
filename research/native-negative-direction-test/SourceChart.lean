import NativeDefect
import CriticalMargins
import SchurLogic

/-! Audit of the actual jet-restricted space. No new source, metric or moment is defined. -/
namespace CarryNegativeDirection
open CarrySelfAdjointOperator ChiralReturn CarryCriticalSource
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- The source-generated incident chart covers the WHOLE original finite incident span. -/
theorem incident_chart_eventually_bijective (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, Function.Bijective (fun x : Fin (2*n) → ℂ =>
      radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k x)) := by
  filter_upwards [nativeSourceChiralJetInput_eventually_bijective n] with k hk
  exact (radialIncidentCoordinates k (2*n)).symm.bijective.comp hk

/-- Invisibility in the actual incident leg forces the complete source input to be zero. -/
theorem incident_jet_eventually_injective (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, Function.Injective (fun x : Fin (2*n) → ℂ =>
      (nativeSourceProjectiveBoundaryJetSynthesis n k x).1) := by
  filter_upwards [nativeSourceChiralJetInput_eventually_bijective n] with k hk
  intro x y hxy
  apply hk.1
  apply radialIncidentSynthesis_injective k (2*n)
  simpa only [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource] using hxy

theorem invisible_incidence_cannot_return (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      (nativeSourceProjectiveBoundaryJetSynthesis n k x).1=0 →
      x=0 ∧ (nativeSourceProjectiveBoundaryJetSynthesis n k x).2=0 := by
  filter_upwards [incident_jet_eventually_injective n] with k hk x hx
  have hz : (nativeSourceProjectiveBoundaryJetSynthesis n k (0:Fin (2*n) → ℂ)).1=0 := by
    simp only [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,map_zero]
  have he := hk (hx.trans hz.symm)
  refine ⟨he,?_⟩
  simp only [he,nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,map_zero]

end
end CarryNegativeDirection
