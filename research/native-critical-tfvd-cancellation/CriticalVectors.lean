import ResponseFlux

namespace CarryCriticalTfvd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def triple (a b c : ℂ) : ℕ →₀ ℂ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

theorem triple_support (a b c : ℂ) : (triple a b c).support ⊆ Finset.range 3 := by
  intro j hj
  by_contra hn
  have hne : j≠0 ∧ j≠1 ∧ j≠2 := by
    have h : ¬ j<3 := by simpa using hn
    omega
  have hz : triple a b c j=0 := by simp [triple, hne.1, hne.2.1, hne.2.2]
  exact (Finsupp.mem_support_iff.mp hj) hz

def curvatureInput : ℕ →₀ ℂ := triple (-(1/2)) 1 (-(1/2))
def seedInput : ℕ →₀ ℂ := triple (-1) 0 0
def criticalInput (k : ℕ) (a : ℝ) : ℕ →₀ ℂ :=
  (((k : ℝ)+1)^2 : ℂ) • curvatureInput + (a : ℂ) • seedInput

theorem critical_input_triple (k : ℕ) (a : ℝ) :
    criticalInput k a = triple (-(((k : ℝ)+1)^2 : ℂ)/2-(a : ℂ))
      (((k : ℝ)+1)^2 : ℂ) (-(((k : ℝ)+1)^2 : ℂ)/2) := by
  ext j
  rcases j with _ | _ | _ | j
  all_goals simp [criticalInput,curvatureInput,seedInput,triple] <;> ring

theorem critical_input_support (k : ℕ) (a : ℝ) :
    (criticalInput k a).support ⊆ Finset.range 3 := by
  rw [critical_input_triple]; exact triple_support _ _ _

theorem synthesis_triple (a b c : ℂ) : physicalCauchySynthesis (triple a b c) =
    a • completedNativeChiralCauchyFeature 0 + b • completedNativeChiralCauchyFeature 1 +
      c • completedNativeChiralCauchyFeature 2 := by
  simp [triple, physicalCauchySynthesis]

/-- BOTH exterior directions of the stencil are kept, including address 3. -/
theorem commutator_triple (eta : ℝ) (w : ℕ → ℂ) (a b c : ℂ) :
    completionCommutator eta w (triple a b c) =
      Finsupp.single 1 ((eta : ℂ)⁻¹*(w 2-w 1)*c+(eta : ℂ)*(w 0-w 1)*a) +
      Finsupp.single 2 ((eta : ℂ)*(w 1-w 2)*b) +
      Finsupp.single 3 ((eta : ℂ)*(w 2-w 3)*c) := by
  ext j
  rcases j with _ | _ | _ | _ | j
  all_goals simp [completion_commutator_zero, completion_commutator_succ, triple]

theorem source_triple (k : ℕ) (a b c : ℂ) :
    physicalCompletedFiniteSource k (triple a b c) =
      a • canonicalCompletedNativeRadialProjectiveChiralState k 0 +
      b • canonicalCompletedNativeRadialProjectiveChiralState k 1 +
      c • canonicalCompletedNativeRadialProjectiveChiralState k 2 := by
  rw [physicalCompletedFiniteSource_original]
  simp only [triple,map_add,Finsupp.linearCombination_single]

theorem second_scale (k : ℕ) :
    ((2 : ℂ)*canonicalCompletedC3RadialSecondStep k^2)⁻¹ = -(((k : ℝ)+1)^2 : ℂ)/2 := by
  unfold canonicalCompletedC3RadialSecondStep canonicalGreenJetStep
  push_cast
  have hk : (k : ℂ)+1≠0 := by exact_mod_cast (show (k : ℝ)+1≠0 by positivity)
  field_simp [hk, Complex.I_ne_zero]
  norm_num [Complex.I_sq]

/-- Whole-vector identification with the existing, unaltered native jets.
The free coefficient a is not selected by a moment condition here. -/
theorem critical_source_jets (k : ℕ) (a : ℝ) :
    physicalCompletedFiniteSource k (criticalInput k a) =
      projectiveChiralDifferenceJet k 2 - (a : ℂ) • projectiveChiralDifferenceJet k 0 := by
  have hj2 : projectiveChiralDifferenceJet k 2 =
      (-(((k : ℝ)+1)^2 : ℂ)/2) •
        (canonicalCompletedNativeRadialProjectiveChiralState k 0 -
          (2 : ℂ) • canonicalCompletedNativeRadialProjectiveChiralState k 1 +
          canonicalCompletedNativeRadialProjectiveChiralState k 2) := by
    change ((2 : ℂ)*canonicalCompletedC3RadialSecondStep k^2)⁻¹ •
      (∑ r ∈ Finset.range 3, completedGreenForwardWeight 2 r •
        canonicalCompletedNativeRadialProjectiveChiralState k r) = _
    rw [second_scale]
    norm_num [Finset.sum_range_succ,completedGreenForwardWeight]
    module
  rw [critical_input_triple,source_triple,hj2]
  norm_num [projectiveChiralDifferenceJet,Finset.sum_range_succ,completedGreenForwardWeight]
  module

end
end CarryCriticalTfvd
