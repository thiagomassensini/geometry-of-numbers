import RadialConservative
import StationaryObstruction
import CarrySelfAdjointOperator.CompletedNativeChiralReturnLinearizationObstruction

namespace CarryRadialConservative
open CarrySelfAdjointOperator ChiralReturn NativeLaguerre CarryConservativeIntertwiner
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

def nativeDefect (k N : ℕ) (c : Fin N → ℂ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  radialReturnedSynthesis k N c-conservativeSynthesis k N c

theorem native_defect_columns (k N : ℕ) (c : Fin N → ℂ) :
    nativeDefect k N c=∑ j,
      (c j*(completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)-
        (radialSymbol k j:ℂ))) • completedNativeRadialChiralCauchyState k j := by
  simp only [nativeDefect,radialReturnedSynthesis,conservativeSynthesis,
    LinearMap.coe_mk,AddHom.coe_mk,completedNativeRadialChiralMultiplierState,smul_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  module

/-- Independent coefficient vectors; neither mixed term is dropped. -/
theorem native_polarized_ledger (k N : ℕ) (c d : Fin N → ℂ) :
    inner ℂ (radialIncidentSynthesis k N c) (radialIncidentSynthesis k N d)-
      inner ℂ (radialReturnedSynthesis k N c) (radialReturnedSynthesis k N d)=
      conj (conservativePort k N c)*conservativePort k N d-
      inner ℂ (conservativeSynthesis k N c) (nativeDefect k N d)-
      inner ℂ (nativeDefect k N c) (conservativeSynthesis k N d)-
      inner ℂ (nativeDefect k N c) (nativeDefect k N d) := by
  have h := polarized_conservation k N c d
  unfold nativeDefect
  simp only [inner_sub_left,inner_sub_right]
  linear_combination h

theorem native_energy_ledger (k N : ℕ) (c : Fin N → ℂ) :
    ‖radialIncidentSynthesis k N c‖^2-‖radialReturnedSynthesis k N c‖^2=
      ‖conservativePort k N c‖^2-
      2*(inner ℂ (conservativeSynthesis k N c) (nativeDefect k N c)).re-
      ‖nativeDefect k N c‖^2 := by
  have h := congrArg Complex.re (native_polarized_ledger k N c c)
  simp only [Complex.sub_re] at h
  have hs (z : CanonicalCompletedNativeChiralCauchyCarrier) : (inner ℂ z z).re=‖z‖^2 :=
    (norm_sq_eq_re_inner (𝕜:=ℂ) z).symm
  have hp : (conj (conservativePort k N c)*conservativePort k N c).re=‖conservativePort k N c‖^2 := by
    rw [Complex.conj_mul']
    norm_cast
  rw [hs,hs,hp,hs] at h
  have he := congrArg Complex.re (inner_conj_symm (conservativeSynthesis k N c) (nativeDefect k N c))
  simp only [Complex.conj_re] at he
  linarith

/-- Coefficients belong to the original jet synthesis, before scalar readout. -/
def jetCoefficients (n k : ℕ) (x : Fin (2*n) → ℂ) := nativeSourceChiralJetInput n k x

theorem exact_native_transfer_jet (n k : ℕ) (x : Fin (2*n) → ℂ) :
    radialReturnTransfer k (2*n) (radialIncidentVector k (2*n) (jetCoefficients n k x))=
      (nativeSourceProjectiveBoundaryJetSynthesis n k x).2 := by
  rw [radialReturnTransfer_exact,nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource]
  rfl

/-- Domain/denominator guards remain simultaneous only on a FIXED finite support. -/
theorem finite_eventually_admissible (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ j : Fin N,
      canonicalCompletedC3RadialTiltPoint k j ∈ completedNativeHeightDomain ∧
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0 := by
  have hp0 : completedNativePositiveHermiteBiehlerCoordinate 0≠0 := by
    rw [completedNativePositiveHermiteBiehlerCoordinate_zero]
    exact mul_ne_zero Complex.I_ne_zero completedNativeOperatorCharacteristic_zero_ne_zero
  have hp := hasDerivAt_completedNativePositiveHermiteBiehlerCoordinate_zero.continuousAt.eventually_ne hp0
  have hj (j : Fin N) := (canonicalCompletedC3RadialTiltPoint_eventually_admissible j).and
    ((canonicalCompletedC3RadialTiltPoint_tendsto_zero j).eventually hp)
  have h := (Finset.univ : Finset (Fin N)).eventually_all.mpr (fun j _ => hj j)
  filter_upwards [h] with k hk j
  exact ⟨(hk j (Finset.mem_univ j)).1.1,(hk j (Finset.mem_univ j)).1.2,
    (hk j (Finset.mem_univ j)).2⟩

end
end CarryRadialConservative
