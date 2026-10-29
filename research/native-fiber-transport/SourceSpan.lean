import TransportBudget
import CarrySelfAdjointOperator.CompletedC3CoisometricAmbientStrictPositivity

/-! Test on finite syntheses of the ORIGINAL canonical source family.
The source points and their independence are pre-existing. The full trace
(including completion/chart), rather than only its positive projection, is
annihilated. No arbitrary ambient direct-only vector is used. -/
namespace CarryFiberTransport
open CarrySelfAdjointOperator CarryTraceFiber CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section

/-- The existing thirteen exact native points, unchanged. -/
def nativeSources (i : Fin 13) : Source :=
  canonicalCompletedC3EnrichedChiralSourceState
    (canonicalCausalChiralObstructionPoint i)
    (operatorHeightParameter_canonicalCausalChiralObstructionPoint_mem_strip i)

def nativeSynthesis (c : Fin 13 → ℝ) : Source := ∑ i, c i • nativeSources i

theorem nativeSources_causal (i : Fin 13) :
    nativeSources i ∈ canonicalCompletedC3CausalChiralSourceSubmodule :=
  canonicalCompletedC3EnrichedChiralSourceState_mem_causalSubmodule _ _

theorem nativeSynthesis_causal (c : Fin 13 → ℝ) :
    nativeSynthesis c ∈ canonicalCompletedC3CausalChiralSourceSubmodule := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (nativeSources_causal i)

theorem nativeSources_ambient_independent :
    LinearIndependent ℝ (fun i : Fin 13 => ambientReadout (nativeSources i)) := by
  have h := (canonicalCompletedC3AmbientResponseState_realExponent_linearIndependent
    canonicalCausalChiralObstructionExponent canonicalCausalChiralObstructionExponent_pos
    canonicalCausalChiralObstructionExponent_injective).restrict_scalars' ℝ
  exact h

theorem ambient_nativeSynthesis_ne_zero (c : Fin 13 → ℝ) (hc : ∃ i, c i ≠ 0) :
    ambientReadout (nativeSynthesis c) ≠ 0 := by
  intro hz
  have hsum : ∑ i, c i • ambientReadout (nativeSources i)=0 := by
    simpa only [nativeSynthesis,map_sum,map_smul] using hz
  rcases hc with ⟨i,hi⟩
  exact hi ((Fintype.linearIndependent_iff.mp nativeSources_ambient_independent) c hsum i)

/-- A source-derived kernel witness for the FULL fixed-parameter trace.
This is more specific than the older abstract finite-rank consumer no-go. -/
theorem full_trace_native_kernel_witness (z : ℂ) :
    ∃ c : Fin 13 → ℝ, (∃ i, c i ≠ 0) ∧
      fullReadout z (nativeSynthesis c)=0 ∧
      ambientReadout (nativeSynthesis c) ≠ 0 := by
  have hdep : ¬ LinearIndependent ℝ (fun i : Fin 13 => fullReadout z (nativeSources i)) := by
    intro h
    have hc := h.fintype_card_le_finrank
    rw [finrank_real_canonicalCompletedC3FullWronskianOperatorCarrier] at hc
    norm_num at hc
  rcases Fintype.not_linearIndependent_iff.mp hdep with ⟨c,hc,hne⟩
  refine ⟨c,hne,?_,ambient_nativeSynthesis_ne_zero c hne⟩
  simpa only [nativeSynthesis,map_sum,map_smul] using hc

/-- Exact negative energy in an ACTUAL causal source combination. The
operator parameter z is fixed across all thirteen source slots; this does
not concern the variable-parameter canonical kernel as a Gram family. -/
theorem causal_full_trace_negative_witness (z : ℂ) (hz : 0 < z.im) :
    ∃ c : Fin 13 → ℝ, (∃ i, c i ≠ 0) ∧
      nativeSynthesis c ∈ canonicalCompletedC3CausalChiralSourceSubmodule ∧
      fullReadout z (nativeSynthesis c)=0 ∧
      defectEnergy z (tracePart (nativeSynthesis c))=0 ∧
      defectEnergy z (fiberPart (nativeSynthesis c))<0 ∧
      defectEnergy z (nativeSynthesis c)<0 := by
  rcases full_trace_native_kernel_witness z with ⟨c,hc,hfull,ha⟩
  have hneg : -(2*z.im)*‖ambientReadout (nativeSynthesis c)‖^2 < 0 := by
    have hn := sq_pos_of_pos (norm_pos_iff.mpr ha)
    nlinarith
  have htrace : defectEnergy z (tracePart (nativeSynthesis c))=0 := by
    rw [defect_of_full_zero z hz.le _ (by rw [full_trace,hfull]),ambient_trace_zero,norm_zero]
    ring
  refine ⟨c,hc,nativeSynthesis_causal c,hfull,htrace,?_,?_⟩
  · rw [fiber_defect_exact z hz.le]
    exact hneg
  · rw [defect_of_full_zero z hz.le _ hfull]
    exact hneg


/-- Coisometric port provenance survives complete finite source synthesis.
The Gamma view changes only the scalar-space instance, never a coordinate. -/
theorem nativeSynthesis_ambient_port (c : Fin 13 → ℝ) :
    ambientReadout (nativeSynthesis c)=
      (canonicalCompletedC3GammaNaimarkViewContinuousLinearMap.comp
        NativeCarrySpectralWeyl.Infinite.realifiedNaimarkPort)
          (cameraReadout (nativeSynthesis c)) := by
  have hpoint (i : Fin 13) : ambientReadout (nativeSources i)=
      (canonicalCompletedC3GammaNaimarkViewContinuousLinearMap.comp
        NativeCarrySpectralWeyl.Infinite.realifiedNaimarkPort)
          (cameraReadout (nativeSources i)) := by
    unfold nativeSources cameraReadout
    rw [canonicalCompletedC3EnrichedCameraReadout_sourceState]
    rfl
  simp only [nativeSynthesis,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hpoint]

theorem nativeSynthesis_ambient_norm_camera (c : Fin 13 → ℝ) :
    ‖ambientReadout (nativeSynthesis c)‖=‖cameraReadout (nativeSynthesis c)‖ := by
  rw [nativeSynthesis_ambient_port]
  change ‖NativeCarrySpectralWeyl.Infinite.realifiedNaimarkPort (cameraReadout (nativeSynthesis c))‖=_
  exact norm_realifiedNaimarkPort _

end
end CarryFiberTransport
