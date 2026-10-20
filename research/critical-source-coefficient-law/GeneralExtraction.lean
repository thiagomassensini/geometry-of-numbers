import SourceTaylor

/-! Arbitrary original jet families and arbitrary Taylor orders. The whole
companion is sewn first, with an analytic remainder of the SAME source.
This is an extraction identity, never a sign or all-order positivity premise. -/
namespace CarrySourceLaw
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalMixed Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

def sourceNode (k r : ℕ) : ℂ := ((r+1:ℕ):ℂ) * (canonicalGreenJetRealStep k:ℂ)

theorem slope_eq_transverse (k r : ℕ) :
    radialCompletedSlope k r = transverseSource (sourceNode k r) := by
  unfold radialCompletedSlope transverseSource sourceNode
    canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep
  rw [← canonicalGreenJetRealStep_coe]
  congr 2
  ring

theorem sourceNode_tendsto (r : ℕ) :
    Tendsto (fun k => sourceNode k r) atTop (nhds 0) := by
  have hs : Tendsto (fun k => (canonicalGreenJetRealStep k:ℂ)) atTop (nhds 0) := by
    simpa only [canonicalGreenJetRealStep_coe] using canonicalGreenJetStep_tendsto_zero
  simpa only [sourceNode, mul_zero] using hs.const_mul ((r+1:ℕ):ℂ)

def sourceTaylorPrefix (order : ℕ) (z : ℂ) : ℂ :=
  ∑ d ∈ Finset.range order, transverseCoefficient d * z^d

def prefixCompanion (n k order : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis k (2*n) (fun r => jetStencil n k x r *
    sourceTaylorPrefix order (sourceNode k r))

def tailCompanion (R : ℂ → ℂ) (n k order : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis k (2*n) (fun r => jetStencil n k x r *
    (sourceNode k r)^order * R (sourceNode k r))

/-- One analytic remainder works for ALL coefficient vectors in any fixed
finite family. The factors and amplitudes are those of the original source.
Uniformity here is in x at fixed n/order; there is no uniform cutoff in n. -/
theorem companion_exact_taylor_sewing (n order : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ x : Fin (2*n) → ℂ,
      sourceCompanion k (nativeSourceChiralJetInput n k x) 1 =
        (Complex.I*(Real.sqrt 2:ℂ)⁻¹) •
          (prefixCompanion n k order x + tailCompanion R n k order x) := by
  obtain ⟨R,hR,he⟩ := source_exact_remainder order
  refine ⟨R,hR,?_⟩
  have hs : ∀ᶠ k : ℕ in atTop, ∀ r : Fin (2*n),
      transverseSource (sourceNode k r) = sourceTaylorPrefix order (sourceNode k r) +
        (sourceNode k r)^order * R (sourceNode k r) := by
    rw [eventually_all]
    intro r
    exact (sourceNode_tendsto r).eventually he
  filter_upwards [hs, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)]
    with k hk hr
  intro x
  rw [sourceCompanion_eq_stencil n k x (fun r => (hr r).2.1) (fun r => (hr r).2.2)]
  congr 1
  unfold prefixCompanion tailCompanion
  rw [← map_add]
  congr 1
  funext r
  simp only [Pi.add_apply, slope_eq_transverse, hk r]
  ring

/-- Complete mixed readout at EVERY order; every ordered Cauchy cross stays
in its original pairing and the analytic tail is not deleted. -/
theorem balance_exact_taylor_sewing (n order : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ x : Fin (2*n) → ℂ,
      (storage k (nativeSourceChiralJetInput n k x) 1).re =
        2*(inner ℂ (radialIncidentSynthesis k (2*n) (jetStencil n k x))
          (prefixCompanion n k order x)).re +
        2*(inner ℂ (radialIncidentSynthesis k (2*n) (jetStencil n k x))
          (tailCompanion R n k order x)).re := by
  obtain ⟨R,hR,he⟩ := source_exact_remainder order
  refine ⟨R,hR,?_⟩
  have hs : ∀ᶠ k : ℕ in atTop, ∀ r : Fin (2*n),
      transverseSource (sourceNode k r) = sourceTaylorPrefix order (sourceNode k r) +
        (sourceNode k r)^order * R (sourceNode k r) := by
    rw [eventually_all]
    intro r
    exact (sourceNode_tendsto r).eventually he
  filter_upwards [hs, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)]
    with k hk hr
  intro x
  rw [storage_eq_stencil_slope n k x (fun r => (hr r).2.1) (fun r => (hr r).2.2)]
  have hsplit : radialIncidentSynthesis k (2*n)
      (fun r => jetStencil n k x r * radialCompletedSlope k r) =
      prefixCompanion n k order x + tailCompanion R n k order x := by
    unfold prefixCompanion tailCompanion
    rw [← map_add]
    congr 1
    funext r
    simp only [Pi.add_apply, slope_eq_transverse, hk r]
    ring
  rw [hsplit, inner_add_right, Complex.add_re]
  ring

/-- Sample remainder coefficient control, available at every analytic order.
This does not bound a growing jet stencil without accounting for its powers. -/
theorem analytic_sample_remainder_tendsto (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0)
    (r : ℕ) : Tendsto (fun k => R (sourceNode k r)) atTop (nhds (R 0)) :=
  hR.continuousAt.tendsto.comp (sourceNode_tendsto r)

end
end CarrySourceLaw
