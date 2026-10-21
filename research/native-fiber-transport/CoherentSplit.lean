import ReadoutTransport
import CarrySelfAdjointOperator.CompletedC3CausalChiralSourceCoherence

/-! Split the EXISTING enriched source while preserving its duplicated-direct
coherence. Every map tested below is an existing native readout. -/
namespace CarryFiberTransport
open CarrySelfAdjointOperator CarryTraceFiber CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite
open CanonicalCompletedC3AllCutoffOnePointHilbert
open scoped InnerProductSpace ComplexConjugate
noncomputable section

local instance : InnerProductSpace ℝ CarryGammaComplexNaimark :=
  InnerProductSpace.rclikeToReal ℂ _

abbrev Source := CanonicalCompletedC3EnrichedChiralSourceCarrier
abbrev fullReadout := canonicalCompletedC3EnrichedNormalizedFullWronskianReadout
abbrev plusReadout := canonicalCompletedC3EnrichedPositiveChiralReadout
abbrev minusReadout := canonicalCompletedC3EnrichedNegativeChiralReadout
abbrev ambientReadout := canonicalCompletedC3EnrichedDirectNaimarkReadout
abbrev cameraReadout := canonicalCompletedC3EnrichedCameraReadout
abbrev enlargedReadout := canonicalCompletedC3EnrichedCoisometricChiralReadout

def tracePart (u : Source) : Source := WithLp.toLp 2
  (0, WithLp.toLp 2 (balancedLift (projection u.snd.fst),u.snd.snd))
def fiberPart (u : Source) : Source := WithLp.toLp 2
  (u.fst, WithLp.toLp 2 (invisible u.snd.fst,0))

theorem source_reconstruction (u : Source) : tracePart u+fiberPart u=u := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [tracePart,fiberPart]
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact physical_reconstruct _
    · simp [tracePart,fiberPart]

theorem tracePart_orthogonal_fiberPart (u v : Source) :
    inner ℝ (tracePart u) (fiberPart v)=0 := by
  simp only [tracePart,fiberPart,WithLp.prod_inner_apply]
  change inner ℝ 0 v.fst +
    (inner ℝ (balancedLift (projection u.snd.fst)) (invisible v.snd.fst)+inner ℝ u.snd.snd 0)=0
  rw [inner_zero_left,inner_zero_right,invisible_orthogonal]
  ring

theorem source_pairing_split (u v : Source) :
    inner ℝ u v=inner ℝ (tracePart u) (tracePart v)+inner ℝ (fiberPart u) (fiberPart v) := by
  have hrev : inner ℝ (fiberPart u) (tracePart v)=0 := by
    rw [real_inner_comm]
    exact tracePart_orthogonal_fiberPart _ _
  calc
    _ = inner ℝ (tracePart u+fiberPart u) (tracePart v+fiberPart v) := by
      rw [source_reconstruction,source_reconstruction]
    _ = _ := by
      simp only [inner_add_left,inner_add_right,tracePart_orthogonal_fiberPart,hrev]
      ring

theorem fiber_direct (u : Source) : (fiberPart u).snd.fst.direct=u.snd.fst.direct := by
  simp [fiberPart,invisible,balancedLift,direct]

theorem tracePart_coherent (u : Source) : tracePart u ∈ canonicalCompletedC3EnrichedDirectCoherentSubmodule := by
  rw [canonicalCompletedC3EnrichedDirectCoherentSubmodule_mem_iff]
  change (0 : CarryGammaComplexNaimark)=canonicalCompletedC3GammaNaimarkView
    (balancedLift (projection u.snd.fst)).direct
  simp [balancedLift,direct]

theorem fiberPart_coherent (u : Source)
    (hu : u ∈ canonicalCompletedC3EnrichedDirectCoherentSubmodule) :
    fiberPart u ∈ canonicalCompletedC3EnrichedDirectCoherentSubmodule := by
  rw [canonicalCompletedC3EnrichedDirectCoherentSubmodule_mem_iff] at hu ⊢
  change u.fst=canonicalCompletedC3GammaNaimarkView (fiberPart u).snd.fst.direct
  rw [fiber_direct]
  exact hu

theorem trace_fiber_zero (u : Source) : canonicalCompletedC3EnrichedTraceReadout (fiberPart u)=0 := by
  change projection (invisible u.snd.fst)=0
  exact projection_invisible _

theorem arch_fiber_zero (u : Source) : canonicalCompletedC3EnrichedArchimedeanReadout (fiberPart u)=0 := rfl

theorem ambient_trace_zero (u : Source) : ambientReadout (tracePart u)=0 := rfl

theorem ambient_fiber (u : Source) : ambientReadout (fiberPart u)=ambientReadout u := rfl

theorem camera_trace_zero (u : Source) : cameraReadout (tracePart u)=0 := by
  change realifiedNaimarkAdjoint (balancedLift (projection u.snd.fst)).direct=0
  simp [balancedLift,direct]

theorem camera_fiber (u : Source) : cameraReadout (fiberPart u)=cameraReadout u := by
  change realifiedNaimarkAdjoint (fiberPart u).snd.fst.direct=realifiedNaimarkAdjoint u.snd.fst.direct
  rw [fiber_direct]

theorem full_fiber_zero (z : ℂ) (u : Source) : fullReadout z (fiberPart u)=0 := by
  change WithLp.toLp 2
    (((canonicalC3ChartFactorHeight z)⁻¹*nativeXiCompletionFactor z) •
      canonicalCompletedC3EnrichedTraceReadout (fiberPart u),
     (canonicalC3ChartFactorHeight z)⁻¹ • canonicalCompletedC3EnrichedArchimedeanReadout (fiberPart u))=0
  rw [trace_fiber_zero,arch_fiber_zero]
  simp

theorem full_trace (z : ℂ) (u : Source) : fullReadout z (tracePart u)=fullReadout z u := by
  have h := congrArg (fullReadout z) (source_reconstruction u)
  rw [map_add,full_fiber_zero,add_zero] at h
  exact h

theorem plus_fiber_zero (z : ℂ) (u : Source) : plusReadout z (fiberPart u)=0 := by
  change canonicalCompletedC3FullWronskianPositiveProjectionMap (fullReadout z (fiberPart u))=0
  rw [full_fiber_zero,map_zero]

theorem minus_fiber_zero (z : ℂ) (u : Source) : minusReadout z (fiberPart u)=0 := by
  change canonicalCompletedC3FullWronskianNegativeProjectionMap (fullReadout z (fiberPart u))=0
  rw [full_fiber_zero,map_zero]

theorem plus_trace (z : ℂ) (u : Source) : plusReadout z (tracePart u)=plusReadout z u := by
  have h := congrArg (plusReadout z) (source_reconstruction u)
  rw [map_add,plus_fiber_zero,add_zero] at h
  exact h

theorem minus_trace (z : ℂ) (u : Source) : minusReadout z (tracePart u)=minusReadout z u := by
  have h := congrArg (minusReadout z) (source_reconstruction u)
  rw [map_add,minus_fiber_zero,add_zero] at h
  exact h

end
end CarryFiberTransport
