import SourceReadouts
import CompletedSource

/-! The complete physical states are fixed before applying their algebraic
endpoint traces. Both cutoffs, radial indices, supports and inputs remain
independent. No continuity of a trace on the ambient L2 closure is assumed. -/
namespace CarryCompletedTrace
open CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open CarryCompletedPairing CPFormal.Analytic.Cp
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def traceWedge (V C W D : EndpointDomain) : ℂ :=
  mixedScalarBoundaryWedge (endpointTrace 0 V) (endpointTrace 0 C)
    (endpointTrace 0 W) (endpointTrace 0 D)

/-- Polarized Green expression in the ORIGINAL metric, before boundary readout. -/
def eulerWedge (V C W D : EndpointDomain) : ℂ :=
  inner ℂ (eulerAction W : PhysicalCauchySpace) (C : PhysicalCauchySpace) +
  inner ℂ (W : PhysicalCauchySpace) (eulerAction C : PhysicalCauchySpace) -
  inner ℂ (eulerAction D : PhysicalCauchySpace) (V : PhysicalCauchySpace) -
  inner ℂ (D : PhysicalCauchySpace) (eulerAction V : PhysicalCauchySpace)

theorem euler_wedge_trace (V C W D : EndpointDomain) :
    eulerWedge V C W D = traceWedge V C W D := by
  have h := endpoint_green W C
  have h' := endpoint_green D V
  unfold eulerWedge traceWedge mixedScalarBoundaryWedge
  linear_combination -h + h'

theorem mixed_wedge_scale (α β V C W D : ℂ) :
    mixedScalarBoundaryWedge (α*V) (α*C) (β*W) (β*D) =
      α*conj β*mixedScalarBoundaryWedge V C W D := by
  simp only [mixedScalarBoundaryWedge,map_mul]
  ring

theorem mixed_wedge_sum {N M : ℕ} (a V C : Fin N → ℂ) (b W D : Fin M → ℂ) :
    mixedScalarBoundaryWedge (∑ i,a i*V i) (∑ i,a i*C i)
      (∑ j,b j*W j) (∑ j,b j*D j) =
    ∑ i, ∑ j, a i*conj (b j)*mixedScalarBoundaryWedge (V i) (C i) (W j) (D j) := by
  simp only [mixedScalarBoundaryWedge,map_sum,map_mul,Finset.sum_mul,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual physical endpoint pairing = weighted whole completed Mellin pairing.
The four mixed completion terms remain in the original completed source. -/
theorem completed_trace_pairing_mellin (A B k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ)
    (hz : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hw : ∀ j : Fin M, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint l j) ∈ genuineCriticalStrip) :
    traceWedge (valueCore k c r) (companionCore k c r)
      (valueCore l d s) (companionCore l d s) =
      ((Real.sqrt ((k : ℝ)+1) : ℂ)*(Real.sqrt ((l : ℝ)+1) : ℂ)) *
      ∑ i, ∑ j, sourceWeight k c r i * conj (sourceWeight l d s j) *
        completedIntegralPairing A B
          (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint l j) := by
  unfold traceWedge
  rw [value_core_trace,companion_core_trace,value_core_trace,companion_core_trace]
  simp only [Nat.descFactorial_zero,Nat.cast_one,one_mul]
  rw [mixed_wedge_scale,mixed_wedge_sum]
  simp only [Complex.conj_ofReal]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [completed_pairing_eq_original A B (hz i) (hw j)]
  rfl

theorem completed_euler_pairing_mellin (A B k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ)
    (hz : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hw : ∀ j : Fin M, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint l j) ∈ genuineCriticalStrip) :
    eulerWedge (valueCore k c r) (companionCore k c r)
      (valueCore l d s) (companionCore l d s) =
      ((Real.sqrt ((k : ℝ)+1) : ℂ)*(Real.sqrt ((l : ℝ)+1) : ℂ)) *
      ∑ i, ∑ j, sourceWeight k c r i * conj (sourceWeight l d s j) *
        completedIntegralPairing A B
          (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint l j) := by
  rw [euler_wedge_trace]
  exact completed_trace_pairing_mellin A B k l c d r s hz hw

def physicalMixedPairing (k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ) : ℂ :=
  inner ℂ (physicalSourceValue k c r) (physicalSourceCompanion l d s) -
    inner ℂ (physicalSourceCompanion k c r) (physicalSourceValue l d s)

/-- The ACTUAL Cauchy pairing, with its Gram factor still present. No
endpoint readout is substituted for the original Hilbert inner product. -/
theorem physical_mixed_pairing_mellin (A B k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ)
    (hz : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hw : ∀ j : Fin M, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint l j) ∈ genuineCriticalStrip) :
    physicalMixedPairing k l c d r s =
    ∑ i, ∑ j, conj (sourceWeight k c r i) * sourceWeight l d s j *
      inner ℂ (completedNativeRadialChiralCauchyState k i) (completedNativeRadialChiralCauchyState l j) *
      completedIntegralPairing B A
        (canonicalCompletedC3RadialTiltPoint l j) (canonicalCompletedC3RadialTiltPoint k i) := by
  change inner ℂ (ChiralReturn.sourceValue k c r) (ChiralReturn.sourceCompanion l d s) -
    inner ℂ (ChiralReturn.sourceCompanion k c r) (ChiralReturn.sourceValue l d s) = _
  unfold ChiralReturn.sourceValue ChiralReturn.sourceCompanion
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum]
  rw [← Finset.sum_sub_distrib,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [completed_pairing_eq_original B A (hw i) (hz j)]
  simp only [sourceWeight,completedGreenWronskian,completedNativeOperatorBoundaryCompanion,
    map_mul,map_neg,div_eq_mul_inv]
  ring

/-- Exact residual between the Euler boundary pairing and the original
physical pairing. Every completed Mellin cross is retained. -/
theorem boundary_minus_bulk_mellin (A B k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ)
    (hz : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hw : ∀ j : Fin M, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint l j) ∈ genuineCriticalStrip) :
    traceWedge (valueCore l d s) (companionCore l d s)
      (valueCore k c r) (companionCore k c r) - physicalMixedPairing k l c d r s =
    ∑ i, ∑ j, conj (sourceWeight k c r i) * sourceWeight l d s j *
      ((Real.sqrt ((k : ℝ)+1) : ℂ)*(Real.sqrt ((l : ℝ)+1) : ℂ) -
        inner ℂ (completedNativeRadialChiralCauchyState k i) (completedNativeRadialChiralCauchyState l j)) *
      completedIntegralPairing B A
        (canonicalCompletedC3RadialTiltPoint l j) (canonicalCompletedC3RadialTiltPoint k i) := by
  rw [completed_trace_pairing_mellin B A l k d c s r hw hz,
    physical_mixed_pairing_mellin A B k l c d r s hz hw]
  rw [Finset.sum_comm (f := fun j i => _)]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Both companion decompositions are applied at the vector level first. -/
theorem completed_trace_split (k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ)
    (hz : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hw : ∀ j : Fin M, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint l j) ∈ genuineCriticalStrip) :
    traceWedge (valueCore k c r) (companionCore k c r)
      (valueCore l d s) (companionCore l d s) =
    traceWedge (valueCore k c r) (nativeCore k c r)
      (valueCore l d s) (nativeCore l d s) +
    traceWedge (valueCore k c r) (completionCore k c r)
      (valueCore l d s) (completionCore l d s) := by
  rw [companion_core_split k c r hz,companion_core_split l d s hw]
  simp only [traceWedge,mixedScalarBoundaryWedge,map_add]
  ring

end
end CarryCompletedTrace
