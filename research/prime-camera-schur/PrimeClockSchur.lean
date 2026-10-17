import PrimeClockBridge

/-! Orthogonal extraction AFTER coherent prime synthesis, with the actual
central state and the original product inner product. The global return,
all ordered prime/return crosses, and the derived tail are retained. -/
namespace CarryPrimeClock
open CarrySelfAdjointOperator GeometryOfNumbers.Analysis
open GeometryOfNumbers.Analysis.BaseTwoCompletion
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The standard zero-coordinate inclusion; its norm follows from the old
product norm. This is not an isometry fitted to a moment matrix. -/
def edgeInjectionIsometry : MaterialEdgeL2 →ₗᵢ[ℂ] MaterialCarrier where
  toLinearMap := edgeInjection
  norm_map' g := by
    have h : ‖edgeInjection g‖^2 = ‖g‖^2 := by
      simp [edgeInjection]
    nlinarith [norm_nonneg (edgeInjection g), norm_nonneg g]

theorem physicalClockHead_tendsto (t : ℝ) :
    Tendsto (fun M => physicalClockHead M t) atTop (𝓝 (physicalClock t)) := by
  rw [physicalClock_eq_interior_return]
  exact ((edgeInjectionIsometry.continuous.tendsto _).comp
    (coherentPrefix_tendsto t)).add tendsto_const_nhds

theorem physicalClockTail_tendsto_zero (t : ℝ) :
    Tendsto (fun M => physicalClockTail M t) atTop (𝓝 0) := by
  simpa only [physicalClockTail, edgeInjectionIsometry, LinearIsometry.coe_mk,
    map_zero, Function.comp_def] using ((edgeInjectionIsometry.continuous.tendsto _).comp
      (clockTail_tendsto_zero t))

def centeredCamera (M : ℕ) (t : ℝ) (p : ℕ) : MaterialCarrier :=
  carryMaterialCentralComplement
    (edgeInjection (cameraResolvedLogSlopeChannel M t p))

def centeredReturn (t : ℝ) : MaterialCarrier :=
  carryMaterialCentralComplement (returnInjection (globalClockReturn t))

def centeredHead (M : ℕ) (t : ℝ) : MaterialCarrier :=
  carryMaterialCentralComplement (physicalClockHead M t)

def centeredTail (M : ℕ) (t : ℝ) : MaterialCarrier :=
  carryMaterialCentralComplement (physicalClockTail M t)

def centeredClock (t : ℝ) : MaterialCarrier :=
  carryMaterialCentralComplement (physicalClock t)

theorem centeredHead_prime_reconstruction (M : ℕ) (t : ℝ) :
    centeredHead M t =
      (∑ p ∈ cameraResolvedLogSlopeSupport M t, centeredCamera M t p) + centeredReturn t := by
  simp only [centeredHead, physicalClockHead, centeredCamera, centeredReturn,
    coherentPrefix, cameraPrefix,
    finiteCameraResolvedLogSlopePrefixState_synthesis_apply, map_add, map_sum]

/-- Prime-prime, prime-return, return-prime, return-return, in order. -/
theorem centeredHead_pairing (M N : ℕ) (t u : ℝ) :
    inner ℂ (centeredHead M t) (centeredHead N u) =
      (∑ p ∈ cameraResolvedLogSlopeSupport M t,
        ∑ q ∈ cameraResolvedLogSlopeSupport N u,
          inner ℂ (centeredCamera M t p) (centeredCamera N u q)) +
      (∑ p ∈ cameraResolvedLogSlopeSupport M t,
        inner ℂ (centeredCamera M t p) (centeredReturn u)) +
      (∑ q ∈ cameraResolvedLogSlopeSupport N u,
        inner ℂ (centeredReturn t) (centeredCamera N u q)) +
      inner ℂ (centeredReturn t) (centeredReturn u) := by
  rw [centeredHead_prime_reconstruction M t, centeredHead_prime_reconstruction N u]
  simp only [inner_add_left, inner_add_right, sum_inner, inner_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  ring

theorem centeredClock_head_tail (M : ℕ) (t : ℝ) :
    centeredHead M t + centeredTail M t = centeredClock t := by
  change carryMaterialCentralComplement (physicalClockHead M t) +
    carryMaterialCentralComplement (physicalClockTail M t) =
      carryMaterialCentralComplement (physicalClock t)
  rw [← map_add, physicalClock_head_tail]

/-- Independent cutoffs; no separate convergence of expanded prime sums. -/
theorem centeredClock_pairing_head_tail (M N : ℕ) (t u : ℝ) :
    inner ℂ (centeredClock t) (centeredClock u) =
      inner ℂ (centeredHead M t) (centeredHead N u) +
      inner ℂ (centeredHead M t) (centeredTail N u) +
      inner ℂ (centeredTail M t) (centeredHead N u) +
      inner ℂ (centeredTail M t) (centeredTail N u) := by
  rw [← centeredClock_head_tail M t, ← centeredClock_head_tail N u]
  simp only [inner_add_left, inner_add_right]
  ring

theorem centeredHead_tendsto (t : ℝ) :
    Tendsto (fun M => centeredHead M t) atTop (𝓝 (centeredClock t)) :=
  (carryMaterialCentralComplement.continuous.tendsto _).comp (physicalClockHead_tendsto t)

theorem centeredHead_pairing_tendsto (t u : ℝ) :
    Tendsto (fun MN : ℕ × ℕ => inner ℂ (centeredHead MN.1 t) (centeredHead MN.2 u))
      (atTop ×ˢ atTop) (𝓝 (inner ℂ (centeredClock t) (centeredClock u))) := by
  exact ((centeredHead_tendsto t).comp tendsto_fst).inner
    ((centeredHead_tendsto u).comp tendsto_snd)

/-- The projection coefficient is forced by the actual central source. -/
theorem centeredClock_physical_schur (t u : ℝ) :
    inner ℂ (centeredClock t) (centeredClock u) =
      inner ℂ (physicalClock t) (physicalClock u) -
        conj (inner ℂ carryMaterialCentralUnit (physicalClock t))*
          inner ℂ carryMaterialCentralUnit (physicalClock u) :=
  carryMaterialCentral_pairing _ _

/-- This is the preexisting physical forcing, now with prime provenance. -/
theorem centeredClock_zero_eq_forcing :
    centeredClock 0 = carryMaterialClockCentralForcing := rfl

theorem centeredHead_zero_tendsto_forcing :
    Tendsto (fun M => centeredHead M 0) atTop (𝓝 carryMaterialClockCentralForcing) := by
  simpa only [centeredClock_zero_eq_forcing] using centeredHead_tendsto 0

theorem centeredClock_zero_nonzero : centeredClock 0 ≠ 0 :=
  carryMaterialClock_forcing_nonzero

end
end CarryPrimeClock
