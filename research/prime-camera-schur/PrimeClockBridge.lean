import GeometryOfNumbers.Analysis.CarryMaterialClockCentralCoupling
import GeometryOfNumbers.Analysis.BaseTwoOrdinaryLogGradientCrosswalk
import CarrySelfAdjointOperator.MultibaseTfvdCameraGramHilbertTransport

/-! The existing prime ledger, coherently synthesized into the full physical
clock carrier. Camera indices, material edges and the global return remain
distinct. The new maps are coordinate injections into the ORIGINAL product.
No moment, target Gram, new metric or spectral operator is used. -/
namespace CarryPrimeClock
open CarrySelfAdjointOperator GeometryOfNumbers.Analysis
open GeometryOfNumbers.Analysis.BaseTwoCompletion
open NativeCarrySpectralWeyl.Camera CPFormal.Analytic.Cp
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem native_line_eq_material_parameter (t : ℝ) :
    nativeLine t = baseTwoDressingParameter (t : ℂ) := by
  simp only [nativeLine, baseTwoDressingParameter, mul_comm Complex.I]

/-- A component crosswalk, not an equivalence between complete carriers. -/
theorem material_log_gradient_eq_tfvd (t : ℝ) :
    baseTwoCompletedMaterialClockL2 t =
      canonicalCompletedC3LogJetState (nativeLine t)
        (by simp [nativeLine] : 0 < (nativeLine t).re) := by
  apply lp.ext
  funext n
  change baseTwoCompletedBoundaryHilbertClockCoordinate
    (baseTwoCompletedBoundaryHilbertState t) n = positiveLogDirichletGradient (nativeLine t) n
  rw [baseTwoCompletedClockCoordinate_eq_nativeLogFormula]
  simp only [baseTwoNativeLogGradientFormula, positiveLogDirichletGradient,
    positiveLogDirichletValue, positiveDirichletValue,
    native_line_eq_material_parameter, Nat.add_assoc]

def cameraPrefix (M : ℕ) (t : ℝ) : CameraResolvedCarryVertical :=
  finiteCameraResolvedLogSlopePrefixState M t

def coherentPrefix (M : ℕ) (t : ℝ) : MaterialEdgeL2 :=
  cameraChannelSynthesis (cameraPrefix M t)

theorem coherentPrefix_eq_tfvd (M : ℕ) (t : ℝ) :
    coherentPrefix M t = canonicalCompletedC3LogJetPrefixState (nativeLine t) M :=
  finiteCameraResolvedLogSlopePrefixState_synthesis_eq_completedTfvd M t

theorem coherentPrefix_tendsto (t : ℝ) :
    Tendsto (fun M => coherentPrefix M t) atTop
      (𝓝 (baseTwoCompletedMaterialClockL2 t)) := by
  rw [material_log_gradient_eq_tfvd]
  simp_rw [coherentPrefix_eq_tfvd]
  exact canonicalCompletedC3LogJetPrefixState_tendsto (by simp [nativeLine])

/-- The omitted interior is derived from the already existing full state. -/
def clockTail (M : ℕ) (t : ℝ) : MaterialEdgeL2 :=
  baseTwoCompletedMaterialClockL2 t - coherentPrefix M t

theorem clockTail_apply (M : ℕ) (t : ℝ) (n : ℕ) :
    clockTail M t n =
      if n < M then 0 else baseTwoNativeLogGradientFormula t n := by
  simp only [clockTail, lp.coeFn_sub, Pi.sub_apply, coherentPrefix_eq_tfvd,
    canonicalCompletedC3LogJetPrefixState_apply]
  have h (k : ℕ) : baseTwoCompletedMaterialClockL2 t k = baseTwoNativeLogGradientFormula t k :=
    baseTwoOrdinaryLogGradientState_log_apply t k
  rw [h n]
  have he : positiveLogDirichletGradient (nativeLine t) n = baseTwoNativeLogGradientFormula t n := by
    simp only [positiveLogDirichletGradient, positiveLogDirichletValue, positiveDirichletValue,
      baseTwoNativeLogGradientFormula, native_line_eq_material_parameter, Nat.add_assoc]
  rw [he]
  split <;> simp_all

theorem clockTail_tendsto_zero (t : ℝ) :
    Tendsto (fun M => clockTail M t) atTop (𝓝 0) := by
  simpa only [clockTail, sub_self] using
    ((tendsto_const_nhds (x := baseTwoCompletedMaterialClockL2 t)).sub (coherentPrefix_tendsto t))

/-- Coordinate injection into seed ⊕ (edges ⊕ global return), with its old norm. -/
def edgeInjection : MaterialEdgeL2 →ₗ[ℂ] MaterialCarrier where
  toFun g := WithLp.toLp 2 (0, WithLp.toLp 2 (g, 0))
  map_add' x y := by
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · simp
    · apply (WithLp.ofLp_injective 2)
      apply Prod.ext <;> simp
  map_smul' a x := by
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · simp
    · apply (WithLp.ofLp_injective 2)
      apply Prod.ext <;> simp

def returnInjection : ℂ →ₗ[ℂ] MaterialCarrier where
  toFun b := WithLp.toLp 2 (0, WithLp.toLp 2 (0, b))
  map_add' x y := by
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · simp
    · apply (WithLp.ofLp_injective 2)
      apply Prod.ext <;> simp
  map_smul' a x := by
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · simp
    · apply (WithLp.ofLp_injective 2)
      apply Prod.ext <;> simp

def physicalClock (t : ℝ) : MaterialCarrier :=
  completedBoundaryTransportedClock
    ⟨baseTwoCompletedBoundaryHilbertState t,
      baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩

def globalClockReturn (t : ℝ) : ℂ := (physicalClock t).snd.snd

/-- The return is complete even when the interior cutoff is finite. This
does not assert that the finite prefix is in the clock graph domain. -/
def physicalClockHead (M : ℕ) (t : ℝ) : MaterialCarrier :=
  edgeInjection (coherentPrefix M t) + returnInjection (globalClockReturn t)

def physicalClockTail (M : ℕ) (t : ℝ) : MaterialCarrier :=
  edgeInjection (clockTail M t)

theorem physicalClock_eq_interior_return (t : ℝ) :
    physicalClock t = edgeInjection (baseTwoCompletedMaterialClockL2 t) +
      returnInjection (globalClockReturn t) := by
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · simp [physicalClock, edgeInjection, returnInjection]
  · apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · simp [physicalClock, edgeInjection, returnInjection]
      rfl
    · simp [globalClockReturn, edgeInjection, returnInjection]

/-- Reconstruct the actual transported clock, including its derived return. -/
theorem physicalClock_head_tail (M : ℕ) (t : ℝ) :
    physicalClockHead M t + physicalClockTail M t = physicalClock t := by
  rw [physicalClock_eq_interior_return]
  simp only [physicalClockHead, physicalClockTail, clockTail, map_sub]
  abel

/-- The global return is the original convergent whole-cell sum. -/
theorem globalClockReturn_hasSum (t : ℝ) :
    HasSum (completedBoundaryCellReturnCoordinates (physicalClock t))
      (globalClockReturn t) :=
  completedBoundaryTransportedClock_image_boundary _

theorem physicalClock_pairing (t u : ℝ) :
    inner ℂ (physicalClock t) (physicalClock u) =
      inner ℂ (baseTwoCompletedMaterialClockL2 t) (baseTwoCompletedMaterialClockL2 u) +
        conj (globalClockReturn t)*globalClockReturn u := by
  rw [physicalClock_eq_interior_return t, physicalClock_eq_interior_return u]
  simp [edgeInjection, returnInjection, WithLp.prod_inner_apply, RCLike.inner_apply, mul_comm]

theorem coherentPrefix_prime_pairing (M N : ℕ) (t u : ℝ) :
    inner ℂ (coherentPrefix M t) (coherentPrefix N u) =
      ∑ p ∈ cameraResolvedLogSlopeSupport M t,
        ∑ q ∈ cameraResolvedLogSlopeSupport N u,
          inner ℂ (cameraResolvedLogSlopeChannel M t p)
            (cameraResolvedLogSlopeChannel N u q) := by
  simp only [coherentPrefix, cameraPrefix,
    finiteCameraResolvedLogSlopePrefixState_synthesis_apply, sum_inner, inner_sum]
  rw [Finset.sum_comm]

/-- Both ordered prime crosses and the complete clock return. -/
theorem physicalClockHead_prime_pairing (M N : ℕ) (t u : ℝ) :
    inner ℂ (physicalClockHead M t) (physicalClockHead N u) =
      (∑ p ∈ cameraResolvedLogSlopeSupport M t,
        ∑ q ∈ cameraResolvedLogSlopeSupport N u,
          inner ℂ (cameraResolvedLogSlopeChannel M t p)
            (cameraResolvedLogSlopeChannel N u q)) +
        conj (globalClockReturn t)*globalClockReturn u := by
  have h : inner ℂ (physicalClockHead M t) (physicalClockHead N u) =
      inner ℂ (coherentPrefix M t) (coherentPrefix N u) +
        conj (globalClockReturn t)*globalClockReturn u := by
    simp [physicalClockHead, edgeInjection, returnInjection,
      WithLp.prod_inner_apply, RCLike.inner_apply, mul_comm]
  rw [h, coherentPrefix_prime_pairing]

end
end CarryPrimeClock
