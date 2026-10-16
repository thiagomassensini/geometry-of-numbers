import GeometryOfNumbers.Analysis.CarryMaterialResidualResponse
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Central-plane deflation of the SAME completed material source. The
complex line is the real plane of the two quadratures. No target Gram enters
the definitions. The canonical residual identification is a separate test. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev MaterialCarrier := BaseTwoCompletedBoundaryHilbertCarrier

theorem carryMaterial_center_ne_zero : baseTwoCompletedBoundaryHilbertState 0 ≠ 0 := by
  intro h
  have hs := congrArg (fun y : MaterialCarrier => y.fst) h
  simp only [carryMaterial_source_seed, WithLp.zero_fst] at hs
  exact one_ne_zero hs

/-- Unit vector determined by the actual completed source at zero. -/
def carryMaterialCentralUnit : MaterialCarrier :=
  ((‖baseTwoCompletedBoundaryHilbertState 0‖ : ℂ)⁻¹) • baseTwoCompletedBoundaryHilbertState 0

theorem carryMaterialCentralUnit_norm : ‖carryMaterialCentralUnit‖ = 1 := by
  have hn := norm_ne_zero_iff.mpr carryMaterial_center_ne_zero
  simp [carryMaterialCentralUnit, norm_smul, Complex.norm_real, hn]

theorem carryMaterialCentralUnit_inner : inner ℂ carryMaterialCentralUnit carryMaterialCentralUnit = 1 := by
  rw [inner_self_eq_norm_sq_to_K, carryMaterialCentralUnit_norm]
  norm_num

def carryMaterialCentralProjection : MaterialCarrier →L[ℂ] MaterialCarrier :=
  (innerSL ℂ carryMaterialCentralUnit).smulRight carryMaterialCentralUnit

def carryMaterialCentralComplement : MaterialCarrier →L[ℂ] MaterialCarrier :=
  ContinuousLinearMap.id ℂ MaterialCarrier - carryMaterialCentralProjection

theorem carryMaterialCentralProjection_apply (y : MaterialCarrier) :
    carryMaterialCentralProjection y = inner ℂ carryMaterialCentralUnit y • carryMaterialCentralUnit := rfl

theorem carryMaterialCentralComplement_apply (y : MaterialCarrier) :
    carryMaterialCentralComplement y = y - inner ℂ carryMaterialCentralUnit y • carryMaterialCentralUnit := rfl

theorem carryMaterialCentral_reconstruct (y : MaterialCarrier) :
    carryMaterialCentralProjection y + carryMaterialCentralComplement y = y := by
  simp only [carryMaterialCentralComplement_apply, carryMaterialCentralProjection_apply]
  abel

theorem carryMaterialCentralComplement_unit_inner (y : MaterialCarrier) :
    inner ℂ carryMaterialCentralUnit (carryMaterialCentralComplement y) = 0 := by
  rw [carryMaterialCentralComplement_apply, inner_sub_right, inner_smul_right,
    carryMaterialCentralUnit_inner, mul_one, sub_self]

theorem carryMaterialCentralComplement_rotation (y : MaterialCarrier) :
    carryMaterialCentralComplement (Complex.I • y) = Complex.I • carryMaterialCentralComplement y :=
  map_smul carryMaterialCentralComplement Complex.I y

theorem carryMaterialCentralComplement_center :
    carryMaterialCentralComplement (baseTwoCompletedBoundaryHilbertState 0) = 0 := by
  have hn : (‖baseTwoCompletedBoundaryHilbertState 0‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr carryMaterial_center_ne_zero
  have hu : baseTwoCompletedBoundaryHilbertState 0 =
      (‖baseTwoCompletedBoundaryHilbertState 0‖ : ℂ) • carryMaterialCentralUnit := by
    simp only [carryMaterialCentralUnit, smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [hu, map_smul, carryMaterialCentralComplement_apply,
    carryMaterialCentralUnit_inner, one_smul, sub_self, smul_zero]

/-- Every ordered crossing survives; the central/complement mixed terms
vanish by proved orthogonality, not by deletion of a return coordinate. -/
theorem carryMaterialCentral_pairing (x y : MaterialCarrier) :
    inner ℂ (carryMaterialCentralComplement x) (carryMaterialCentralComplement y) =
      inner ℂ x y - conj (inner ℂ carryMaterialCentralUnit x)*inner ℂ carryMaterialCentralUnit y := by
  simp only [carryMaterialCentralComplement_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, carryMaterialCentralUnit_inner, mul_one]
  rw [inner_conj_symm x carryMaterialCentralUnit]
  ring

theorem carryMaterialCentral_full_pairing (x y : MaterialCarrier) :
    inner ℂ x y = inner ℂ (carryMaterialCentralProjection x) (carryMaterialCentralProjection y) +
      inner ℂ (carryMaterialCentralComplement x) (carryMaterialCentralComplement y) := by
  rw [carryMaterialCentral_pairing]
  simp only [carryMaterialCentralProjection_apply, inner_smul_left, inner_smul_right,
    carryMaterialCentralUnit_inner, mul_one]
  ring

/-- Fixed normalization already used in the central-calibration investigation. -/
def carryMaterialNormalizedState (t : ℝ) : MaterialCarrier :=
  (((Real.sqrt 2 : ℝ) : ℂ)*baseTwoCanonicalResponse t)⁻¹ •
    baseTwoVectorDressing t (baseTwoCompletedBoundaryHilbertState t)

def carryMaterialCenteredState (t : ℝ) : MaterialCarrier :=
  carryMaterialCentralComplement (carryMaterialNormalizedState t)

theorem carryMaterialNormalizedState_cancel (t : ℝ) :
    carryMaterialNormalizedState t =
      (((Real.sqrt 2 : ℝ) : ℂ)*baseTwoCriticalCompleteSignal t)⁻¹ •
        baseTwoCompletedBoundaryHilbertState t := by
  rw [carryMaterialNormalizedState, baseTwoVectorDressing_apply, smul_smul,
    baseTwoCanonicalResponse_eq_dressing_mul_signal]
  congr 1
  have hd := baseTwoCanonicalDressingScalar_ne_zero t
  rw [mul_inv_rev, mul_inv_rev]
  field_simp

theorem carryMaterialCenteredState_zero : carryMaterialCenteredState 0 = 0 := by
  rw [carryMaterialCenteredState, carryMaterialNormalizedState_cancel, map_smul,
    carryMaterialCentralComplement_center, smul_zero]

/-- The derivative of the scalar normalization cancels ONLY because the
entire central state is killed; the projected material clock stays intact. -/
theorem carryMaterialCenteredState_hasDerivAt_zero :
    HasDerivAt carryMaterialCenteredState
      ((((Real.sqrt 2 : ℝ) : ℂ)*baseTwoCriticalCompleteSignal 0)⁻¹ •
        carryMaterialCentralComplement (-Complex.I • completedBoundaryTransportedClock
          ⟨baseTwoCompletedBoundaryHilbertState 0, baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0⟩)) 0 := by
  have hs := (baseTwoCriticalCompleteSignal_analyticAt 0).differentiableAt.hasDerivAt
  have hn : ((Real.sqrt 2 : ℝ) : ℂ)*baseTwoCriticalCompleteSignal 0 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')
      carryMaterial_origin_signal_ne_zero
  have hi := (hs.const_mul ((Real.sqrt 2 : ℝ) : ℂ)).inv hn
  have hy := (carryMaterialCentralComplement.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (completedBoundaryState_hasDerivAt_clock 0)
  have h := hi.smul hy
  change HasDerivAt (fun t : ℝ => (((Real.sqrt 2 : ℝ) : ℂ)*baseTwoCriticalCompleteSignal t)⁻¹ •
    carryMaterialCentralComplement (baseTwoCompletedBoundaryHilbertState t))
    ((((Real.sqrt 2 : ℝ) : ℂ)*baseTwoCriticalCompleteSignal 0)⁻¹ •
      carryMaterialCentralComplement (-Complex.I • completedBoundaryTransportedClock
        ⟨baseTwoCompletedBoundaryHilbertState 0, baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0⟩) +
      _ • carryMaterialCentralComplement (baseTwoCompletedBoundaryHilbertState 0)) 0 at h
  rw [carryMaterialCentralComplement_center, smul_zero, add_zero] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by
    rw [carryMaterialCenteredState, carryMaterialNormalizedState_cancel, map_smul])


/-- The projection preserves the existing graph domain: its subtracted
central vector is itself a proved graph-domain element. -/
theorem carryMaterialCentralComplement_mem_clockDomain (y : MaterialCarrier)
    (hy : y ∈ completedBoundaryTransportedClock.domain) :
    carryMaterialCentralComplement y ∈ completedBoundaryTransportedClock.domain := by
  rw [carryMaterialCentralComplement_apply]
  apply completedBoundaryTransportedClock.domain.sub_mem hy
  apply completedBoundaryTransportedClock.domain.smul_mem
  apply completedBoundaryTransportedClock.domain.smul_mem
  exact baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0

/-- Exact quadratic Schur complement in the original Hilbert metric. -/
theorem carryMaterialCentralComplement_norm_sq (y : MaterialCarrier) :
    ‖carryMaterialCentralComplement y‖^2 =
      ‖y‖^2 - ‖inner ℂ carryMaterialCentralUnit y‖^2 := by
  have h := congrArg Complex.re (carryMaterialCentral_pairing y y)
  simp only [inner_self_eq_norm_sq_to_K, Complex.sub_re, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] at h
  simp only [← RCLike.ofReal_pow, ← Complex.sq_norm] at h
  change (‖carryMaterialCentralComplement y‖^2 : ℝ) = ‖y‖^2 - ‖inner ℂ carryMaterialCentralUnit y‖^2 at h
  exact h

/-- First-jet energy: full clock, full return, and the central-clock crossing. -/
theorem carryMaterialCenteredState_firstJet_energy :
    let k := completedBoundaryTransportedClock
      ⟨baseTwoCompletedBoundaryHilbertState 0, baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0⟩
    ‖deriv carryMaterialCenteredState 0‖^2 =
      (‖k‖^2 - ‖inner ℂ carryMaterialCentralUnit k‖^2) /
        (2*‖baseTwoCriticalCompleteSignal 0‖^2) := by
  dsimp only
  rw [carryMaterialCenteredState_hasDerivAt_zero.deriv,
    map_smul, norm_smul, norm_smul, norm_inv, norm_mul, mul_pow, mul_pow,
    norm_neg, Complex.norm_I, one_pow, one_mul]
  have hs : ‖((Real.sqrt 2 : ℝ) : ℂ)‖^2 = 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  rw [inv_pow, mul_pow, hs, carryMaterialCentralComplement_norm_sq]
  ring

/-- Explicit Schur formula for the actual normalized physical family, with
both independent parameters. It is not assumed to be the canonical kernel. -/
theorem carryMaterialCenteredState_pairing (t u : ℝ) :
    inner ℂ (carryMaterialCenteredState t) (carryMaterialCenteredState u) =
      inner ℂ (carryMaterialNormalizedState t) (carryMaterialNormalizedState u) -
        conj (inner ℂ carryMaterialCentralUnit (carryMaterialNormalizedState t))*
          inner ℂ carryMaterialCentralUnit (carryMaterialNormalizedState u) :=
  carryMaterialCentral_pairing _ _

/-- Lossless Hilbert-sum transport. The removed central plane is retained
beside its orthogonal complement, using only the original metric. -/
def carryMaterialCentralSplit : MaterialCarrier →L[ℂ] WithLp 2 (MaterialCarrier × MaterialCarrier) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ MaterialCarrier MaterialCarrier).symm.toContinuousLinearMap.comp
    (carryMaterialCentralProjection.prod carryMaterialCentralComplement)

theorem carryMaterialCentralSplit_pairing (x y : MaterialCarrier) :
    inner ℂ (carryMaterialCentralSplit x) (carryMaterialCentralSplit y) = inner ℂ x y := by
  rw [WithLp.prod_inner_apply]
  exact (carryMaterialCentral_full_pairing x y).symm

theorem carryMaterialCentralComplement_quadratures :
    carryMaterialCentralComplement carryMaterialCentralUnit = 0 ∧
      carryMaterialCentralComplement (Complex.I • carryMaterialCentralUnit) = 0 := by
  have he : carryMaterialCentralComplement carryMaterialCentralUnit = 0 := by
    rw [carryMaterialCentralComplement_apply, carryMaterialCentralUnit_inner, one_smul, sub_self]
  exact ⟨he, by rw [map_smul, he, smul_zero]⟩

end
end GeometryOfNumbers.Analysis
