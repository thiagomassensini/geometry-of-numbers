import GeometryOfNumbers.Analysis.CarryMaterialCentralProjectionBounds

/-! Full companion/value transport in the ORIGINAL material carrier.
The readout complement is fixed by seed+global-return, not by a target Gram.
The Green form is an adapter to the existing boundary convention; its
literal equality is checked externally without adding a Lake dependency. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Riesz mean for the existing readout seed+global-return. -/
def carryMaterialReadoutMeanVector : MaterialCarrier :=
  WithLp.toLp 2 ((1/2 : ℂ), WithLp.toLp 2 (0, (1/2 : ℂ)))

def carryMaterialReadoutProjection : MaterialCarrier →L[ℂ] MaterialCarrier :=
  baseTwoCompletedBoundaryHilbertReadout.smulRight carryMaterialReadoutMeanVector

def carryMaterialReadoutComplement : MaterialCarrier →L[ℂ] MaterialCarrier :=
  ContinuousLinearMap.id ℂ MaterialCarrier - carryMaterialReadoutProjection

theorem carryMaterialReadoutComplement_apply (y : MaterialCarrier) :
    carryMaterialReadoutComplement y =
      WithLp.toLp 2 ((y.fst-y.snd.snd)/2,
        WithLp.toLp 2 (y.snd.fst, (y.snd.snd-y.fst)/2)) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [carryMaterialReadoutComplement, carryMaterialReadoutProjection,
      carryMaterialReadoutMeanVector, baseTwoCompletedBoundaryHilbertReadout_apply]
    ring
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [carryMaterialReadoutComplement, carryMaterialReadoutProjection,
        carryMaterialReadoutMeanVector]
    · simp [carryMaterialReadoutComplement, carryMaterialReadoutProjection,
        carryMaterialReadoutMeanVector, baseTwoCompletedBoundaryHilbertReadout_apply]
      ring

theorem carryMaterialReadoutComplement_readout (y : MaterialCarrier) :
    baseTwoCompletedBoundaryHilbertReadout (carryMaterialReadoutComplement y) = 0 := by
  rw [carryMaterialReadoutComplement_apply, baseTwoCompletedBoundaryHilbertReadout_apply]
  change (y.fst-y.snd.snd)/2 + (y.snd.snd-y.fst)/2 = 0
  ring

theorem carryMaterialReadoutComplement_of_readout_zero (y : MaterialCarrier)
    (hy : baseTwoCompletedBoundaryHilbertReadout y = 0) :
    carryMaterialReadoutComplement y = y := by
  simp [carryMaterialReadoutComplement, carryMaterialReadoutProjection, hy]

theorem carryMaterialReadout_reconstruct (y : MaterialCarrier) :
    carryMaterialReadoutProjection y + carryMaterialReadoutComplement y = y := by
  change carryMaterialReadoutProjection y + (y-carryMaterialReadoutProjection y) = y
  abel

/-- Polarized upgrade of the EXISTING seed/return norm-gap identity. -/
theorem carryMaterialReadout_pairing (x y : MaterialCarrier) :
    inner ℂ x y =
      (1/2 : ℂ)*conj (baseTwoCompletedBoundaryHilbertReadout x)*
        baseTwoCompletedBoundaryHilbertReadout y +
      inner ℂ (carryMaterialReadoutComplement x) (carryMaterialReadoutComplement y) := by
  rw [carryMaterialReadoutComplement_apply, carryMaterialReadoutComplement_apply]
  simp only [WithLp.prod_inner_apply, RCLike.inner_apply,
    baseTwoCompletedBoundaryHilbertReadout_apply, map_div₀, map_sub, map_add, map_ofNat]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

/-- Componentwise Green form on the existing Hilbert space. -/
def carryMaterialPairGreen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E × E) : ℂ := inner ℂ x.2 y.1 - inner ℂ x.1 y.2

def carryMaterialPairComplement (x : MaterialCarrier × MaterialCarrier) :
    MaterialCarrier × MaterialCarrier :=
  (carryMaterialReadoutComplement x.1, carryMaterialReadoutComplement x.2)

def carryMaterialPairReadout (x : MaterialCarrier × MaterialCarrier) : ℂ × ℂ :=
  (baseTwoCompletedBoundaryHilbertReadout x.1, baseTwoCompletedBoundaryHilbertReadout x.2)

/-- The signed hidden Green balance remains, including both orientations. -/
theorem carryMaterialPairGreen_readout_ledger (x y : MaterialCarrier × MaterialCarrier) :
    carryMaterialPairGreen x y =
      (1/2 : ℂ)*carryMaterialPairGreen (carryMaterialPairReadout x) (carryMaterialPairReadout y) +
      carryMaterialPairGreen (carryMaterialPairComplement x) (carryMaterialPairComplement y) := by
  unfold carryMaterialPairGreen
  rw [carryMaterialReadout_pairing x.2 y.1, carryMaterialReadout_pairing x.1 y.2]
  simp only [carryMaterialPairReadout, carryMaterialPairComplement, RCLike.inner_apply]
  ring

/-- Full companion and twice the value; its quotient is the existing r0. -/
def carryMaterialCompanionValuePair (t : ℝ) : MaterialCarrier × MaterialCarrier :=
  (carryMaterialDressedCompanion t
    ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩,
   (2 : ℂ) • baseTwoVectorDressing t (baseTwoCompletedBoundaryHilbertState t))

theorem carryMaterialCompanionValuePair_readout (t : ℝ) :
    carryMaterialPairReadout (carryMaterialCompanionValuePair t) =
      (-deriv baseTwoCanonicalResponse t, 2*baseTwoCanonicalResponse t) := by
  apply Prod.ext
  · exact carryMaterialDressedCompanion_source_readout t
  · simp only [carryMaterialPairReadout, carryMaterialCompanionValuePair, map_smul,
      carryMaterial_dressed_completed_readout, smul_eq_mul]

/-- Source-scale reduction on the whole pair, before taking readouts. -/
def carryMaterialPairReduction (t : ℝ) :
    (MaterialCarrier × MaterialCarrier) →ₗ[ℂ] (MaterialCarrier × MaterialCarrier) where
  toFun x := (x.1-((carryMaterialResponseScale*t : ℝ) : ℂ) • x.2,
    ((carryMaterialResponseScale*t : ℝ) : ℂ) • x.1)
  map_add' x y := by
    apply Prod.ext
    · change x.1+y.1-((carryMaterialResponseScale*t : ℝ) : ℂ) • (x.2+y.2) =
        (x.1-((carryMaterialResponseScale*t : ℝ) : ℂ) • x.2) +
          (y.1-((carryMaterialResponseScale*t : ℝ) : ℂ) • y.2)
      rw [smul_add]
      abel
    · exact smul_add _ _ _
  map_smul' a x := by
    apply Prod.ext
    · change a • x.1-((carryMaterialResponseScale*t : ℝ) : ℂ) • (a • x.2) =
        a • (x.1-((carryMaterialResponseScale*t : ℝ) : ℂ) • x.2)
      rw [smul_sub, smul_comm]
    · exact smul_comm _ _ _

theorem carryMaterialPairReduction_reconstruct (t : ℝ) (x : MaterialCarrier × MaterialCarrier)
    (ht : carryMaterialResponseScale*t ≠ 0) :
    let y := carryMaterialPairReduction t x
    x = (((carryMaterialResponseScale*t : ℝ) : ℂ)⁻¹ • y.2,
      ((carryMaterialResponseScale*t : ℝ) : ℂ)⁻¹ •
        (((carryMaterialResponseScale*t : ℝ) : ℂ)⁻¹ • y.2-y.1)) := by
  have hn : ((carryMaterialResponseScale*t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  dsimp only [carryMaterialPairReduction, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [smul_smul, inv_mul_cancel₀ hn, one_smul]
  simp only [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- Division-free Green transport with two independent real parameters. -/
theorem carryMaterialPairReduction_green (t u : ℝ) (x y : MaterialCarrier × MaterialCarrier) :
    carryMaterialPairGreen (carryMaterialPairReduction t x) (carryMaterialPairReduction u y) =
      ((carryMaterialResponseScale^2*t*u : ℝ) : ℂ)*carryMaterialPairGreen x y -
        ((carryMaterialResponseScale*(u-t) : ℝ) : ℂ)*inner ℂ x.1 y.1 := by
  simp only [carryMaterialPairGreen, carryMaterialPairReduction, LinearMap.coe_mk,
    AddHom.coe_mk, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    Complex.conj_ofReal]
  push_cast
  ring

theorem carryMaterialPairReduction_readout (t : ℝ) (x : MaterialCarrier × MaterialCarrier) :
    carryMaterialPairReadout (carryMaterialPairReduction t x) =
      ((carryMaterialPairReadout x).1-((carryMaterialResponseScale*t : ℝ) : ℂ)*(carryMaterialPairReadout x).2,
       ((carryMaterialResponseScale*t : ℝ) : ℂ)*(carryMaterialPairReadout x).1) := by
  simp only [carryMaterialPairReadout, carryMaterialPairReduction, LinearMap.coe_mk,
    AddHom.coe_mk, map_sub, map_smul, smul_eq_mul]

theorem carryMaterialPairReduction_complement (t : ℝ) (x : MaterialCarrier × MaterialCarrier) :
    carryMaterialPairComplement (carryMaterialPairReduction t x) =
      carryMaterialPairReduction t (carryMaterialPairComplement x) := by
  simp only [carryMaterialPairComplement, carryMaterialPairReduction, LinearMap.coe_mk,
    AddHom.coe_mk, map_sub, map_smul]

/-- The origin need not be a removable vector zero when its readout vanishes. -/
theorem carryMaterialCompanion_center_ne_zero :
    (carryMaterialCompanionValuePair 0).1 ≠ 0 := by
  intro hz
  have h := congrArg carryMaterialCentralComplement hz
  rw [map_zero] at h
  change carryMaterialCentralComplement
    (carryMaterialDressedCompanion 0
      ⟨baseTwoCompletedBoundaryHilbertState 0, baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0⟩) = 0 at h
  rw [carryMaterialDressedCompanion_apply, map_neg, map_add, map_smul, map_smul,
    map_smul, carryMaterialCentralComplement_center, smul_zero, add_zero, neg_eq_zero] at h
  have hd := baseTwoCanonicalDressingScalar_ne_zero 0
  have hk := (smul_eq_zero.mp h).resolve_left hd
  have hk0 := (smul_eq_zero.mp hk).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
  have hp := carryMaterialCentralClock_complement_norm_lower
  change carryMaterialCentralComplement carryMaterialCentralClock = 0 at hk0
  rw [hk0, norm_zero] at hp
  norm_num at hp

/-- The derivative of the dressing acts on the value slot BEFORE readout.
The factor 1/2 comes from storing twice the value in the second slot. -/
def carryMaterialPairDressing (t : ℝ) (x : MaterialCarrier × MaterialCarrier) :
    MaterialCarrier × MaterialCarrier :=
  (baseTwoCanonicalDressingScalar t • x.1 -
      (deriv baseTwoCanonicalDressingScalar t / 2) • x.2,
    baseTwoCanonicalDressingScalar t • x.2)

theorem carryMaterialCompanionValuePair_dressing (t : ℝ) :
    carryMaterialCompanionValuePair t = carryMaterialPairDressing t
      (Complex.I • completedBoundaryTransportedClock
        ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩,
       (2 : ℂ) • baseTwoCompletedBoundaryHilbertState t) := by
  apply Prod.ext
  · dsimp only [carryMaterialCompanionValuePair, carryMaterialPairDressing]
    rw [carryMaterialDressedCompanion_apply]
    module

  · simp only [carryMaterialCompanionValuePair, carryMaterialPairDressing,
      baseTwoVectorDressing_apply, smul_smul]
    congr 1
    ring

/-- Vector Green dressing law. Both ordered derivative/value crosses stay. -/
theorem carryMaterialPairDressing_green (t u : ℝ) (x y : MaterialCarrier × MaterialCarrier) :
    carryMaterialPairGreen (carryMaterialPairDressing t x) (carryMaterialPairDressing u y) =
      conj (baseTwoCanonicalDressingScalar t)*baseTwoCanonicalDressingScalar u*
        carryMaterialPairGreen x y +
      (conj (deriv baseTwoCanonicalDressingScalar t)*baseTwoCanonicalDressingScalar u -
        conj (baseTwoCanonicalDressingScalar t)*deriv baseTwoCanonicalDressingScalar u)/2 *
          inner ℂ x.2 y.2 := by
  simp only [carryMaterialPairDressing, carryMaterialPairGreen, inner_smul_left,
    inner_smul_right, inner_sub_left, inner_sub_right, map_div₀, map_ofNat]
  ring

def carryMaterialReducedCompanionPair (t : ℝ) : MaterialCarrier × MaterialCarrier :=
  carryMaterialPairReduction t (carryMaterialCompanionValuePair t)

theorem carryMaterialReducedCompanionPair_zero :
    carryMaterialReducedCompanionPair 0 = ((carryMaterialCompanionValuePair 0).1, 0) := by
  simp [carryMaterialReducedCompanionPair, carryMaterialPairReduction]

/-- Affine centering of the actual readout-null constant; its channel is
retained explicitly in the Green ledger rather than silently removed. -/
def carryMaterialReducedCenteredPair (t : ℝ) : MaterialCarrier × MaterialCarrier :=
  ((carryMaterialReducedCompanionPair t).1-(carryMaterialCompanionValuePair 0).1,
    (carryMaterialReducedCompanionPair t).2)

theorem carryMaterialReducedCenteredPair_zero : carryMaterialReducedCenteredPair 0 = 0 := by
  simp [carryMaterialReducedCenteredPair, carryMaterialReducedCompanionPair_zero]

theorem carryMaterialReducedCenteredPair_reconstruct (t : ℝ) :
    carryMaterialReducedCompanionPair t =
      carryMaterialReducedCenteredPair t + ((carryMaterialCompanionValuePair 0).1, 0) := by
  apply Prod.ext <;> simp [carryMaterialReducedCenteredPair]

theorem carryMaterialReducedCenteredPair_green (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u) =
      carryMaterialPairGreen (carryMaterialReducedCenteredPair t) (carryMaterialReducedCenteredPair u) +
        inner ℂ (carryMaterialReducedCompanionPair t).2 (carryMaterialCompanionValuePair 0).1 -
        inner ℂ (carryMaterialCompanionValuePair 0).1 (carryMaterialReducedCompanionPair u).2 := by
  simp only [carryMaterialPairGreen, carryMaterialReducedCenteredPair,
    inner_sub_left, inner_sub_right]
  ring

/-- Zero self-Green form does not remove the two mixed Green crossings. -/
theorem carryMaterialReducedCenter_self_green :
    carryMaterialPairGreen ((carryMaterialCompanionValuePair 0).1, (0 : MaterialCarrier))
      ((carryMaterialCompanionValuePair 0).1, (0 : MaterialCarrier)) = 0 := by
  simp [carryMaterialPairGreen]

/-- The full hidden pairing is the original gradient plus the inherited
seed/return contrast, with both arguments independent. -/
theorem carryMaterialReadoutComplement_pairing (x y : MaterialCarrier) :
    inner ℂ (carryMaterialReadoutComplement x) (carryMaterialReadoutComplement y) =
      inner ℂ x.snd.fst y.snd.fst +
        (1/2 : ℂ)*conj (x.fst-x.snd.snd)*(y.fst-y.snd.snd) := by
  rw [carryMaterialReadoutComplement_apply, carryMaterialReadoutComplement_apply]
  simp only [WithLp.prod_inner_apply, RCLike.inner_apply, map_div₀, map_sub, map_ofNat]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

theorem carryMaterialPairGreen_hidden_expansion (x y : MaterialCarrier × MaterialCarrier) :
    carryMaterialPairGreen (carryMaterialPairComplement x) (carryMaterialPairComplement y) =
      (inner ℂ x.2.snd.fst y.1.snd.fst - inner ℂ x.1.snd.fst y.2.snd.fst) +
        (1/2 : ℂ)*(conj (x.2.fst-x.2.snd.snd)*(y.1.fst-y.1.snd.snd) -
          conj (x.1.fst-x.1.snd.snd)*(y.2.fst-y.2.snd.snd)) := by
  simp only [carryMaterialPairGreen, carryMaterialPairComplement,
    carryMaterialReadoutComplement_pairing]
  ring

theorem carryMaterialPairDressing_complement (t : ℝ) (x : MaterialCarrier × MaterialCarrier) :
    carryMaterialPairComplement (carryMaterialPairDressing t x) =
      carryMaterialPairDressing t (carryMaterialPairComplement x) := by
  simp only [carryMaterialPairComplement, carryMaterialPairDressing, map_sub, map_smul]

/-- The projective chart is singular at t=0. Retaining the ORIGINAL value
alongside the reduced pair gives a lossless transport at EVERY parameter. -/
def carryMaterialPairReductionWithValue (t : ℝ) :
    (MaterialCarrier × MaterialCarrier) →ₗ[ℂ] ((MaterialCarrier × MaterialCarrier) × MaterialCarrier) :=
  (carryMaterialPairReduction t).prod (LinearMap.snd ℂ MaterialCarrier MaterialCarrier)

theorem carryMaterialPairReductionWithValue_reconstruct (t : ℝ) (x : MaterialCarrier × MaterialCarrier) :
    x = ((carryMaterialPairReductionWithValue t x).1.1 +
      ((carryMaterialResponseScale*t : ℝ) : ℂ) • (carryMaterialPairReductionWithValue t x).2,
      (carryMaterialPairReductionWithValue t x).2) := by
  apply Prod.ext
  · change x.1 = x.1-((carryMaterialResponseScale*t : ℝ) : ℂ) • x.2 +
      ((carryMaterialResponseScale*t : ℝ) : ℂ) • x.2
    abel
  · rfl

theorem carryMaterialPairReductionWithValue_injective (t : ℝ) :
    Function.Injective (carryMaterialPairReductionWithValue t) := by
  intro x y h
  calc
    x = ((carryMaterialPairReductionWithValue t x).1.1 +
      ((carryMaterialResponseScale*t : ℝ) : ℂ) • (carryMaterialPairReductionWithValue t x).2,
      (carryMaterialPairReductionWithValue t x).2) := carryMaterialPairReductionWithValue_reconstruct t x
    _ = ((carryMaterialPairReductionWithValue t y).1.1 +
      ((carryMaterialResponseScale*t : ℝ) : ℂ) • (carryMaterialPairReductionWithValue t y).2,
      (carryMaterialPairReductionWithValue t y).2) := by rw [h]
    _ = y := (carryMaterialPairReductionWithValue_reconstruct t y).symm

end
end GeometryOfNumbers.Analysis
