import GeometryOfNumbers.Analysis.CarryMaterialCompanionGreenTransport
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The central/complement blocks of the EXISTING material clock, on its
graph domain. The coupling is derived from the actual central source Y0.
No autonomous evolution, symmetric clock, new metric, or higher Hilbert jet
is asserted. Dressing and projective reduction retain their signed crosses. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

local notation "Y" => baseTwoCompletedBoundaryHilbertState
local notation "L" => completedBoundaryTransportedClock
local notation "P" => carryMaterialCentralProjection
local notation "Q" => carryMaterialCentralComplement
local notation "D" => baseTwoCanonicalDressingScalar

/-- Coefficient in the original central line, expressed relative to Y0
rather than the already normalized unit vector. It changes no amplitude. -/
def carryMaterialClockCentralCoefficient : MaterialCarrier →L[ℂ] ℂ :=
  ((‖Y 0‖ : ℂ)⁻¹) • innerSL ℂ carryMaterialCentralUnit

theorem carryMaterialClock_central_projection (y : MaterialCarrier) :
    P y = carryMaterialClockCentralCoefficient y • Y 0 := by
  change inner ℂ carryMaterialCentralUnit y •
    (((‖Y 0‖ : ℂ)⁻¹) • Y 0) =
      (((‖Y 0‖ : ℂ)⁻¹)*inner ℂ carryMaterialCentralUnit y) • Y 0
  rw [smul_smul]
  congr 1
  ring

theorem carryMaterialClock_central_coefficient_zero :
    carryMaterialClockCentralCoefficient (Y 0) = 1 := by
  have he : P (Y 0) = Y 0 := by
    have h := carryMaterialCentral_reconstruct (Y 0)
    simpa only [carryMaterialCentralComplement_center, add_zero] using h
  rw [carryMaterialClock_central_projection] at he
  have hseed := congrArg (fun y : MaterialCarrier => y.fst) he
  simpa only [WithLp.smul_fst, carryMaterial_source_seed, smul_eq_mul, mul_one] using hseed

/-- The existing complement map preserves the existing clock graph domain. -/
def carryMaterialClockDomainComplement : completedBoundaryTransportedClock.domain →ₗ[ℂ] completedBoundaryTransportedClock.domain where
  toFun y := ⟨Q y.val, carryMaterialCentralComplement_mem_clockDomain y.val y.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add Q x.val y.val
  map_smul' a x := by apply Subtype.ext; exact map_smul Q a x.val

/-- Concrete forcing vector from the completed physical central state.
It includes the clocked global return before central projection. -/
def carryMaterialClockCentralForcing : MaterialCarrier := Q carryMaterialCentralClock

/-- The forcing retains the actual first material-edge logarithmic contrast. -/
theorem carryMaterialClock_forcing_material_coordinate :
    carryMaterialCentralEdgeContrast carryMaterialClockCentralForcing =
      ((Real.log 2 / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [carryMaterialClockCentralForcing, carryMaterialCentralEdgeContrast_complement,
    carryMaterialCentralEdgeContrast_clock]

theorem carryMaterialClock_forcing_nonzero : carryMaterialClockCentralForcing ≠ 0 := by
  intro hz
  have h := carryMaterialCentralClock_complement_norm_lower
  change (1/32 : ℝ) < ‖carryMaterialClockCentralForcing‖^2 at h
  rw [hz, norm_zero] at h
  norm_num at h

/-- Exact full-clock reconstruction; no iterate of L is required. -/
theorem carryMaterialClock_domain_reconstruct (y : completedBoundaryTransportedClock.domain) :
    L y = L (carryMaterialClockDomainComplement y) +
      carryMaterialClockCentralCoefficient y.val • carryMaterialCentralClock := by
  have hy : y = carryMaterialClockDomainComplement y +
      carryMaterialClockCentralCoefficient y.val •
        (⟨Y 0, baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0⟩ : completedBoundaryTransportedClock.domain) := by
    apply Subtype.ext
    change y.val = Q y.val + carryMaterialClockCentralCoefficient y.val • Y 0
    rw [← carryMaterialClock_central_projection]
    exact (carryMaterialCentral_reconstruct y.val).symm.trans (add_comm _ _)
  conv_lhs => rw [hy]
  change completedBoundaryTransportedClock.toFun (_ + _) = _
  rw [map_add, map_smul]
  rfl

/-- The central-to-complement block has one source-derived forcing vector.
The compressed action is still evaluated only on its proved graph domain. -/
theorem carryMaterialClock_complement_forced (y : completedBoundaryTransportedClock.domain) :
    Q (L y) = Q (L (carryMaterialClockDomainComplement y)) +
      carryMaterialClockCentralCoefficient y.val • carryMaterialClockCentralForcing := by
  rw [carryMaterialClock_domain_reconstruct y, map_add, map_smul]
  rfl

def carryMaterialClockComplementState (t : ℝ) : MaterialCarrier := Q (Y t)

def carryMaterialClockComplementAction (t : ℝ) : MaterialCarrier :=
  Q (L (carryMaterialClockDomainComplement
    ⟨Y t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩))

theorem carryMaterialClock_complement_derivative (t : ℝ) :
    HasDerivAt carryMaterialClockComplementState
      (-Complex.I • (carryMaterialClockComplementAction t +
        carryMaterialClockCentralCoefficient (Y t) • carryMaterialClockCentralForcing)) t := by
  have h := (carryMaterialCentralComplement.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (completedBoundaryState_hasDerivAt_clock t)
  have he : Q (L ⟨Y t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩) =
      carryMaterialClockComplementAction t +
        carryMaterialClockCentralCoefficient (Y t) • carryMaterialClockCentralForcing :=
    carryMaterialClock_complement_forced _
  change HasDerivAt carryMaterialClockComplementState
    (Q (-Complex.I • L ⟨Y t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩)) t at h
  rw [map_smul, he] at h
  exact h

theorem carryMaterialClock_complement_origin : carryMaterialClockComplementState 0 = 0 :=
  carryMaterialCentralComplement_center

theorem carryMaterialClock_action_origin : carryMaterialClockComplementAction 0 = 0 := by
  have h : carryMaterialClockDomainComplement
      ⟨Y 0, baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0⟩ = 0 := by
    apply Subtype.ext
    exact carryMaterialCentralComplement_center
  change Q (completedBoundaryTransportedClock.toFun _) = 0
  rw [h, map_zero, map_zero]

theorem carryMaterialClock_complement_origin_derivative :
    HasDerivAt carryMaterialClockComplementState (-Complex.I • carryMaterialClockCentralForcing) 0 := by
  simpa only [carryMaterialClock_action_origin, carryMaterialClock_central_coefficient_zero,
    one_smul, zero_add] using carryMaterialClock_complement_derivative 0

def carryMaterialCentralPairProjection (x : MaterialCarrier × MaterialCarrier) :
    MaterialCarrier × MaterialCarrier := (P x.1, P x.2)

def carryMaterialCentralPairComplement (x : MaterialCarrier × MaterialCarrier) :
    MaterialCarrier × MaterialCarrier := (Q x.1, Q x.2)

theorem carryMaterialClock_pair_green_split (x y : MaterialCarrier × MaterialCarrier) :
    carryMaterialPairGreen x y =
      carryMaterialPairGreen (carryMaterialCentralPairProjection x) (carryMaterialCentralPairProjection y) +
      carryMaterialPairGreen (carryMaterialCentralPairComplement x) (carryMaterialCentralPairComplement y) := by
  have h1 := carryMaterialCentral_full_pairing x.2 y.1
  have h2 := carryMaterialCentral_full_pairing x.1 y.2
  simp only [carryMaterialPairGreen, carryMaterialCentralPairProjection,
    carryMaterialCentralPairComplement]
  linear_combination h1-h2

/-- This is only the compressed component of the existing companion pair.
The forcing pair below must be retained beside it. -/
def carryMaterialClockCompressedPair (t : ℝ) : MaterialCarrier × MaterialCarrier :=
  carryMaterialPairDressing t
    (Complex.I • carryMaterialClockComplementAction t,
      (2 : ℂ) • carryMaterialClockComplementState t)

def carryMaterialClockForcingScalar (t : ℝ) : ℂ :=
  Complex.I*D t*carryMaterialClockCentralCoefficient (Y t)

def carryMaterialClockForcingPair (t : ℝ) : MaterialCarrier × MaterialCarrier :=
  (carryMaterialClockForcingScalar t • carryMaterialClockCentralForcing, 0)

theorem carryMaterialClock_companion_complement (t : ℝ) :
    carryMaterialCentralPairComplement (carryMaterialCompanionValuePair t) =
      carryMaterialClockCompressedPair t + carryMaterialClockForcingPair t := by
  have he : Q (L ⟨Y t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩) =
      carryMaterialClockComplementAction t +
        carryMaterialClockCentralCoefficient (Y t) • carryMaterialClockCentralForcing :=
    carryMaterialClock_complement_forced _
  rw [carryMaterialCompanionValuePair_dressing]
  apply Prod.ext
  · simp only [carryMaterialCentralPairComplement, carryMaterialPairDressing,
      carryMaterialClockCompressedPair, carryMaterialClockForcingPair,
      carryMaterialClockForcingScalar, Prod.fst_add, map_sub, map_smul,
      carryMaterialClockComplementState]
    rw [he, smul_add]
    module
  · simp only [carryMaterialCentralPairComplement, carryMaterialPairDressing,
      carryMaterialClockCompressedPair, carryMaterialClockForcingPair,
      Prod.snd_add, map_smul, carryMaterialClockComplementState, add_zero]

theorem carryMaterialClock_compressed_pair_origin : carryMaterialClockCompressedPair 0 = 0 := by
  simp [carryMaterialClockCompressedPair, carryMaterialClock_action_origin,
    carryMaterialClock_complement_origin, carryMaterialPairDressing]

theorem carryMaterialClock_forcing_pair_self_green (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialClockForcingPair t) (carryMaterialClockForcingPair u) = 0 := by
  simp [carryMaterialPairGreen, carryMaterialClockForcingPair]

private theorem pair_green_add (x a y b : MaterialCarrier × MaterialCarrier) :
    carryMaterialPairGreen (x+a) (y+b) = carryMaterialPairGreen x y +
      carryMaterialPairGreen x b + carryMaterialPairGreen a y + carryMaterialPairGreen a b := by
  simp only [carryMaterialPairGreen, Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]
  ring

/-- The complete dressing connection is retained in the compressed block. -/
theorem carryMaterialClock_compressed_green (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialClockCompressedPair t) (carryMaterialClockCompressedPair u) =
      2*Complex.I*conj (D t)*D u*
        (inner ℂ (carryMaterialClockComplementState t) (carryMaterialClockComplementAction u) +
          inner ℂ (carryMaterialClockComplementAction t) (carryMaterialClockComplementState u)) +
      2*(conj (deriv D t)*D u-conj (D t)*deriv D u)*
        inner ℂ (carryMaterialClockComplementState t) (carryMaterialClockComplementState u) := by
  rw [carryMaterialClockCompressedPair, carryMaterialClockCompressedPair,
    carryMaterialPairDressing_green]
  simp only [carryMaterialPairGreen, inner_smul_left, inner_smul_right, map_ofNat,
    Complex.conj_I]
  ring

/-- Both ordered forcing crosses, before any diagonal or energy projection. -/
theorem carryMaterialClock_complement_green (t u : ℝ) :
    carryMaterialPairGreen
      (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair t))
      (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair u)) =
      carryMaterialPairGreen (carryMaterialClockCompressedPair t) (carryMaterialClockCompressedPair u) +
      2*Complex.I*conj (D t)*D u*
        (carryMaterialClockCentralCoefficient (Y u)*
            inner ℂ (carryMaterialClockComplementState t) carryMaterialClockCentralForcing +
          conj (carryMaterialClockCentralCoefficient (Y t))*
            inner ℂ carryMaterialClockCentralForcing (carryMaterialClockComplementState u)) := by
  rw [carryMaterialClock_companion_complement t, carryMaterialClock_companion_complement u,
    pair_green_add, carryMaterialClock_forcing_pair_self_green]
  simp only [carryMaterialPairGreen, carryMaterialClockCompressedPair,
    carryMaterialPairDressing, carryMaterialClockForcingPair, carryMaterialClockForcingScalar,
    inner_zero_left, inner_zero_right, sub_zero, zero_sub, inner_smul_left,
    inner_smul_right, map_mul, map_ofNat, Complex.conj_I]
  ring

/-- A mixed central row sees the nonzero forcing, although its diagonal at
the origin vanishes. No division by u or u-t is used. -/
theorem carryMaterialClock_complement_green_origin (u : ℝ) :
    carryMaterialPairGreen
      (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair 0))
      (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair u)) =
      2*Complex.I*conj (D 0)*D u*
        inner ℂ carryMaterialClockCentralForcing (carryMaterialClockComplementState u) := by
  rw [carryMaterialClock_complement_green, carryMaterialClock_compressed_pair_origin]
  simp only [carryMaterialPairGreen, Prod.fst_zero, Prod.snd_zero, inner_zero_left,
    carryMaterialClock_complement_origin, carryMaterialClock_central_coefficient_zero,
    map_one, one_mul, mul_zero, zero_add, sub_self]

theorem carryMaterialClock_complement_green_origin_derivative :
    HasDerivAt (fun u : ℝ => carryMaterialPairGreen
      (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair 0))
      (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair u)))
      ((2*‖D 0‖^2*‖carryMaterialClockCentralForcing‖^2 : ℝ) : ℂ) 0 := by
  have hinner := (hasDerivAt_const (0 : ℝ) carryMaterialClockCentralForcing).inner ℂ
    carryMaterialClock_complement_origin_derivative
  have hinner' : HasDerivAt
      (fun u => inner ℂ carryMaterialClockCentralForcing (carryMaterialClockComplementState u))
      (-Complex.I*((‖carryMaterialClockCentralForcing‖^2 : ℝ) : ℂ)) 0 := by
    apply hinner.congr_deriv
    rw [carryMaterialClock_complement_origin, inner_zero_left, add_zero,
      inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h := (((baseTwoCanonicalDressingScalar_analyticAt 0).differentiableAt.hasDerivAt).mul hinner').const_mul
    (2*Complex.I*conj (D 0))
  have hi : Complex.I^2 = -1 := Complex.I_sq
  have hd : conj (D 0)*D 0 = ((‖D 0‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => by
    simpa only [Pi.mul_apply, mul_assoc] using carryMaterialClock_complement_green_origin u))).congr_deriv
  rw [carryMaterialClock_complement_origin, inner_zero_right, mul_zero, zero_add]
  push_cast at hd ⊢
  linear_combination -2*‖carryMaterialClockCentralForcing‖^2*hi*conj (D 0)*D 0 +
    2*‖carryMaterialClockCentralForcing‖^2*hd

theorem carryMaterialClock_complement_green_origin_derivative_pos :
    0 < (deriv (fun u : ℝ => carryMaterialPairGreen
      (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair 0))
      (carryMaterialCentralPairComplement (carryMaterialCompanionValuePair u))) 0).re := by
  rw [carryMaterialClock_complement_green_origin_derivative.deriv, Complex.ofReal_re]
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
    (baseTwoCanonicalDressingScalar_ne_zero 0))))
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr carryMaterialClock_forcing_nonzero))

theorem carryMaterialClock_pair_projection_reduction (t : ℝ) (x : MaterialCarrier × MaterialCarrier) :
    carryMaterialCentralPairProjection (carryMaterialPairReduction t x) =
      carryMaterialPairReduction t (carryMaterialCentralPairProjection x) := by
  apply Prod.ext <;> simp [carryMaterialCentralPairProjection, carryMaterialPairReduction]

theorem carryMaterialClock_pair_complement_reduction (t : ℝ) (x : MaterialCarrier × MaterialCarrier) :
    carryMaterialCentralPairComplement (carryMaterialPairReduction t x) =
      carryMaterialPairReduction t (carryMaterialCentralPairComplement x) := by
  apply Prod.ext <;> simp [carryMaterialCentralPairComplement, carryMaterialPairReduction]

theorem carryMaterialClock_reduced_complement (t : ℝ) :
    carryMaterialCentralPairComplement (carryMaterialReducedCompanionPair t) =
      carryMaterialPairReduction t (carryMaterialClockCompressedPair t) +
        carryMaterialPairReduction t (carryMaterialClockForcingPair t) := by
  rw [carryMaterialReducedCompanionPair, carryMaterialClock_pair_complement_reduction,
    carryMaterialClock_companion_complement, map_add]

/-- The forcing/forcing Green term becomes a NONZERO signed term after
projective reduction. Its vanishing before reduction cannot justify deletion. -/
theorem carryMaterialClock_reduced_forcing_green (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
      (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) =
      -((carryMaterialResponseScale*(u-t) : ℝ) : ℂ)*
        conj (carryMaterialClockForcingScalar t)*carryMaterialClockForcingScalar u*
          inner ℂ carryMaterialClockCentralForcing carryMaterialClockCentralForcing := by
  rw [carryMaterialPairReduction_green, carryMaterialClock_forcing_pair_self_green]
  simp only [mul_zero, zero_sub, carryMaterialClockForcingPair,
    inner_smul_left, inner_smul_right]
  ring

/-- Complete central/complement and reduced-forcing ledger. Every physical
component is constructed before applying the canonical scalar readout. -/
theorem carryMaterialClock_reduced_green_ledger (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u) =
      carryMaterialPairGreen
        (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t))
        (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair u)) +
      carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
        (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) +
      carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
        (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) +
      carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
        (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) +
      carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
        (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) := by
  rw [carryMaterialClock_pair_green_split, carryMaterialClock_reduced_complement t,
    carryMaterialClock_reduced_complement u, pair_green_add]
  ring

end
end GeometryOfNumbers.Analysis
