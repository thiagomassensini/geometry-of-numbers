import GeometryOfNumbers.Analysis.BaseTwoNormalizedCenterSector

/-! Incoming causal center reconstruction and outgoing leg return have
separate geometric roles. The standard adjoint is tested, not assumed. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open private zeroSeedPhysicalInput zeroSeedPhysicalInput_norm from
  GeometryOfNumbers.Analysis.BaseTwoBoundedPhysicalCenterCoupling

private theorem legSynthesis_single (k : ℕ) :
    baseTwoCenterLegSynthesis (lp.single 2 k 1) =
      lp.single 2 (k,0) (baseTwoCenterLegUnit k 0 : ℂ) +
      lp.single 2 (k,1) (baseTwoCenterLegUnit k 1 : ℂ) := by
  apply lp.ext
  funext e
  rcases e with ⟨j,a⟩
  by_cases h : j = k
  · subst j
    fin_cases a <;> simp [baseTwoCenterLegSynthesis_apply,lp.single_apply]
  · simp [baseTwoCenterLegSynthesis_apply,lp.single_apply,h]

/-- Standard Hilbert adjoint: the real geometric unit coefficients need no phase. -/
theorem baseTwoCenterLegSynthesis_adjoint_apply (x : PhysicalEdgeL2) (k : ℕ) :
    baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint x k =
      ∑ a : Fin 2, (baseTwoCenterLegUnit k a : ℂ) * x (k,a) := by
  have h := baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint_inner_right
    (lp.single 2 k 1) x
  rw [lp.inner_single_left] at h
  change inner ℂ (1:ℂ) (baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint x k) =
    inner ℂ (baseTwoCenterLegSynthesis (lp.single 2 k 1)) x at h
  rw [legSynthesis_single,inner_add_left,lp.inner_single_left,lp.inner_single_left] at h
  rw [show (Finset.univ : Finset (Fin 2)) = {0,1} by decide]
  simpa only [RCLike.inner_apply,map_one,mul_one,one_mul,Complex.conj_ofReal,
    Finset.sum_insert,Finset.sum_singleton,Finset.mem_singleton,
    show (0:Fin 2) ≠ 1 by decide,not_false_eq_true,mul_comm] using h

/-- Reuses the generic adjoint identity of a LinearIsometry. -/
theorem baseTwoCenterLegSynthesis_adjoint_comp_self :
    baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint.comp
      baseTwoCenterLegSynthesis.toContinuousLinearMap = ContinuousLinearMap.id ℂ BaseTwoCenterL2 :=
  baseTwoCenterLegSynthesis.adjoint_comp_self

/-- Public name for the already constructed standard physical zero-seed input. -/
def baseTwoPhysicalToSeeded : PhysicalEdgeL2 →L[ℂ] BaseTwoSeededMaterialHilbert :=
  zeroSeedPhysicalInput

@[simp] theorem baseTwoPhysicalToSeeded_apply (x : PhysicalEdgeL2) :
    baseTwoPhysicalToSeeded x = WithLp.toLp 2 (0,baseTwoPhysicalEdgeEmbedding x) := rfl

theorem baseTwoPhysicalToSeeded_norm (x : PhysicalEdgeL2) :
    ‖baseTwoPhysicalToSeeded x‖ = ‖x‖ := zeroSeedPhysicalInput_norm x

/-- Incoming physical center reconstruction; not defined from an adjoint. -/
def baseTwoPhysicalCenterReconstruction : PhysicalEdgeL2 →L[ℂ] BaseTwoCenterL2 :=
  baseTwoNormalizedCenterReconstruction.comp baseTwoPhysicalToSeeded

@[simp] theorem baseTwoPhysicalCenterReconstruction_apply (x : PhysicalEdgeL2) (k : ℕ) :
    baseTwoPhysicalCenterReconstruction x k =
      (baseTwoCenterGapNorm k:ℂ) *
        baseTwoCenterReconstruction (WithLp.toLp 2 (0,baseTwoPhysicalEdgeEmbedding x)) k := rfl

theorem baseTwoPhysicalCenterSelfCoupling_factorization :
    baseTwoPhysicalCenterSelfCoupling =
      baseTwoCenterLegSynthesis.toContinuousLinearMap.comp baseTwoPhysicalCenterReconstruction := by
  ext x e
  change baseTwoCenterCouplingOperator (baseTwoPhysicalToSeeded x) e =
    baseTwoCenterLegSynthesis (baseTwoNormalizedCenterReconstruction (baseTwoPhysicalToSeeded x)) e
  exact congrArg (fun A : BaseTwoSeededMaterialHilbert →L[ℂ] PhysicalEdgeL2 =>
    A (baseTwoPhysicalToSeeded x) e) baseTwoCenterCoupling_factorization

/-- The right edge is not in the causal prefix preceding its own center. -/
theorem baseTwoPhysicalCenterReconstruction_deltaRight_zero :
    baseTwoPhysicalCenterReconstruction baseTwoPhysicalCenterDeltaRight 0 = 0 := by
  have h := congrArg (fun A : PhysicalEdgeL2 →L[ℂ] PhysicalEdgeL2 =>
    A baseTwoPhysicalCenterDeltaRight (0,1)) baseTwoPhysicalCenterSelfCoupling_factorization
  change baseTwoPhysicalCenterSelfCoupling baseTwoPhysicalCenterDeltaRight (0,1) =
    (baseTwoCenterLegUnit 0 1:ℂ) *
      baseTwoPhysicalCenterReconstruction baseTwoPhysicalCenterDeltaRight 0 at h
  rw [baseTwoPhysicalCenterSelfCoupling_apply,
    baseTwoPhysicalCenterSelfCouplingRaw_deltaRight_first_cell] at h
  have hu : (baseTwoCenterLegUnit 0 1:ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact ne_of_gt (div_pos (baseTwoCenterLogGap_right_pos 0) (baseTwoCenterGapNorm_pos 0))
  exact (mul_eq_zero.mp h.symm).resolve_left hu

/-- Outgoing right-leg return remains nonzero at that same center. -/
theorem baseTwoCenterLegSynthesis_adjoint_deltaRight :
    baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint baseTwoPhysicalCenterDeltaRight 0 =
      (baseTwoCenterLegUnit 0 1:ℂ) := by
  rw [baseTwoCenterLegSynthesis_adjoint_apply]
  simp [baseTwoPhysicalCenterDeltaRight,lp.single_apply,Fin.sum_univ_succ]

/-- Literal first-cell log-gap ratio, with the geometric normalization. -/
theorem baseTwoCenterLegSynthesis_adjoint_deltaRight_explicit :
    baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint baseTwoPhysicalCenterDeltaRight 0 =
      ((Real.log 5 - Real.log 4) /
        Real.sqrt ((Real.log 4 - Real.log 3)^2 + (Real.log 5 - Real.log 4)^2) : ℝ) := by
  rw [baseTwoCenterLegSynthesis_adjoint_deltaRight]
  rfl

theorem baseTwoCenterLegSynthesis_adjoint_deltaRight_ne_zero :
    baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint baseTwoPhysicalCenterDeltaRight 0 ≠ 0 := by
  rw [baseTwoCenterLegSynthesis_adjoint_deltaRight]
  exact Complex.ofReal_ne_zero.mpr
    (ne_of_gt (div_pos (baseTwoCenterLogGap_right_pos 0) (baseTwoCenterGapNorm_pos 0)))

/-- Incoming causal reconstruction is not outgoing synthesis's Hilbert adjoint. -/
theorem baseTwoPhysicalCenterReconstruction_ne_legSynthesis_adjoint :
    baseTwoPhysicalCenterReconstruction ≠ baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint := by
  intro h
  have hz := baseTwoPhysicalCenterReconstruction_deltaRight_zero
  rw [h] at hz
  exact baseTwoCenterLegSynthesis_adjoint_deltaRight_ne_zero hz

end GeometryOfNumbers.Analysis.BaseTwoCompletion
