import GeometryOfNumbers.Analysis.BaseTwoCenterSectorAdjointMismatch
import GeometryOfNumbers.Analysis.SymmetricKrylovHankel

/-! Separate incoming causal reconstruction from outgoing leg return.
This block is made only from existing bounded geometric maps. It is not
identified with the completed material clock or with a moment generator. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- Standard products, with distinct copies for incoming and outgoing center data. -/
abbrev BaseTwoSeparatedCenterHilbert :=
  WithLp 2 (PhysicalEdgeL2 × WithLp 2 (BaseTwoCenterL2 × BaseTwoCenterL2))

private abbrev physical : BaseTwoSeparatedCenterHilbert →L[ℂ] PhysicalEdgeL2 :=
  WithLp.fstL 2 ℂ PhysicalEdgeL2 (WithLp 2 (BaseTwoCenterL2 × BaseTwoCenterL2))
private abbrev incoming : BaseTwoSeparatedCenterHilbert →L[ℂ] BaseTwoCenterL2 :=
  (WithLp.fstL 2 ℂ BaseTwoCenterL2 BaseTwoCenterL2).comp
    (WithLp.sndL 2 ℂ PhysicalEdgeL2 (WithLp 2 (BaseTwoCenterL2 × BaseTwoCenterL2)))
private abbrev outgoing : BaseTwoSeparatedCenterHilbert →L[ℂ] BaseTwoCenterL2 :=
  (WithLp.sndL 2 ℂ BaseTwoCenterL2 BaseTwoCenterL2).comp
    (WithLp.sndL 2 ℂ PhysicalEdgeL2 (WithLp 2 (BaseTwoCenterL2 × BaseTwoCenterL2)))

/-- Bounded by composition, with no fitted norm or free matrix coefficient. -/
def baseTwoSeparatedCenterBlock :
    BaseTwoSeparatedCenterHilbert →L[ℂ] BaseTwoSeparatedCenterHilbert :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ PhysicalEdgeL2
    (WithLp 2 (BaseTwoCenterL2 × BaseTwoCenterL2))).symm.toContinuousLinearMap.comp
    (((baseTwoPhysicalCenterReconstruction.adjoint.comp incoming) +
      (baseTwoCenterLegSynthesis.toContinuousLinearMap.comp outgoing)).prod
      ((WithLp.prodContinuousLinearEquiv 2 ℂ BaseTwoCenterL2 BaseTwoCenterL2).symm.toContinuousLinearMap.comp
        ((baseTwoPhysicalCenterReconstruction.comp physical).prod
          (baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint.comp physical))))

@[simp] theorem baseTwoSeparatedCenterBlock_apply (x : BaseTwoSeparatedCenterHilbert) :
    baseTwoSeparatedCenterBlock x = WithLp.toLp 2
      (baseTwoPhysicalCenterReconstruction.adjoint x.snd.fst +
        baseTwoCenterLegSynthesis x.snd.snd,
       WithLp.toLp 2 (baseTwoPhysicalCenterReconstruction x.fst,
         baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint x.fst)) := rfl

/-- Unlike the excluded single-center block, this keeps T and S.adjoint distinct. -/
theorem baseTwoSeparatedCenterBlock_symmetric :
    baseTwoSeparatedCenterBlock.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ (baseTwoSeparatedCenterBlock x) y = inner ℂ x (baseTwoSeparatedCenterBlock y)
  rw [baseTwoSeparatedCenterBlock_apply,baseTwoSeparatedCenterBlock_apply]
  simp only [WithLp.prod_inner_apply,
    inner_add_left,inner_add_right]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  change (inner ℂ x.snd.fst (baseTwoPhysicalCenterReconstruction y.fst) +
    inner ℂ (baseTwoCenterLegSynthesis x.snd.snd) y.fst) +
    (inner ℂ (baseTwoPhysicalCenterReconstruction x.fst) y.snd.fst +
     inner ℂ x.fst (baseTwoCenterLegSynthesis y.snd.snd)) =
    (inner ℂ (baseTwoPhysicalCenterReconstruction x.fst) y.snd.fst +
     inner ℂ x.fst (baseTwoCenterLegSynthesis y.snd.snd)) +
    (inner ℂ x.snd.fst (baseTwoPhysicalCenterReconstruction y.fst) +
     inner ℂ (baseTwoCenterLegSynthesis x.snd.snd) y.fst)
  ring

/-- Incoming and outgoing observations remain different vector coordinates. -/
def baseTwoCenterRoleObservation :
    PhysicalEdgeL2 →L[ℂ] WithLp 2 (BaseTwoCenterL2 × BaseTwoCenterL2) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ BaseTwoCenterL2 BaseTwoCenterL2).symm.toContinuousLinearMap.comp
    (baseTwoPhysicalCenterReconstruction.prod
      baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint)

@[simp] theorem baseTwoCenterRoleObservation_apply (p : PhysicalEdgeL2) :
    baseTwoCenterRoleObservation p = WithLp.toLp 2
      (baseTwoPhysicalCenterReconstruction p,
        baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint p) := rfl

/-- The separated block sends physical data to both geometric center roles. -/
theorem baseTwoSeparatedCenterBlock_physical (p : PhysicalEdgeL2) :
    baseTwoSeparatedCenterBlock (WithLp.toLp 2 (p,0)) =
      WithLp.toLp 2 (0,baseTwoCenterRoleObservation p) := by
  rw [baseTwoSeparatedCenterBlock_apply,baseTwoCenterRoleObservation_apply]
  simp

/-- Exact nonnegative observation energy; no moment value is used. -/
theorem baseTwoCenterRoleObservation_energy (p : PhysicalEdgeL2) :
    ‖baseTwoCenterRoleObservation p‖^2 =
      ‖baseTwoPhysicalCenterReconstruction p‖^2 +
        ‖baseTwoCenterLegSynthesis.toContinuousLinearMap.adjoint p‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

/-- All index sums for this independently constructed symmetric block follow
from the existing abstract theorem. This does not calibrate canonical moments. -/
theorem baseTwoSeparatedCenterKrylov_inner_add (v : BaseTwoSeparatedCenterHilbert)
    (i j : ℕ) :
    inner ℂ ((baseTwoSeparatedCenterBlock.toLinearMap^i) v)
      ((baseTwoSeparatedCenterBlock.toLinearMap^j) v) =
    inner ℂ v ((baseTwoSeparatedCenterBlock.toLinearMap^(i+j)) v) :=
  symmetricKrylov_inner_add _ baseTwoSeparatedCenterBlock_symmetric v i j

/-- A literal first-column gate, explicitly conditional. No vector is defined
from moments, and the condition is not claimed for any completed state here. -/
theorem baseTwoSeparatedCenter_firstColumn_implies_evenKernel
    (v : BaseTwoSeparatedCenterHilbert)
    (hfirst : ∀ r : ℕ, baseTwoCanonicalMomentSequence r =
      (inner ℂ v ((baseTwoSeparatedCenterBlock.toLinearMap^(2*r)) v)).re)
    (i j : ℕ) :
    baseTwoCanonicalMomentSequence (i+j) =
      (inner ℂ ((baseTwoSeparatedCenterBlock.toLinearMap^(2*i)) v)
        ((baseTwoSeparatedCenterBlock.toLinearMap^(2*j)) v)).re := by
  rw [baseTwoSeparatedCenterKrylov_inner_add]
  rw [← Nat.mul_add]
  exact hfirst (i+j)

end GeometryOfNumbers.Analysis.BaseTwoCompletion
