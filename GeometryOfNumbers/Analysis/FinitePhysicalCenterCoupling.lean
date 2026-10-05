import GeometryOfNumbers.Analysis.FiniteSeedGradientClock
import GeometryOfNumbers.Analysis.BaseTwoPhysicalCenterClockDefect

/-! # First-cell physical self-coupling in the standard Hilbert metric
The center is reconstructed from seed and preceding material edges. The right
edge is absent from this prefix. This excludes only symmetry of this diagonal
physical block, not a completed clock or a larger geometric realization.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open NativeMaterialClock

/-- The two physical coordinates of the existing first base-two cell. -/
abbrev FiniteBaseTwoPhysicalCarrier := FiniteRealSpectralHilbert 2

/-- Zero seed/residual, with the two physical coordinates at material edges 2,3. -/
def finitePhysicalCenterInput :
    FiniteBaseTwoPhysicalCarrier →ₗ[ℂ] FiniteSeedGradientCarrier 4 where
  toFun x := WithLp.toLp 2 (0, WithLp.toLp 2
    (fun j : Fin 4 => if j.val = baseTwoCellLeftEdge 0 then x 0
      else if j.val = baseTwoCellRightEdge 0 then x 1 else 0))
  map_add' x y := by
    apply WithLp.ofLp_injective 2; apply Prod.ext
    · simp
    · ext j; fin_cases j <;> simp
  map_smul' a x := by
    apply WithLp.ofLp_injective 2; apply Prod.ext
    · simp
    · ext j; fin_cases j <;> simp

/-- Finite reconstruction preceding the same geometric center c=4. -/
def finiteOneCellCenterReconstruction : FiniteSeedGradientCarrier 4 →ₗ[ℂ] ℂ where
  toFun y := y.fst + finiteGradientPrefix y.snd (baseTwoCenter 0 - 1)
  map_add' x y := by simp [finiteGradientPrefix, Finset.sum_add_distrib]; ring
  map_smul' a x := by simp [finiteGradientPrefix, Finset.mul_sum, mul_add]

def finiteOneCellCenterLogGap (a : Fin 2) : ℝ :=
  if a.val = 0 then Real.log (baseTwoCenter 0 : ℝ) -
      Real.log ((baseTwoCenter 0 - 1 : ℕ) : ℝ)
    else Real.log ((baseTwoCenter 0 + 1 : ℕ) : ℝ) - Real.log (baseTwoCenter 0 : ℝ)

/-- Geometric center reconstruction followed by left/right log-gap synthesis. -/
def finiteOneCellCenterCoupling :
    FiniteSeedGradientCarrier 4 →ₗ[ℂ] FiniteBaseTwoPhysicalCarrier where
  toFun y := WithLp.toLp 2 (fun a =>
    (finiteOneCellCenterLogGap a : ℂ) * finiteOneCellCenterReconstruction y)
  map_add' x y := by ext a; simp [map_add, mul_add]
  map_smul' a x := by ext j; simp [map_smul]; ring

def finitePhysicalCenterSelfCoupling : Module.End ℂ FiniteBaseTwoPhysicalCarrier :=
  finiteOneCellCenterCoupling.comp finitePhysicalCenterInput

def finitePhysicalCenterDeltaLeft : FiniteBaseTwoPhysicalCarrier :=
  finiteRealSpectralBasisVector 2 0

def finitePhysicalCenterDeltaRight : FiniteBaseTwoPhysicalCarrier :=
  finiteRealSpectralBasisVector 2 1

theorem finiteOneCellCenterReconstruction_physical (x : FiniteBaseTwoPhysicalCarrier) :
    finiteOneCellCenterReconstruction (finitePhysicalCenterInput x) = x 0 := by
  simp [finiteOneCellCenterReconstruction, finitePhysicalCenterInput,
    finiteGradientPrefix, Finset.sum_filter, Fin.sum_univ_succ, baseTwo_center_eq]

theorem finiteOneCellCenterReconstruction_deltaLeft :
    finiteOneCellCenterReconstruction (finitePhysicalCenterInput finitePhysicalCenterDeltaLeft) = 1 := by
  rw [finiteOneCellCenterReconstruction_physical]
  simp [finitePhysicalCenterDeltaLeft, finiteRealSpectralBasisVector]

theorem finiteOneCellCenterReconstruction_deltaRight :
    finiteOneCellCenterReconstruction (finitePhysicalCenterInput finitePhysicalCenterDeltaRight) = 0 := by
  rw [finiteOneCellCenterReconstruction_physical]
  simp [finitePhysicalCenterDeltaRight, finiteRealSpectralBasisVector]

/-- Matrix on {L0,R0}: [[log4-log3,0],[log5-log4,0]]. -/
theorem finitePhysicalCenterSelfCoupling_apply (x : FiniteBaseTwoPhysicalCarrier) (a : Fin 2) :
    finitePhysicalCenterSelfCoupling x a = (finiteOneCellCenterLogGap a : ℂ) * x 0 := by
  change (finiteOneCellCenterLogGap a : ℂ) *
    finiteOneCellCenterReconstruction (finitePhysicalCenterInput x) = _
  rw [finiteOneCellCenterReconstruction_physical]

theorem finitePhysicalCenterSelfCoupling_deltaLeft (a : Fin 2) :
    finitePhysicalCenterSelfCoupling finitePhysicalCenterDeltaLeft a =
      (finiteOneCellCenterLogGap a : ℂ) := by
  rw [finitePhysicalCenterSelfCoupling_apply]
  simp [finitePhysicalCenterDeltaLeft, finiteRealSpectralBasisVector]

theorem finitePhysicalCenterSelfCoupling_deltaRight :
    finitePhysicalCenterSelfCoupling finitePhysicalCenterDeltaRight = 0 := by
  ext a
  rw [finitePhysicalCenterSelfCoupling_apply]
  simp [finitePhysicalCenterDeltaRight, finiteRealSpectralBasisVector]

theorem finitePhysicalCenterCoupling_inner_left_right :
    inner ℂ (finitePhysicalCenterSelfCoupling finitePhysicalCenterDeltaLeft)
      finitePhysicalCenterDeltaRight = (Real.log 5 - Real.log 4 : ℝ) := by
  simp [PiLp.inner_apply, finitePhysicalCenterSelfCoupling_deltaLeft,
    finitePhysicalCenterDeltaRight, finiteRealSpectralBasisVector, PiLp.single_apply,
    RCLike.inner_apply, finiteOneCellCenterLogGap, baseTwo_center_eq]

theorem finitePhysicalCenterCoupling_inner_right_image :
    inner ℂ finitePhysicalCenterDeltaLeft
      (finitePhysicalCenterSelfCoupling finitePhysicalCenterDeltaRight) = 0 := by
  rw [finitePhysicalCenterSelfCoupling_deltaRight, inner_zero_right]

/-- Strict monotonicity of log, with no numerical estimate, witnesses asymmetry. -/
theorem finitePhysicalCenterCoupling_not_symmetric :
    ¬ finitePhysicalCenterSelfCoupling.IsSymmetric := by
  intro h
  have he := h finitePhysicalCenterDeltaLeft finitePhysicalCenterDeltaRight
  rw [finitePhysicalCenterCoupling_inner_left_right,
    finitePhysicalCenterCoupling_inner_right_image] at he
  have hp : 0 < Real.log 5 - Real.log 4 :=
    sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))
  exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hp)) he

end GeometryOfNumbers.Analysis.BaseTwoCompletion
