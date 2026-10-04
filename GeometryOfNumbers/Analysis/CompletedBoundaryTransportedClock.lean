import GeometryOfNumbers.Analysis.CompletedMaterialGradientStrongClock
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # The partial transported material clock of the completed boundary state

The domain retains the geometric boundary graph and requires both a Hilbert
clock interior and a convergent whole-cell clock return. No bounded or symmetric
extension to the full independent product is asserted.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal InnerProduct
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

def completedBoundaryClockCoordinates :
    BaseTwoCompletedBoundaryHilbertCarrier →ₗ[ℂ] (ℕ → ℂ) where
  toFun y := baseTwoCompletedBoundaryHilbertClockCoordinate y
  map_add' x y := by
    funext j
    simp only [baseTwoCompletedBoundaryHilbertClockCoordinate, WithLp.add_fst, WithLp.add_snd,
      lp.coeFn_add, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' a x := by
    funext j
    simp only [baseTwoCompletedBoundaryHilbertClockCoordinate, WithLp.smul_fst,
      WithLp.smul_snd, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

def completedBoundaryCellReturnCoordinates :
    BaseTwoCompletedBoundaryHilbertCarrier →ₗ[ℂ] (ℕ → ℂ) where
  toFun y k := y.snd.fst (baseTwoCellRightEdge k) - y.snd.fst (baseTwoCellLeftEdge k)
  map_add' x y := by funext k; simp; ring
  map_smul' a x := by funext k; simp [mul_sub]

def completedBoundaryClockCellCoordinates :
    BaseTwoCompletedBoundaryHilbertCarrier →ₗ[ℂ] (ℕ → ℂ) where
  toFun y k := completedBoundaryClockCoordinates y (baseTwoCellRightEdge k) -
    completedBoundaryClockCoordinates y (baseTwoCellLeftEdge k)
  map_add' x y := by funext k; simp [sub_add_sub_comm]
  map_smul' a x := by funext k; simp [mul_sub]

/-- Natural graph domain: the stored return is the actual whole-cell sum,
the triangular clock interior is in ℓ², and its cell return is summable. -/
def completedBoundaryTransportedClockDomain : Submodule ℂ BaseTwoCompletedBoundaryHilbertCarrier where
  carrier := { y | HasSum (completedBoundaryCellReturnCoordinates y) y.snd.snd ∧
    Memℓp (completedBoundaryClockCoordinates y) 2 ∧
    Summable (completedBoundaryClockCellCoordinates y) }
  zero_mem' := by
    change HasSum (completedBoundaryCellReturnCoordinates 0) (WithLp.snd (WithLp.snd (0 : BaseTwoCompletedBoundaryHilbertCarrier))) ∧ _
    simpa only [map_zero, WithLp.zero_snd] using
      (show HasSum (0 : ℕ → ℂ) 0 ∧ Memℓp (0 : ℕ → ℂ) 2 ∧ Summable (0 : ℕ → ℂ) from
        ⟨hasSum_zero, zero_memℓp, summable_zero⟩)
  add_mem' := by
    intro x y hx hy
    exact ⟨by simpa only [map_add, WithLp.add_snd, Pi.add_def] using hx.1.add hy.1,
      by simpa only [map_add] using hx.2.1.add hy.2.1,
      by simpa only [map_add, Pi.add_def] using hx.2.2.add hy.2.2⟩
  smul_mem' := by
    intro a y hy
    exact ⟨by simpa only [map_smul, WithLp.smul_snd, Pi.smul_def] using hy.1.const_smul a,
      by simpa only [map_smul] using hy.2.1.const_smul a,
      by simpa only [map_smul, Pi.smul_def] using hy.2.2.const_smul a⟩

/-- The transported clock is defined only on its derived graph domain. -/
def completedBoundaryTransportedClock :
    BaseTwoCompletedBoundaryHilbertCarrier →ₗ.[ℂ] BaseTwoCompletedBoundaryHilbertCarrier where
  domain := completedBoundaryTransportedClockDomain
  toFun :=
    { toFun := fun y => WithLp.toLp 2 (0, WithLp.toLp 2
        ((⟨completedBoundaryClockCoordinates y, y.property.2.1⟩ : MaterialEdgeL2),
          ∑' k, completedBoundaryClockCellCoordinates y k))
      map_add' := by
        intro x y
        apply (WithLp.ofLp_injective 2); apply Prod.ext
        · simp
        · apply (WithLp.ofLp_injective 2); apply Prod.ext
          · apply lp.ext
            exact map_add completedBoundaryClockCoordinates x.val y.val
          · change (∑' k, completedBoundaryClockCellCoordinates (x.val+y.val) k) = _
            simp only [map_add, Pi.add_apply]
            exact x.property.2.2.tsum_add y.property.2.2
      map_smul' := by
        intro a y
        apply (WithLp.ofLp_injective 2); apply Prod.ext
        · simp
        · apply (WithLp.ofLp_injective 2); apply Prod.ext
          · apply lp.ext
            exact map_smul completedBoundaryClockCoordinates a y.val
          · change (∑' k, completedBoundaryClockCellCoordinates (a • y.val) k) = _
            simp only [map_smul, Pi.smul_apply]
            exact y.property.2.2.tsum_const_smul a }

@[simp] theorem completedBoundaryTransportedClock_seed
    (y : completedBoundaryTransportedClock.domain) :
    (completedBoundaryTransportedClock y).fst = 0 := rfl

@[simp] theorem completedBoundaryTransportedClock_interior
    (y : completedBoundaryTransportedClock.domain) (j : ℕ) :
    (completedBoundaryTransportedClock y).snd.fst j =
      baseTwoCompletedBoundaryHilbertClockCoordinate y.val j := rfl

@[simp] theorem completedBoundaryTransportedClock_boundary
    (y : completedBoundaryTransportedClock.domain) :
    (completedBoundaryTransportedClock y).snd.snd =
      baseTwoCompletedBoundaryClockReturn y.val := rfl

/-- The image has the literal geometric boundary relation. This does not
claim membership in a second-order clock domain. -/
theorem completedBoundaryTransportedClock_image_boundary
    (y : completedBoundaryTransportedClock.domain) :
    HasSum (completedBoundaryCellReturnCoordinates (completedBoundaryTransportedClock y))
      (completedBoundaryTransportedClock y).snd.snd := y.property.2.2.hasSum

theorem baseTwoCompletedBoundaryHilbertState_mem_clockDomain (t : ℝ) :
    baseTwoCompletedBoundaryHilbertState t ∈ completedBoundaryTransportedClock.domain := by
  refine ⟨?_, ?_, summable_baseTwoCompletedBoundaryClockReturn t⟩
  · change HasSum (fun k => criticalMaterialGradient t (baseTwoCellRightEdge k) -
      criticalMaterialGradient t (baseTwoCellLeftEdge k)) (baseTwoCompletedBoundaryValue t)
    simpa only [baseTwoCompletedBoundaryValue, ← baseTwoCriticalCenterCell_eq_gradientEdges] using
      (summable_baseTwoCriticalCenterCell t).hasSum
  · exact (baseTwoCompletedMaterialClock_memLp_one t).of_exponent_ge (by norm_num)

/-- Strong derivative in the full standard Hilbert product. -/
theorem completedBoundaryState_hasDerivAt_clock (t : ℝ) :
    HasDerivAt baseTwoCompletedBoundaryHilbertState
      (-Complex.I • completedBoundaryTransportedClock
        ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩) t := by
  let innerPack := (WithLp.prodContinuousLinearEquiv 2 ℂ MaterialEdgeL2 ℂ).symm
  have hi := (innerPack.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    ((baseTwoCompletedMaterialGradientL2_hasDerivAt_clock t).prodMk
      (baseTwoCompletedBoundaryValue_hasDerivAt_clock t))
  let outerPack := (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (WithLp 2 (MaterialEdgeL2 × ℂ))).symm
  have hs : HasDerivAt (fun u => criticalMaterialSample u 1) (0:ℂ) t := by
    simpa only [criticalMaterialSample_one] using hasDerivAt_const t (1:ℂ)
  have h := (outerPack.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hs.prodMk hi)
  change HasDerivAt baseTwoCompletedBoundaryHilbertState
    (WithLp.toLp 2 (0, WithLp.toLp 2 (-Complex.I • baseTwoCompletedMaterialClockL2 t,
      -Complex.I * baseTwoCompletedBoundaryClockReturn (baseTwoCompletedBoundaryHilbertState t)))) t at h
  have hv : (-Complex.I • completedBoundaryTransportedClock
      ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩) =
      WithLp.toLp 2 (0, WithLp.toLp 2 (-Complex.I • baseTwoCompletedMaterialClockL2 t,
        -Complex.I * baseTwoCompletedBoundaryClockReturn (baseTwoCompletedBoundaryHilbertState t))) := by
    apply (WithLp.ofLp_injective 2); apply Prod.ext
    · simp
    · rfl
  rw [hv]
  exact h


/-- Material delta at n=1 encoded as seed and consecutive differences.
It predates and does not depend on any moment/readout calibration. -/
def completedBoundaryMaterialDeltaOne : BaseTwoCompletedBoundaryHilbertCarrier :=
  WithLp.toLp 2 (1, WithLp.toLp 2 (-lp.single 2 0 (1:ℂ), 0))

/-- Material delta at n=2 in the same geometric coordinates. -/
def completedBoundaryMaterialDeltaTwo : BaseTwoCompletedBoundaryHilbertCarrier :=
  WithLp.toLp 2 (0, WithLp.toLp 2
    (lp.single 2 0 (1:ℂ) - lp.single 2 1 (1:ℂ), 0))

private theorem deltaOne_clock_coordinates :
    completedBoundaryClockCoordinates completedBoundaryMaterialDeltaOne = 0 := by
  funext j
  change baseTwoCompletedBoundaryHilbertClockCoordinate completedBoundaryMaterialDeltaOne j = 0
  by_cases hj : j = 0
  · subst j
    simp [baseTwoCompletedBoundaryHilbertClockCoordinate, completedBoundaryMaterialDeltaOne,
      lp.coeFn_single, Pi.single_apply]
  · have hjpos : 0 < j := by omega
    simp [baseTwoCompletedBoundaryHilbertClockCoordinate, completedBoundaryMaterialDeltaOne,
      lp.coeFn_single, Pi.single_apply, Finset.sum_neg_distrib, hj, hjpos]

private theorem deltaTwo_clock_coordinates :
    completedBoundaryClockCoordinates completedBoundaryMaterialDeltaTwo =
      (Real.log 2 : ℂ) • ⇑completedBoundaryMaterialDeltaTwo.snd.fst := by
  funext j
  change baseTwoCompletedBoundaryHilbertClockCoordinate completedBoundaryMaterialDeltaTwo j = _
  by_cases h0 : j = 0
  · subst j
    simp [baseTwoCompletedBoundaryHilbertClockCoordinate, completedBoundaryMaterialDeltaTwo,
      lp.coeFn_single, Pi.single_apply]
  · by_cases h1 : j = 1
    · subst j
      simp [baseTwoCompletedBoundaryHilbertClockCoordinate, completedBoundaryMaterialDeltaTwo,
        lp.coeFn_single, Pi.single_apply, Finset.sum_sub_distrib]
      ring
    · have hj : 1 < j := by omega
      have hj0 : 0 < j := by omega
      simp [baseTwoCompletedBoundaryHilbertClockCoordinate, completedBoundaryMaterialDeltaTwo,
        lp.coeFn_single, Pi.single_apply, Finset.sum_sub_distrib, h0, h1, hj, hj0]

private theorem deltaOne_cell_returns :
    completedBoundaryCellReturnCoordinates completedBoundaryMaterialDeltaOne = 0 := by
  funext k
  simp [completedBoundaryCellReturnCoordinates, completedBoundaryMaterialDeltaOne,
    lp.coeFn_single]

private theorem deltaTwo_cell_returns :
    completedBoundaryCellReturnCoordinates completedBoundaryMaterialDeltaTwo = 0 := by
  funext k
  simp [completedBoundaryCellReturnCoordinates, completedBoundaryMaterialDeltaTwo,
    lp.coeFn_single]

private theorem deltaOne_clock_cells :
    completedBoundaryClockCellCoordinates completedBoundaryMaterialDeltaOne = 0 := by
  funext k
  simp [completedBoundaryClockCellCoordinates, deltaOne_clock_coordinates]

private theorem deltaTwo_clock_cells :
    completedBoundaryClockCellCoordinates completedBoundaryMaterialDeltaTwo = 0 := by
  funext k
  change completedBoundaryClockCoordinates completedBoundaryMaterialDeltaTwo (baseTwoCellRightEdge k) -
    completedBoundaryClockCoordinates completedBoundaryMaterialDeltaTwo (baseTwoCellLeftEdge k) = 0
  rw [deltaTwo_clock_coordinates]
  change (Real.log 2 : ℂ) * completedBoundaryMaterialDeltaTwo.snd.fst (baseTwoCellRightEdge k) -
    (Real.log 2 : ℂ) * completedBoundaryMaterialDeltaTwo.snd.fst (baseTwoCellLeftEdge k) = 0
  rw [← mul_sub]
  have hg := congrFun deltaTwo_cell_returns k
  change completedBoundaryMaterialDeltaTwo.snd.fst (baseTwoCellRightEdge k) -
    completedBoundaryMaterialDeltaTwo.snd.fst (baseTwoCellLeftEdge k) = 0 at hg
  rw [hg, mul_zero]

theorem completedBoundaryMaterialDeltaOne_mem_domain :
    completedBoundaryMaterialDeltaOne ∈ completedBoundaryTransportedClock.domain := by
  change HasSum (completedBoundaryCellReturnCoordinates completedBoundaryMaterialDeltaOne) 0 ∧
    Memℓp (completedBoundaryClockCoordinates completedBoundaryMaterialDeltaOne) 2 ∧ _
  rw [deltaOne_cell_returns, deltaOne_clock_coordinates, deltaOne_clock_cells]
  exact ⟨hasSum_zero, zero_memℓp, summable_zero⟩

theorem completedBoundaryMaterialDeltaTwo_mem_domain :
    completedBoundaryMaterialDeltaTwo ∈ completedBoundaryTransportedClock.domain := by
  change HasSum (completedBoundaryCellReturnCoordinates completedBoundaryMaterialDeltaTwo) 0 ∧
    Memℓp (completedBoundaryClockCoordinates completedBoundaryMaterialDeltaTwo) 2 ∧ _
  rw [deltaTwo_cell_returns, deltaTwo_clock_coordinates, deltaTwo_clock_cells]
  exact ⟨hasSum_zero,
    (lp.memℓp completedBoundaryMaterialDeltaTwo.snd.fst).const_smul (Real.log 2 : ℂ), summable_zero⟩

theorem completedBoundaryTransportedClock_deltaOne :
    completedBoundaryTransportedClock
      ⟨completedBoundaryMaterialDeltaOne, completedBoundaryMaterialDeltaOne_mem_domain⟩ = 0 := by
  apply (WithLp.ofLp_injective 2); apply Prod.ext
  · rfl
  · apply (WithLp.ofLp_injective 2); apply Prod.ext
    · apply lp.ext; exact deltaOne_clock_coordinates
    · change (∑' k, completedBoundaryClockCellCoordinates completedBoundaryMaterialDeltaOne k) = 0
      simp [deltaOne_clock_cells]

theorem completedBoundaryTransportedClock_deltaTwo :
    completedBoundaryTransportedClock
      ⟨completedBoundaryMaterialDeltaTwo, completedBoundaryMaterialDeltaTwo_mem_domain⟩ =
      (Real.log 2 : ℂ) • completedBoundaryMaterialDeltaTwo := by
  apply (WithLp.ofLp_injective 2); apply Prod.ext
  · simp [completedBoundaryMaterialDeltaTwo]
  · apply (WithLp.ofLp_injective 2); apply Prod.ext
    · apply lp.ext; exact deltaTwo_clock_coordinates
    · change (∑' k, completedBoundaryClockCellCoordinates completedBoundaryMaterialDeltaTwo k) = _
      rw [deltaTwo_clock_cells]
      simp [completedBoundaryMaterialDeltaTwo]

theorem completedBoundaryMaterialDelta_inner :
    inner ℂ completedBoundaryMaterialDeltaOne completedBoundaryMaterialDeltaTwo = -1 := by
  simp [completedBoundaryMaterialDeltaOne, completedBoundaryMaterialDeltaTwo,
    WithLp.prod_inner_apply, inner_neg_left, inner_sub_right, lp.inner_single_left, RCLike.inner_apply]

/-- The finite standard-metric obstruction persists on the actual infinite
graph domain. No assertion about another metric or carrier follows. -/
theorem completedBoundaryTransportedClock_not_standard_symmetric :
    ¬ completedBoundaryTransportedClock.IsFormalAdjoint completedBoundaryTransportedClock := by
  intro hs
  have h := hs ⟨completedBoundaryMaterialDeltaOne, completedBoundaryMaterialDeltaOne_mem_domain⟩
    ⟨completedBoundaryMaterialDeltaTwo, completedBoundaryMaterialDeltaTwo_mem_domain⟩
  rw [completedBoundaryTransportedClock_deltaOne, completedBoundaryTransportedClock_deltaTwo,
    inner_zero_left] at h
  rw [inner_smul_right (𝕜 := ℂ) completedBoundaryMaterialDeltaOne completedBoundaryMaterialDeltaTwo
    (Real.log 2 : ℂ), completedBoundaryMaterialDelta_inner] at h
  have hc : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.log_pos (by norm_num)))
  exact hc (by simpa using h.symm)

/-- Non-symmetry also rules out self-adjointness in this same standard metric. -/
theorem completedBoundaryTransportedClock_not_selfAdjoint :
    ¬ IsSelfAdjoint completedBoundaryTransportedClock := by
  intro hs
  apply completedBoundaryTransportedClock_not_standard_symmetric
  have he : completedBoundaryTransportedClock.adjoint = completedBoundaryTransportedClock :=
    LinearPMap.isSelfAdjoint_def.mp hs
  simpa only [he] using
    (LinearPMap.adjoint_isFormalAdjoint hs.dense_domain (T := completedBoundaryTransportedClock))

end GeometryOfNumbers.Analysis.BaseTwoCompletion
