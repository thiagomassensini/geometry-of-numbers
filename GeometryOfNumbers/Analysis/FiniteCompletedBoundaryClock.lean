import GeometryOfNumbers.Analysis.FiniteSeedGradientClock

/-! # Whole-cell boundary as a redundant finite graph coordinate

The finite clock acts on the graph of the geometric boundary map. No arbitrary
extension to the independent ambient boundary coordinate is introduced.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProduct
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GeometryOfNumbers.Analysis.NativeMaterialClock
open GeometryOfNumbers.Analysis.FiniteClockJets

/-- Typed actual edges inside the synchronized 4N-edge material cutoff. -/
def finiteBaseTwoLeftEdge {N : ℕ} (k : Fin N) : Fin (4 * N) :=
  ⟨baseTwoCellLeftEdge k.val, (baseTwoCell_materialCutoff N).1 _ k.isLt |>.1⟩
def finiteBaseTwoRightEdge {N : ℕ} (k : Fin N) : Fin (4 * N) :=
  ⟨baseTwoCellRightEdge k.val, (baseTwoCell_materialCutoff N).1 _ k.isLt |>.2⟩

/-- The exact linear complete-cell return map on finite gradients. -/
def finiteCompletedBoundaryReturn (N : ℕ) : FiniteRealSpectralHilbert (4 * N) →ₗ[ℂ] ℂ where
  toFun g := ∑ k : Fin N, (g (finiteBaseTwoRightEdge k) - g (finiteBaseTwoLeftEdge k))
  map_add' x y := by simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]; ring
  map_smul' a x := by simp [Finset.mul_sum, mul_sub]

abbrev FiniteCompletedBoundaryCarrier (N : ℕ) : Type :=
  WithLp 2 (ℂ × WithLp 2 (FiniteRealSpectralHilbert (4 * N) × ℂ))

def finiteCompletedBoundaryEmbed (N : ℕ) :
    FiniteSeedGradientCarrier (4 * N) →ₗ[ℂ] FiniteCompletedBoundaryCarrier N where
  toFun x := WithLp.toLp 2 (x.fst, WithLp.toLp 2 (x.snd, finiteCompletedBoundaryReturn N x.snd))
  map_add' x y := by
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · rfl
    · apply (WithLp.ofLp_injective 2); apply Prod.ext
      · rfl
      · exact map_add _ _ _
  map_smul' a x := by
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · rfl
    · apply (WithLp.ofLp_injective 2); apply Prod.ext
      · rfl
      · exact map_smul _ _ _

def finiteCompletedBoundaryForget (N : ℕ) :
    FiniteCompletedBoundaryCarrier N →ₗ[ℂ] FiniteSeedGradientCarrier (4 * N) where
  toFun y := WithLp.toLp 2 (y.fst, y.snd.fst)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem finiteCompletedBoundaryForget_embed (N : ℕ)
    (x : FiniteSeedGradientCarrier (4 * N)) :
    finiteCompletedBoundaryForget N (finiteCompletedBoundaryEmbed N x) = x := rfl

def finiteCompletedBoundaryGraph (N : ℕ) : Submodule ℂ (FiniteCompletedBoundaryCarrier N) :=
  LinearMap.range (finiteCompletedBoundaryEmbed N)

theorem finiteCompletedBoundaryGraph_mem_iff (N : ℕ) (y : FiniteCompletedBoundaryCarrier N) :
    y ∈ finiteCompletedBoundaryGraph N ↔ y.snd.snd = finiteCompletedBoundaryReturn N y.snd.fst := by
  constructor
  · rintro ⟨x, rfl⟩; rfl
  · intro h
    refine ⟨finiteCompletedBoundaryForget N y, ?_⟩
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · rfl
    · apply (WithLp.ofLp_injective 2); apply Prod.ext
      · rfl
      · exact h.symm

/-- Clock only on the redundant graph, with its boundary action derived from
clocked complete cells. -/
def finiteCompletedBoundaryClock (N : ℕ) :
    Module.End ℂ (finiteCompletedBoundaryGraph N) where
  toFun y := ⟨finiteCompletedBoundaryEmbed N
    (finiteSeedGradientClock (4 * N) (finiteCompletedBoundaryForget N y)),
      ⟨_, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change finiteCompletedBoundaryEmbed N (finiteSeedGradientClock (4*N)
      (finiteCompletedBoundaryForget N ((x : FiniteCompletedBoundaryCarrier N) + y))) =
      finiteCompletedBoundaryEmbed N (finiteSeedGradientClock (4*N) (finiteCompletedBoundaryForget N x)) +
      finiteCompletedBoundaryEmbed N (finiteSeedGradientClock (4*N) (finiteCompletedBoundaryForget N y))
    simp only [map_add]
  map_smul' a x := by
    apply Subtype.ext
    change finiteCompletedBoundaryEmbed N (finiteSeedGradientClock (4*N)
      (finiteCompletedBoundaryForget N (a • (x : FiniteCompletedBoundaryCarrier N)))) =
      a • finiteCompletedBoundaryEmbed N (finiteSeedGradientClock (4*N) (finiteCompletedBoundaryForget N x))
    simp only [map_smul]

/-- Literal graph invariance, not an independent boundary equation. -/
theorem finiteCompletedBoundaryClock_graph_invariant (N : ℕ)
    (y : finiteCompletedBoundaryGraph N) :
    ((finiteCompletedBoundaryClock N y : finiteCompletedBoundaryGraph N) :
      FiniteCompletedBoundaryCarrier N) ∈ finiteCompletedBoundaryGraph N :=
  (finiteCompletedBoundaryClock N y).property

theorem finiteCompletedBoundaryClock_boundary (N : ℕ) (y : finiteCompletedBoundaryGraph N) :
    (finiteCompletedBoundaryClock N y : FiniteCompletedBoundaryCarrier N).snd.snd =
      ∑ k : Fin N,
        ((finiteSeedGradientClock (4 * N) (finiteCompletedBoundaryForget N y)).snd
            (finiteBaseTwoRightEdge k) -
          (finiteSeedGradientClock (4 * N) (finiteCompletedBoundaryForget N y)).snd
            (finiteBaseTwoLeftEdge k)) := rfl

/-- Graph-valued embedding, needed for the strong derivative on the graph. -/
def finiteCompletedBoundaryGraphEmbed (N : ℕ) :
    FiniteSeedGradientCarrier (4 * N) →ₗ[ℂ] finiteCompletedBoundaryGraph N where
  toFun x := ⟨finiteCompletedBoundaryEmbed N x, ⟨x, rfl⟩⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul _ _ _

theorem finiteCompletedBoundaryClock_intertwining (N : ℕ)
    (x : FiniteSeedGradientCarrier (4 * N)) :
    finiteCompletedBoundaryClock N (finiteCompletedBoundaryGraphEmbed N x) =
      finiteCompletedBoundaryGraphEmbed N (finiteSeedGradientClock (4 * N) x) := rfl

/-- This is the existing finite material orbit, encoded and embedded in its
geometric boundary graph, before readout. -/
def finiteCompletedBoundaryOrbit (N : ℕ) (t : ℝ)
    (x : FiniteRealSpectralHilbert (4 * N + 1)) : finiteCompletedBoundaryGraph N :=
  finiteCompletedBoundaryGraphEmbed N (finiteSeedGradientOrbit (4 * N) t x)

theorem finiteCompletedBoundaryOrbit_hasDerivAt (N : ℕ)
    (x : FiniteRealSpectralHilbert (4 * N + 1)) (t : ℝ) :
    HasDerivAt (fun u => finiteCompletedBoundaryOrbit N u x)
      (-Complex.I • finiteCompletedBoundaryClock N (finiteCompletedBoundaryOrbit N t x)) t := by
  let E := (finiteCompletedBoundaryGraphEmbed N).toContinuousLinearMap
  have h := (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (finiteSeedGradientOrbit_hasDerivAt (4 * N) x t)
  change HasDerivAt (fun u => finiteCompletedBoundaryGraphEmbed N (finiteSeedGradientOrbit (4*N) u x))
    (finiteCompletedBoundaryGraphEmbed N (-Complex.I • finiteSeedGradientClock (4*N)
      (finiteSeedGradientOrbit (4*N) t x))) t at h
  simpa only [map_smul, finiteCompletedBoundaryOrbit, finiteCompletedBoundaryClock_intertwining] using h

theorem finiteSeedGradientOrbit_historical_gradient (K : ℕ) (t : ℝ) (j : Fin K) :
    (finiteSeedGradientOrbit K t (historicalInitialState (K + 1))).snd j =
      criticalMaterialGradient t j.val := by
  unfold finiteSeedGradientOrbit
  rw [finiteSeedGradientEncode_gradient]
  rw [← criticalMaterialSample_eq_finiteMaterialOrbit t j.succ,
    ← criticalMaterialSample_eq_finiteMaterialOrbit t j.castSucc]
  rfl

/-- The graph boundary is exactly the previously defined geometric prefix. -/
theorem finiteCompletedBoundaryOrbit_historical_boundary (N : ℕ) (t : ℝ) :
    (finiteCompletedBoundaryOrbit N t (historicalInitialState (4 * N + 1)) :
      FiniteCompletedBoundaryCarrier N).snd.snd = baseTwoCompletedBoundaryPrefix N t := by
  change (∑ k : Fin N,
    ((finiteSeedGradientOrbit (4*N) t (historicalInitialState (4*N+1))).snd
      (finiteBaseTwoRightEdge k) -
    (finiteSeedGradientOrbit (4*N) t (historicalInitialState (4*N+1))).snd
      (finiteBaseTwoLeftEdge k))) = _
  simp only [finiteSeedGradientOrbit_historical_gradient, finiteBaseTwoRightEdge, finiteBaseTwoLeftEdge]
  simpa only [baseTwoCompletedBoundaryPrefix] using
    (Fin.sum_univ_eq_sum_range (fun k => criticalMaterialGradient t (baseTwoCellRightEdge k) -
      criticalMaterialGradient t (baseTwoCellLeftEdge k)) N)

/-- The boundary derivative is the sum of clocked geometric cell returns. -/
theorem finiteCompletedBoundaryOrbit_boundary_hasDerivAt (N : ℕ)
    (x : FiniteRealSpectralHilbert (4 * N + 1)) (t : ℝ) :
    HasDerivAt (fun u => (finiteCompletedBoundaryOrbit N u x :
      FiniteCompletedBoundaryCarrier N).snd.snd)
      (-Complex.I * ∑ k : Fin N,
        ((finiteSeedGradientClock (4 * N) (finiteSeedGradientOrbit (4 * N) t x)).snd
            (finiteBaseTwoRightEdge k) -
          (finiteSeedGradientClock (4 * N) (finiteSeedGradientOrbit (4 * N) t x)).snd
            (finiteBaseTwoLeftEdge k))) t := by
  let beta := (WithLp.sndL 2 ℂ (FiniteRealSpectralHilbert (4*N)) ℂ).comp
    ((WithLp.sndL 2 ℂ ℂ (WithLp 2 (FiniteRealSpectralHilbert (4*N) × ℂ))).comp
      (finiteCompletedBoundaryGraph N).subtypeL)
  have h := (beta.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (finiteCompletedBoundaryOrbit_hasDerivAt N x t)
  change HasDerivAt (fun u => (finiteCompletedBoundaryOrbit N u x :
    FiniteCompletedBoundaryCarrier N).snd.snd)
    (-Complex.I * ∑ k : Fin N,
      ((finiteSeedGradientClock (4 * N) (finiteSeedGradientOrbit (4 * N) t x)).snd
        (finiteBaseTwoRightEdge k) -
      (finiteSeedGradientClock (4 * N) (finiteSeedGradientOrbit (4 * N) t x)).snd
        (finiteBaseTwoLeftEdge k))) t at h
  exact h


/-- Canonical material delta transported into the actual finite boundary graph. -/
def finiteCompletedBoundaryMaterialBasis (N : ℕ) (j : Fin (4 * N + 1)) :
    finiteCompletedBoundaryGraph N :=
  finiteCompletedBoundaryGraphEmbed N (finiteSeedGradientEncode (4*N) (finiteMaterialBasis j))

theorem finiteCompletedBoundaryClock_materialBasis (N : ℕ) (j : Fin (4 * N + 1)) :
    finiteCompletedBoundaryClock N (finiteCompletedBoundaryMaterialBasis N j) =
      (Real.log ((j.val+1 : ℕ) : ℝ) : ℂ) • finiteCompletedBoundaryMaterialBasis N j := by
  unfold finiteCompletedBoundaryMaterialBasis
  rw [finiteCompletedBoundaryClock_intertwining, finiteSeedGradientClock_intertwining,
    finiteMaterialClock_basis]
  simp only [map_smul]

/-- Smallest nonempty C2-cell cutoff: the images of material deltas at 1 and 2
have inner product -1 in the standard seed+gradient+boundary graph metric. -/
theorem finiteCompletedBoundaryMaterialBasis_one_two_inner :
    inner ℂ (finiteCompletedBoundaryMaterialBasis 1 (0 : Fin 5))
      (finiteCompletedBoundaryMaterialBasis 1 (1 : Fin 5)) = -1 := by
  change inner ℂ
    (finiteCompletedBoundaryEmbed 1 (finiteSeedGradientEncode 4 (finiteMaterialBasis (0 : Fin 5))))
    (finiteCompletedBoundaryEmbed 1 (finiteSeedGradientEncode 4 (finiteMaterialBasis (1 : Fin 5)))) = -1
  norm_num [finiteCompletedBoundaryEmbed, finiteSeedGradientEncode,
    WithLp.prod_inner_apply, PiLp.inner_apply, finiteMaterialBasis,
    finiteCompletedBoundaryReturn, finiteBaseTwoRightEdge, finiteBaseTwoLeftEdge,
    Fin.sum_univ_succ, Pi.single_apply, RCLike.inner_apply]

/-- The correctly transported clock is not symmetric in the standard product
Hilbert metric, already on the graph of one complete cell. -/
theorem finiteCompletedBoundaryClock_not_standard_symmetric :
    ¬ LinearMap.IsSymmetric (𝕜 := ℂ) (E := finiteCompletedBoundaryGraph 1) (finiteCompletedBoundaryClock 1) := by
  intro hs
  have h := hs (finiteCompletedBoundaryMaterialBasis 1 (0 : Fin 5))
    (finiteCompletedBoundaryMaterialBasis 1 (1 : Fin 5))
  have hz : finiteCompletedBoundaryClock 1 (finiteCompletedBoundaryMaterialBasis 1 (0 : Fin 5)) = 0 := by
    simpa using finiteCompletedBoundaryClock_materialBasis 1 (0 : Fin 5)
  have ht : finiteCompletedBoundaryClock 1 (finiteCompletedBoundaryMaterialBasis 1 (1 : Fin 5)) =
      (Real.log 2 : ℂ) • finiteCompletedBoundaryMaterialBasis 1 (1 : Fin 5) := by
    simpa using finiteCompletedBoundaryClock_materialBasis 1 (1 : Fin 5)
  rw [hz, ht, inner_zero_left] at h
  rw [inner_smul_right (𝕜 := ℂ) (finiteCompletedBoundaryMaterialBasis 1 (0 : Fin 5))
    (finiteCompletedBoundaryMaterialBasis 1 (1 : Fin 5)) (Real.log 2 : ℂ),
    finiteCompletedBoundaryMaterialBasis_one_two_inner] at h
  have hl : (Real.log 2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hc : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  exact hc (by simpa using h.symm)

end GeometryOfNumbers.Analysis.BaseTwoCompletion
