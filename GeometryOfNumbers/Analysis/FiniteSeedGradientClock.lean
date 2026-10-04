import GeometryOfNumbers.Analysis.BaseTwoCompletedBoundaryDynamics
import GeometryOfNumbers.Analysis.FiniteMaterialClockJets

/-! # Exact finite material-clock transport to seed and first differences

The coordinate equivalence is linear, not unitary. Material edge number j
joins samples j+1 and j+2. The clock is transported from the existing finite
material generator, without asserting symmetry in the standard product norm.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GeometryOfNumbers.Analysis.NativeMaterialClock
open GeometryOfNumbers.Analysis.FiniteClockJets

/-- Standard Hilbert product with K consecutive material edges and one seed. -/
abbrev FiniteSeedGradientCarrier (K : ℕ) : Type :=
  WithLp 2 (ℂ × FiniteRealSpectralHilbert K)

/-- All gradients preceding the material sample with zero-based index n. -/
def finiteGradientPrefix {K : ℕ} (g : FiniteRealSpectralHilbert K) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin K => j.val < n), g j

@[simp] theorem finiteGradientPrefix_zero {K : ℕ} (g : FiniteRealSpectralHilbert K) :
    finiteGradientPrefix g 0 = 0 := by simp [finiteGradientPrefix]

theorem finiteGradientPrefix_succ {K : ℕ} (g : FiniteRealSpectralHilbert K)
    (n : ℕ) (hn : n < K) :
    finiteGradientPrefix g (n + 1) = finiteGradientPrefix g n + g ⟨n, hn⟩ := by
  classical
  have he : Finset.univ.filter (fun j : Fin K => j.val < n + 1) =
      insert ⟨n, hn⟩ (Finset.univ.filter (fun j : Fin K => j.val < n)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      by_cases h : j.val = n
      · left; exact Fin.ext h
      · right; omega
    · rintro (h | h)
      · subst j; simp
      · omega
  unfold finiteGradientPrefix
  rw [he, Finset.sum_insert (by simp), add_comm]

/-- Encode samples into the seed and their actual consecutive differences. -/
def finiteSeedGradientEncode (K : ℕ) :
    FiniteRealSpectralHilbert (K + 1) →ₗ[ℂ] FiniteSeedGradientCarrier K where
  toFun x := WithLp.toLp 2 (x 0,
    WithLp.toLp 2 (fun j : Fin K => x j.succ - x j.castSucc))
  map_add' x y := by
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · rfl
    · ext j; simp; ring
  map_smul' a x := by
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · rfl
    · ext j; simp; ring

/-- Reconstruct every sample by seed plus the preceding differences. -/
def finiteSeedGradientDecode (K : ℕ) :
    FiniteSeedGradientCarrier K →ₗ[ℂ] FiniteRealSpectralHilbert (K + 1) where
  toFun y := WithLp.toLp 2 (fun j => y.fst + finiteGradientPrefix y.snd j.val)
  map_add' x y := by
    ext j
    simp [finiteGradientPrefix, Finset.sum_add_distrib]
    ring
  map_smul' a x := by
    ext j
    simp [finiteGradientPrefix, Finset.mul_sum, mul_add]

@[simp] theorem finiteSeedGradientEncode_seed (K : ℕ)
    (x : FiniteRealSpectralHilbert (K + 1)) : (finiteSeedGradientEncode K x).fst = x 0 := rfl

@[simp] theorem finiteSeedGradientEncode_gradient (K : ℕ)
    (x : FiniteRealSpectralHilbert (K + 1)) (j : Fin K) :
    (finiteSeedGradientEncode K x).snd j = x j.succ - x j.castSucc := rfl

@[simp] theorem finiteSeedGradientDecode_apply (K : ℕ)
    (y : FiniteSeedGradientCarrier K) (j : Fin (K + 1)) :
    finiteSeedGradientDecode K y j = y.fst + finiteGradientPrefix y.snd j.val := rfl

theorem finiteSeedGradientDecode_encode (K : ℕ)
    (x : FiniteRealSpectralHilbert (K + 1)) :
    finiteSeedGradientDecode K (finiteSeedGradientEncode K x) = x := by
  have h : ∀ n (hn : n < K + 1),
      x 0 + finiteGradientPrefix (finiteSeedGradientEncode K x).snd n = x ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
      intro hn
      have hnK : n < K := by omega
      rw [finiteGradientPrefix_succ _ n hnK, ← add_assoc, ih (by omega)]
      simp only [finiteSeedGradientEncode_gradient]
      have he : (⟨n, by omega⟩ : Fin (K+1)) = (⟨n, hnK⟩ : Fin K).castSucc := rfl
      rw [he]
      abel
  ext j
  exact h j.val j.isLt

theorem finiteSeedGradientEncode_decode (K : ℕ) (y : FiniteSeedGradientCarrier K) :
    finiteSeedGradientEncode K (finiteSeedGradientDecode K y) = y := by
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · simp
  · ext j
    change (y.fst + finiteGradientPrefix y.snd (j.val + 1)) -
      (y.fst + finiteGradientPrefix y.snd j.val) = y.snd j
    rw [finiteGradientPrefix_succ _ j.val j.isLt]
    abel

/-- Exact linear coordinate change; no norm-preservation assertion is made. -/
def finiteSeedGradientEquiv (K : ℕ) :
    FiniteRealSpectralHilbert (K + 1) ≃ₗ[ℂ] FiniteSeedGradientCarrier K :=
  { finiteSeedGradientEncode K with
    invFun := finiteSeedGradientDecode K
    left_inv := finiteSeedGradientDecode_encode K
    right_inv := finiteSeedGradientEncode_decode K }

/-- The transported material clock, defined by conjugation, not fitted entries. -/
def finiteSeedGradientClock (K : ℕ) : Module.End ℂ (FiniteSeedGradientCarrier K) :=
  (finiteSeedGradientEncode K).comp
    ((finiteMaterialClock (K + 1)).comp (finiteSeedGradientDecode K))

@[simp] theorem finiteSeedGradientClock_seed (K : ℕ) (y : FiniteSeedGradientCarrier K) :
    (finiteSeedGradientClock K y).fst = 0 := by
  simp [finiteSeedGradientClock, finiteRealSpectralFrequency]

/-- Exact triangular formula for the transported clock. -/
theorem finiteSeedGradientClock_gradient (K : ℕ) (y : FiniteSeedGradientCarrier K)
    (j : Fin K) :
    (finiteSeedGradientClock K y).snd j =
      (Real.log ((j.val + 2 : ℕ) : ℝ) : ℂ) * y.snd j +
      ((Real.log ((j.val + 2 : ℕ) : ℝ) : ℂ) -
        (Real.log ((j.val + 1 : ℕ) : ℝ) : ℂ)) *
        (y.fst + finiteGradientPrefix y.snd j.val) := by
  simp only [finiteSeedGradientClock, LinearMap.comp_apply,
    finiteSeedGradientEncode_gradient, finiteRealSpectralGenerator_apply,
    finiteSeedGradientDecode_apply, finiteRealSpectralFrequency,
    Fin.val_succ, Fin.val_castSucc]
  simp only [Nat.add_assoc, show (1 + 1 : ℕ) = 2 by rfl]
  rw [finiteGradientPrefix_succ _ j.val j.isLt]
  push_cast
  ring

theorem finiteSeedGradientClock_intertwining (K : ℕ)
    (x : FiniteRealSpectralHilbert (K + 1)) :
    finiteSeedGradientClock K (finiteSeedGradientEncode K x) =
      finiteSeedGradientEncode K (finiteMaterialClock (K + 1) x) := by
  simp only [finiteSeedGradientClock, LinearMap.comp_apply, finiteSeedGradientDecode_encode]

/-- Use the existing finite unitary orbit, then change coordinates. -/
def finiteSeedGradientOrbit (K : ℕ) (t : ℝ)
    (x : FiniteRealSpectralHilbert (K + 1)) : FiniteSeedGradientCarrier K :=
  finiteSeedGradientEncode K (finiteMaterialOrbit (K + 1) t x)

/-- Strong finite-dimensional derivative of the existing material orbit. -/
theorem finiteMaterialOrbit_hasDerivAt {M : ℕ}
    (x : FiniteRealSpectralHilbert M) (t : ℝ) :
    HasDerivAt (fun u => finiteMaterialOrbit M u x)
      (-Complex.I • finiteMaterialClock M (finiteMaterialOrbit M t x)) t := by
  have hp : HasDerivAt
      (fun u : ℝ => fun j : Fin M => finiteRealSpectralPhase u j * x j)
      (fun j : Fin M => -Complex.I * (finiteRealSpectralFrequency j : ℂ) *
        (finiteRealSpectralPhase t j * x j)) t := by
    apply hasDerivAt_pi.mpr
    intro j
    have hc : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have hh := (((hc.mul_const (finiteRealSpectralFrequency j : ℂ)).mul_const
      Complex.I).neg).cexp.mul_const (x j)
    simpa [finiteRealSpectralPhase, Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
      using hh
  have h := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hp
  have hv : (WithLp.toLp 2 (fun j : Fin M =>
      -Complex.I * (finiteRealSpectralFrequency j : ℂ) *
        (finiteRealSpectralPhase t j * x j)) : FiniteRealSpectralHilbert M) =
      -Complex.I • finiteMaterialClock M (finiteMaterialOrbit M t x) := by
    ext j
    change -Complex.I * (finiteRealSpectralFrequency j : ℂ) *
      (finiteRealSpectralPhase t j * x j) =
      -Complex.I * ((finiteRealSpectralFrequency j : ℂ) * (finiteRealSpectralPhase t j * x j))
    ring
  rw [← hv]
  exact h

theorem finiteSeedGradientOrbit_hasDerivAt (K : ℕ)
    (x : FiniteRealSpectralHilbert (K + 1)) (t : ℝ) :
    HasDerivAt (fun u => finiteSeedGradientOrbit K u x)
      (-Complex.I • finiteSeedGradientClock K (finiteSeedGradientOrbit K t x)) t := by
  let E := (finiteSeedGradientEncode K).toContinuousLinearMap
  have h := (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (finiteMaterialOrbit_hasDerivAt x t)
  change HasDerivAt (fun u => finiteSeedGradientEncode K (finiteMaterialOrbit (K+1) u x))
    (finiteSeedGradientEncode K (-Complex.I • finiteMaterialClock (K+1)
      (finiteMaterialOrbit (K+1) t x))) t at h
  simpa only [map_smul, finiteSeedGradientOrbit, finiteSeedGradientClock_intertwining] using h

/-- N complete base-two cells require exactly 4N material edges and samples
1,...,4N+1. The number follows from the existing right-edge positions. -/
theorem baseTwoCell_materialCutoff (N : ℕ) :
    (∀ k, k < N → baseTwoCellLeftEdge k < 4 * N ∧ baseTwoCellRightEdge k < 4 * N) ∧
    (0 < N → baseTwoCellRightEdge (N - 1) + 1 = 4 * N) ∧
    historicalHeadDimension 2 N = 4 * N + 1 := by
  simp only [baseTwoCellLeftEdge_eq, baseTwoCellRightEdge_eq, baseTwo_headDimension]
  constructor
  · intro k hk; omega
  · exact ⟨fun h => by omega, trivial⟩

/-- The pullback inner product is recorded, not installed as a new metric. -/
def finiteSeedGradientMaterialPairing (K : ℕ) (x y : FiniteSeedGradientCarrier K) : ℂ :=
  inner ℂ (finiteSeedGradientDecode K x) (finiteSeedGradientDecode K y)

theorem finiteSeedGradientClock_materialPairing_symmetric (K : ℕ)
    (x y : FiniteSeedGradientCarrier K) :
    finiteSeedGradientMaterialPairing K (finiteSeedGradientClock K x) y =
      finiteSeedGradientMaterialPairing K x (finiteSeedGradientClock K y) := by
  have hx : finiteSeedGradientDecode K (finiteSeedGradientClock K x) =
      finiteMaterialClock (K + 1) (finiteSeedGradientDecode K x) :=
    finiteSeedGradientDecode_encode K _
  have hy : finiteSeedGradientDecode K (finiteSeedGradientClock K y) =
      finiteMaterialClock (K + 1) (finiteSeedGradientDecode K y) :=
    finiteSeedGradientDecode_encode K _
  unfold finiteSeedGradientMaterialPairing
  rw [hx, hy]
  exact finiteRealSpectralGenerator_isSymmetric (K + 1) _ _

end GeometryOfNumbers.Analysis.BaseTwoCompletion
