import GeometryOfNumbers.Analysis.BaseTwoPhysicalEdgeC2Address
import GeometryOfNumbers.Analysis.C2GlobalGreenBridge
import GeometryOfNumbers.Analysis.C2RealFiberTfvdIncidence
import GreenFrame.Concrete.Finite.L2CoordinateMask

/-! # Physical/residual material edges and genuine C2 fiber TFVD
Physical edges are reindexed through their odd endpoints and the proved C2
address decoder. Both complex quadratures and the residual material edges are
retained. No physical source amplitude or moment equality is used.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal InnerProductSpace
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open C2GlobalGreenBridge GreenFrame.Concrete RealCarry

private def coordinateRestrictionLinear {α β E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : α → β) (he : Function.Injective e) (L : E →ₗ[ℝ] F)
    (hL : ∀ z, ‖L z‖ ≤ ‖z‖) : ℓ²(β,E) →ₗ[ℝ] ℓ²(α,F) where
  toFun x := ⟨fun i => L (x (e i)), by
    have hx : Memℓp (fun i => x (e i)) 2 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      exact ((lp.memℓp x).summable (by norm_num)).comp_injective he
    exact hx.mono' (fun i => hL _)⟩
  map_add' x y := by apply lp.ext; funext i; exact L.map_add _ _
  map_smul' c x := by apply lp.ext; funext i; exact L.map_smul c _

private theorem coordinateRestrictionLinear_norm {α β E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : α → β) (he : Function.Injective e) (L : E →ₗ[ℝ] F)
    (hL : ∀ z, ‖L z‖ ≤ ‖z‖) (x : ℓ²(β,E)) :
    ‖coordinateRestrictionLinear e he L hL x‖ ≤ ‖x‖ := by
  let y := coordinateRestrictionLinear e he L hL x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hx := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  have hy := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) y
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  rw [hy, hx]
  have hs := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have ht := (lp.memℓp y).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs ht
  apply Summable.tsum_le_tsum_of_inj e he (fun _ _ => sq_nonneg _) _ ht hs
  intro i
  change ‖L (x (e i))‖^2 ≤ ‖x (e i)‖^2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hL _)

private def coordinateRestrictionCLM {α β E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : α → β) (he : Function.Injective e) (L : E →ₗ[ℝ] F)
    (hL : ∀ z, ‖L z‖ ≤ ‖z‖) : ℓ²(β,E) →L[ℝ] ℓ²(α,F) :=
  (coordinateRestrictionLinear e he L hL).mkContinuous 1
    (fun x => by simpa using coordinateRestrictionLinear_norm e he L hL x)

/-- Restriction is a contraction, not an injective map on all material edges. -/
def baseTwoPhysicalEdgeRestriction : MaterialEdgeL2 →L[ℝ] ℓ²(BaseTwoPhysicalEdge,ℂ) :=
  coordinateRestrictionCLM baseTwoPhysicalEdgeIndex baseTwoPhysicalEdgeIndex_injective
    (LinearMap.id : ℂ →ₗ[ℝ] ℂ) (fun _ => le_rfl)

@[simp] theorem baseTwoPhysicalEdgeRestriction_apply (g : MaterialEdgeL2)
    (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalEdgeRestriction g e = g (baseTwoPhysicalEdgeIndex e) := rfl

theorem baseTwoPhysicalEdgeRestriction_norm_le (g : MaterialEdgeL2) :
    ‖baseTwoPhysicalEdgeRestriction g‖ ≤ ‖g‖ :=
  coordinateRestrictionLinear_norm baseTwoPhysicalEdgeIndex baseTwoPhysicalEdgeIndex_injective
    (LinearMap.id : ℂ →ₗ[ℝ] ℂ) (fun _ => le_rfl) g

/-- Reuse the existing complex quadrature map and real-plane Hilbert chart. -/
def baseTwoMaterialEdgeRealification : ℂ →ₗᵢ[ℝ] RealPlaneHilbert :=
  { realPlaneHilbertEquiv.toLinearMap.comp Complex.equivRealProdLm.toLinearMap with
    norm_map' := fun z => by
      have h : realPlaneToComplexIsometry (realPlaneHilbertEquiv (z.re,z.im)) = z := rfl
      exact (realPlaneToComplexIsometry.norm_map _).symm.trans (congrArg norm h) }

theorem baseTwoMaterialEdgeRealification_pack (z : ℂ) :
    realPlaneToComplexIsometry (baseTwoMaterialEdgeRealification z) = z := rfl

theorem baseTwoMaterialEdgeRealification_neg_I (z : ℂ) :
    (baseTwoMaterialEdgeRealification (-Complex.I*z)) 0 =
      (baseTwoMaterialEdgeRealification z) 1 ∧
    (baseTwoMaterialEdgeRealification (-Complex.I*z)) 1 =
      -(baseTwoMaterialEdgeRealification z) 0 := by
  change (-Complex.I*z).re = z.im ∧ (-Complex.I*z).im = -z.re
  simp [Complex.mul_re, Complex.mul_im]

/-- Reindex only after decoding endpoint -> core/direction/true depth. -/
def baseTwoPhysicalEdgeC2State : MaterialEdgeL2 →L[ℝ] GlobalC2BranchCarrier :=
  coordinateRestrictionCLM
    (fun i => baseTwoPhysicalEdgeIndex (baseTwoPhysicalEdgeEquivC2Address.symm i))
    (baseTwoPhysicalEdgeIndex_injective.comp baseTwoPhysicalEdgeEquivC2Address.symm.injective)
    baseTwoMaterialEdgeRealification.toLinearMap
    (fun z => (baseTwoMaterialEdgeRealification.norm_map z).le)

@[simp] theorem baseTwoPhysicalEdgeC2State_apply (g : MaterialEdgeL2)
    (i : GlobalC2BranchAddress) :
    baseTwoPhysicalEdgeC2State g i = baseTwoMaterialEdgeRealification
      (g (baseTwoPhysicalEdgeIndex (baseTwoPhysicalEdgeEquivC2Address.symm i))) := rfl

theorem baseTwoPhysicalEdgeC2State_apply_edge (g : MaterialEdgeL2) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalEdgeC2State g (baseTwoPhysicalEdgeC2Address e) =
      baseTwoMaterialEdgeRealification (g (baseTwoPhysicalEdgeIndex e)) := by
  rw [baseTwoPhysicalEdgeC2State_apply]
  change baseTwoMaterialEdgeRealification (g (baseTwoPhysicalEdgeIndex
    (baseTwoPhysicalEdgeEquivC2Address.symm (baseTwoPhysicalEdgeEquivC2Address e)))) = _
  rw [Equiv.symm_apply_apply]

theorem baseTwoPhysicalEdgeC2State_norm_le (g : MaterialEdgeL2) :
    ‖baseTwoPhysicalEdgeC2State g‖ ≤ ‖g‖ :=
  coordinateRestrictionLinear_norm
    (fun i => baseTwoPhysicalEdgeIndex (baseTwoPhysicalEdgeEquivC2Address.symm i))
    (baseTwoPhysicalEdgeIndex_injective.comp baseTwoPhysicalEdgeEquivC2Address.symm.injective)
    baseTwoMaterialEdgeRealification.toLinearMap
    (fun z => (baseTwoMaterialEdgeRealification.norm_map z).le) g

/-- Physical support projection in the original material-edge carrier. -/
def baseTwoPhysicalEdgeProjection : MaterialEdgeL2 →L[ℂ] MaterialEdgeL2 :=
  l2CoordinateMaskCLM (fun n : ℕ => n % 4 = 2 ∨ n % 4 = 3)

/-- The residual information is retained as its own full Hilbert channel. -/
def baseTwoResidualEdgeProjection : MaterialEdgeL2 →L[ℂ] MaterialEdgeL2 :=
  l2CoordinateMaskCLM (fun n : ℕ => ¬ (n % 4 = 2 ∨ n % 4 = 3))

theorem baseTwoResidualEdgePredicate (n : ℕ) :
    ¬ (n % 4 = 2 ∨ n % 4 = 3) ↔ n % 4 = 0 ∨ n % 4 = 1 := by omega

theorem baseTwoPhysicalResidual_reconstruction (g : MaterialEdgeL2) :
    baseTwoPhysicalEdgeProjection g + baseTwoResidualEdgeProjection g = g := by
  apply lp.ext; funext n
  change (if n % 4 = 2 ∨ n % 4 = 3 then g n else 0) +
    (if ¬ (n % 4 = 2 ∨ n % 4 = 3) then g n else 0) = g n
  by_cases h : n % 4 = 2 ∨ n % 4 = 3
  · rw [if_pos h, if_neg (not_not.mpr h), add_zero]
  · rw [if_neg h, if_pos h, zero_add]

theorem baseTwoPhysicalResidual_orthogonal (g h : MaterialEdgeL2) :
    inner ℂ (baseTwoPhysicalEdgeProjection g) (baseTwoResidualEdgeProjection h) = 0 := by
  rw [lp.inner_eq_tsum]
  have he : (fun n => inner ℂ (baseTwoPhysicalEdgeProjection g n)
      (baseTwoResidualEdgeProjection h n)) = (fun _ : ℕ => (0 : ℂ)) := by
    funext n
    change inner ℂ (if n % 4 = 2 ∨ n % 4 = 3 then g n else 0)
      (if ¬ (n % 4 = 2 ∨ n % 4 = 3) then h n else 0) = 0
    by_cases hn : n % 4 = 2 ∨ n % 4 = 3
    · rw [if_pos hn, if_neg (not_not.mpr hn), inner_zero_right]
    · rw [if_neg hn, if_pos hn, inner_zero_left]
  rw [he, tsum_zero]

theorem baseTwoPhysicalResidual_norm_sq (g : MaterialEdgeL2) :
    ‖g‖^2 = ‖baseTwoPhysicalEdgeProjection g‖^2 + ‖baseTwoResidualEdgeProjection g‖^2 := by
  conv_lhs => rw [← baseTwoPhysicalResidual_reconstruction g]
  simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (baseTwoPhysicalEdgeProjection g) (baseTwoResidualEdgeProjection g)
    (baseTwoPhysicalResidual_orthogonal g g)

/-- Only physical values are read; the residual is still stored separately. -/
theorem baseTwoPhysicalEdgeC2State_projection (g : MaterialEdgeL2) :
    baseTwoPhysicalEdgeC2State (baseTwoPhysicalEdgeProjection g) = baseTwoPhysicalEdgeC2State g := by
  ext i r
  have h := (baseTwoPhysicalEdgeIndex_range _).mp
    ⟨baseTwoPhysicalEdgeEquivC2Address.symm i, rfl⟩
  simp [baseTwoPhysicalEdgeProjection, h]

/-- The actual C2 channel together with the residual retains every material edge. -/
theorem baseTwoPhysicalResidualC2_injective :
    Function.Injective (fun g : MaterialEdgeL2 =>
      (baseTwoPhysicalEdgeC2State g, baseTwoResidualEdgeProjection g)) := by
  intro g h he
  have hp := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  apply lp.ext; funext n
  by_cases hn : n % 4 = 2 ∨ n % 4 = 3
  · rcases (baseTwoPhysicalEdgeIndex_range n).mpr hn with ⟨e,rfl⟩
    have hc := congrArg (fun x : GlobalC2BranchCarrier =>
      realPlaneToComplexIsometry (x (baseTwoPhysicalEdgeC2Address e))) hp
    simpa only [baseTwoPhysicalEdgeC2State_apply_edge,
      baseTwoMaterialEdgeRealification_pack] using hc
  · have hc := congrArg (fun x : MaterialEdgeL2 => x n) hr
    change (if ¬ (n % 4 = 2 ∨ n % 4 = 3) then g n else 0) =
      (if ¬ (n % 4 = 2 ∨ n % 4 = 3) then h n else 0) at hc
    simpa only [if_pos hn] using hc

/-- Restriction/reindexing/realification conserves the physical projected energy. -/
theorem baseTwoPhysicalEdgeC2State_norm_sq_projection (g : MaterialEdgeL2) :
    ‖baseTwoPhysicalEdgeC2State g‖^2 = ‖baseTwoPhysicalEdgeProjection g‖^2 := by
  have he : (fun n => ‖baseTwoPhysicalEdgeProjection g n‖^2) =
      Function.extend baseTwoPhysicalEdgeIndex
        (fun e => ‖g (baseTwoPhysicalEdgeIndex e)‖^2) 0 := by
    funext n
    by_cases hn : n % 4 = 2 ∨ n % 4 = 3
    · rcases (baseTwoPhysicalEdgeIndex_range n).mpr hn with ⟨e,rfl⟩
      rw [baseTwoPhysicalEdgeIndex_injective.extend_apply]
      change ‖if baseTwoPhysicalEdgeIndex e % 4 = 2 ∨
        baseTwoPhysicalEdgeIndex e % 4 = 3 then g (baseTwoPhysicalEdgeIndex e) else 0‖^2 = _
      rw [if_pos hn]
    · have ho : ¬ ∃ e, baseTwoPhysicalEdgeIndex e = n := by
        intro h; exact hn ((baseTwoPhysicalEdgeIndex_range n).mp h)
      rw [Function.extend_apply' _ _ _ ho]
      change ‖if n % 4 = 2 ∨ n % 4 = 3 then g n else 0‖^2 = 0
      rw [if_neg hn]; simp
  have hx := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (baseTwoPhysicalEdgeC2State g)
  have hy := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (baseTwoPhysicalEdgeProjection g)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  rw [hx,hy,he]
  simp only [baseTwoPhysicalEdgeC2State_apply, LinearIsometry.norm_map]
  rw [tsum_extend_zero baseTwoPhysicalEdgeIndex_injective]
  exact baseTwoPhysicalEdgeEquivC2Address.symm.tsum_eq
    (fun e : BaseTwoPhysicalEdge => ‖g (baseTwoPhysicalEdgeIndex e)‖^2)

/-- No residual energy disappears in the actual physical C2 + residual split. -/
theorem baseTwoPhysicalC2Residual_norm_sq (g : MaterialEdgeL2) :
    ‖g‖^2 = ‖baseTwoPhysicalEdgeC2State g‖^2 + ‖baseTwoResidualEdgeProjection g‖^2 := by
  rw [baseTwoPhysicalEdgeC2State_norm_sq_projection]
  exact baseTwoPhysicalResidual_norm_sq g

def baseTwoPhysicalOrdinaryC2State (t : ℝ) : GlobalC2BranchCarrier :=
  baseTwoPhysicalEdgeC2State (baseTwoCompletedMaterialGradientL2 t)

def baseTwoPhysicalLogGradientC2State (t : ℝ) : GlobalC2BranchCarrier :=
  baseTwoPhysicalEdgeC2State (baseTwoCompletedMaterialClockL2 t)

theorem baseTwoPhysicalOrdinaryC2State_apply (t : ℝ) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalOrdinaryC2State t (baseTwoPhysicalEdgeC2Address e) =
      baseTwoMaterialEdgeRealification (criticalMaterialGradient t (baseTwoPhysicalEdgeIndex e)) :=
  baseTwoPhysicalEdgeC2State_apply_edge _ e

theorem baseTwoPhysicalLogGradientC2State_apply (t : ℝ) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalLogGradientC2State t (baseTwoPhysicalEdgeC2Address e) =
      baseTwoMaterialEdgeRealification (baseTwoNativeLogGradientFormula t (baseTwoPhysicalEdgeIndex e)) := by
  rw [baseTwoPhysicalLogGradientC2State, baseTwoPhysicalEdgeC2State_apply_edge,
    baseTwoCompletedMaterialClockL2_apply, baseTwoCompletedClockCoordinate_eq_nativeLogFormula]

/-- Strong derivative in the complete physical branch Hilbert carrier. -/
theorem baseTwoPhysicalOrdinaryC2State_hasDerivAt (t : ℝ) :
    HasDerivAt baseTwoPhysicalOrdinaryC2State
      (baseTwoPhysicalEdgeC2State (-Complex.I • baseTwoCompletedMaterialClockL2 t)) t :=
  baseTwoPhysicalEdgeC2State.hasFDerivAt.comp_hasDerivAt t
    (baseTwoCompletedMaterialGradientL2_hasDerivAt_clock t)

/-- This sum is only asserted on the concrete completed ℓ¹ orbit. -/
theorem baseTwoCompletedBoundaryValue_eq_physicalChannel (t : ℝ) :
    baseTwoCompletedBoundaryValue t = ∑' k : ℕ,
      (realPlaneToComplexIsometry (baseTwoPhysicalOrdinaryC2State t
          (baseTwoPhysicalEdgeC2Address (k,1))) -
       realPlaneToComplexIsometry (baseTwoPhysicalOrdinaryC2State t
          (baseTwoPhysicalEdgeC2Address (k,0)))) := by
  unfold baseTwoCompletedBoundaryValue
  apply tsum_congr; intro k
  rw [baseTwoPhysicalOrdinaryC2State_apply, baseTwoPhysicalOrdinaryC2State_apply,
    baseTwoMaterialEdgeRealification_pack, baseTwoMaterialEdgeRealification_pack]
  simp [baseTwoPhysicalEdgeIndex]

/-- Absolute convergence is inherited from the complete geometric cells. -/
theorem summable_baseTwoPhysicalCellReturn (t : ℝ) :
    Summable (fun k : ℕ =>
      realPlaneToComplexIsometry (baseTwoPhysicalOrdinaryC2State t
        (baseTwoPhysicalEdgeC2Address (k,1))) -
      realPlaneToComplexIsometry (baseTwoPhysicalOrdinaryC2State t
        (baseTwoPhysicalEdgeC2Address (k,0)))) := by
  apply (summable_baseTwoCriticalCenterCell t).congr
  intro k
  rw [baseTwoCriticalCenterCell_eq_gradientEdges,
    baseTwoPhysicalOrdinaryC2State_apply, baseTwoPhysicalOrdinaryC2State_apply,
    baseTwoMaterialEdgeRealification_pack, baseTwoMaterialEdgeRealification_pack]
  simp [baseTwoPhysicalEdgeIndex]

def baseTwoPhysicalOrdinaryTfvd (eta t : ℝ) : C2RealTfvdChannels :=
  c2FiberTfvdAnalysis eta (baseTwoPhysicalOrdinaryC2State t)

def baseTwoPhysicalLogGradientTfvd (eta t : ℝ) : C2RealTfvdChannels :=
  c2FiberTfvdAnalysis eta (baseTwoPhysicalLogGradientC2State t)

theorem baseTwoPhysicalOrdinaryTfvd_synthesis (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (t : ℝ) :
    c2FiberTfvdSynthesis eta h0.le h1 (baseTwoPhysicalOrdinaryTfvd eta t) =
      c2BranchVerticalCoordinates (baseTwoPhysicalOrdinaryC2State t) :=
  c2FiberTfvdSynthesis_analysis eta h0 h1 _

theorem baseTwoPhysicalLogGradientTfvd_synthesis (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (t : ℝ) :
    c2FiberTfvdSynthesis eta h0.le h1 (baseTwoPhysicalLogGradientTfvd eta t) =
      c2BranchVerticalCoordinates (baseTwoPhysicalLogGradientC2State t) :=
  c2FiberTfvdSynthesis_analysis eta h0 h1 _

/-- A lossless material-edge analysis retains the residual next to the true C2 TFVD. -/
def baseTwoPhysicalResidualTfvdAnalysis (eta : ℝ) :
    MaterialEdgeL2 →ₗ[ℝ] (C2RealTfvdChannels × MaterialEdgeL2) :=
  ((c2FiberTfvdAnalysis eta).comp baseTwoPhysicalEdgeC2State.toLinearMap).prod
    (baseTwoResidualEdgeProjection.restrictScalars ℝ).toLinearMap

theorem baseTwoPhysicalResidualTfvdAnalysis_injective (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) :
    Function.Injective (baseTwoPhysicalResidualTfvdAnalysis eta) := by
  intro g h he
  have hp := (c2FiberTfvdAnalysis_injective eta h0 h1) (congrArg Prod.fst he)
  have hr := congrArg Prod.snd he
  exact baseTwoPhysicalResidualC2_injective (Prod.ext hp hr)

/-- Both completed difference channels, each with its residual still present. -/
def baseTwoCompletedPhysicalResidualTfvdPair (eta t : ℝ) :
    (C2RealTfvdChannels × MaterialEdgeL2) × (C2RealTfvdChannels × MaterialEdgeL2) :=
  (baseTwoPhysicalResidualTfvdAnalysis eta (baseTwoCompletedMaterialGradientL2 t),
   baseTwoPhysicalResidualTfvdAnalysis eta (baseTwoCompletedMaterialClockL2 t))

theorem baseTwoCompletedPhysicalResidualTfvdPair_ordinary (eta t : ℝ) :
    (baseTwoCompletedPhysicalResidualTfvdPair eta t).1 =
      (baseTwoPhysicalOrdinaryTfvd eta t,
       baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 t)) := rfl

theorem baseTwoCompletedPhysicalResidualTfvdPair_log (eta t : ℝ) :
    (baseTwoCompletedPhysicalResidualTfvdPair eta t).2 =
      (baseTwoPhysicalLogGradientTfvd eta t,
       baseTwoResidualEdgeProjection (baseTwoCompletedMaterialClockL2 t)) := rfl

/-- Canonical base-two TFVD ratio, already derived upstream from critical depth amplitude. -/
def baseTwoCriticalPhysicalResidualTfvdPair (t : ℝ) :
    (C2RealTfvdChannels × MaterialEdgeL2) × (C2RealTfvdChannels × MaterialEdgeL2) :=
  baseTwoCompletedPhysicalResidualTfvdPair (criticalVerticalAmplitudeRatio 2 (by decide)) t

theorem baseTwoCriticalPhysicalTfvd_synthesis (t : ℝ) :
    let eta := criticalVerticalAmplitudeRatio 2 (by decide)
    c2FiberTfvdSynthesis eta (criticalVerticalAmplitudeRatio_pos 2 _).le
        (criticalVerticalAmplitudeRatio_lt_one 2 (by decide)) (baseTwoPhysicalOrdinaryTfvd eta t) =
      c2BranchVerticalCoordinates (baseTwoPhysicalOrdinaryC2State t) ∧
    c2FiberTfvdSynthesis eta (criticalVerticalAmplitudeRatio_pos 2 _).le
        (criticalVerticalAmplitudeRatio_lt_one 2 (by decide)) (baseTwoPhysicalLogGradientTfvd eta t) =
      c2BranchVerticalCoordinates (baseTwoPhysicalLogGradientC2State t) :=
  ⟨baseTwoPhysicalOrdinaryTfvd_synthesis _ (criticalVerticalAmplitudeRatio_pos 2 _)
      (criticalVerticalAmplitudeRatio_lt_one 2 (by decide)) t,
   baseTwoPhysicalLogGradientTfvd_synthesis _ (criticalVerticalAmplitudeRatio_pos 2 _)
      (criticalVerticalAmplitudeRatio_lt_one 2 (by decide)) t⟩

private def planeEvaluationLinear (r : Fin 2) : RealPlaneHilbert →ₗ[ℝ] ℝ where
  toFun v := v r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def branchCoordinateCLM (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    GlobalC2BranchCarrier →L[ℝ] CarryVerticalL2 :=
  coordinateRestrictionCLM (fun j : ℕ => (m,(a,j)))
    (by intro j k h; exact congrArg (fun i : GlobalC2BranchAddress => i.2.2) h)
    (planeEvaluationLinear r) (fun v => PiLp.norm_apply_le v r)

/-- Each genuine core/sign/quadrature TFVD channel is a continuous real map. -/
def baseTwoPhysicalTfvdChannel (eta : ℝ) (m : PositiveOddCore)
    (a : C2BranchDirection) (r : Fin 2) :
    MaterialEdgeL2 →L[ℝ] (CarryVerticalL2 × (ℝ × ℝ)) :=
  (realCarryTfvdAnalysis eta).comp ((branchCoordinateCLM m a r).comp baseTwoPhysicalEdgeC2State)

theorem baseTwoPhysicalTfvdChannel_apply (eta : ℝ) (m : PositiveOddCore)
    (a : C2BranchDirection) (r : Fin 2) (g : MaterialEdgeL2) :
    baseTwoPhysicalTfvdChannel eta m a r g =
      c2FiberTfvdAnalysis eta (baseTwoPhysicalEdgeC2State g) m a r := rfl

/-- Clock compatibility in the norm of each actual TFVD channel, including trace.
Complex multiplication stays before realification and retains the sign -i. -/
theorem baseTwoPhysicalOrdinaryTfvd_hasDerivAt (eta t : ℝ) (m : PositiveOddCore)
    (a : C2BranchDirection) (r : Fin 2) :
    HasDerivAt (fun u => baseTwoPhysicalOrdinaryTfvd eta u m a r)
      (c2FiberTfvdAnalysis eta
        (baseTwoPhysicalEdgeC2State (-Complex.I • baseTwoCompletedMaterialClockL2 t)) m a r) t := by
  have h := (baseTwoPhysicalTfvdChannel eta m a r).hasFDerivAt.comp_hasDerivAt t
    (baseTwoCompletedMaterialGradientL2_hasDerivAt_clock t)
  exact h

end GeometryOfNumbers.Analysis.BaseTwoCompletion
