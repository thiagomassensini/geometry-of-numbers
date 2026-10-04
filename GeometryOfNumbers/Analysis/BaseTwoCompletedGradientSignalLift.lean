import GeometryOfNumbers.Analysis.BaseTwoCompletedVectorLiftGate
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The complete seeded material-gradient state and its C2 boundary readout

The historical ordinary completed gradient channel is reconstructed locally
from the existing material samples. Its absolute summability supplies the
standard ℓ¹ presentation; the incoming seed retains every material value.
This is a Banach signal lift, not a Hilbert moment/Gram realization.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- Material edge n joins the positive material integers n+1 and n+2.
It is not a vertical depth label. -/
def criticalMaterialGradient (t : ℝ) (n : ℕ) : ℂ :=
  criticalMaterialSample t (n+2) - criticalMaterialSample t (n+1)

/-- Same native-line power difference as the historical ordinary channel,
but derived from the already existing local material sample. -/
theorem criticalMaterialGradient_eq_nativeLinePowerDifference (t : ℝ) (n : ℕ) :
    criticalMaterialGradient t n =
      ((n+2 : ℕ):ℂ)^(-baseTwoDressingParameter (t:ℂ)) -
        ((n+1 : ℕ):ℂ)^(-baseTwoDressingParameter (t:ℂ)) := by
  have he : criticalMaterialExponent t = -baseTwoDressingParameter (t:ℂ) := by
    unfold criticalMaterialExponent baseTwoDressingParameter
    ring
  rw [criticalMaterialGradient, criticalMaterialSample_eq_cpow t (by omega),
    criticalMaterialSample_eq_cpow t (by omega), he]

/-- First-difference bound on the preexisting material orbit. -/
theorem criticalMaterialGradient_norm_le (t : ℝ) (n : ℕ) :
    ‖criticalMaterialGradient t n‖ ≤ ‖criticalMaterialExponent t‖ *
      ((n+1 : ℕ) : ℝ)^(-3/2 : ℝ) := by
  let z := criticalMaterialExponent t
  let a : ℝ := (n+1 : ℕ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hz : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [z, criticalMaterialExponent] at this
  have hfun : criticalMaterialGradient t n = ((a+1 : ℝ):ℂ)^z - (a:ℂ)^z := by
    rw [criticalMaterialGradient, criticalMaterialSample_eq_cpow t (by omega),
      criticalMaterialSample_eq_cpow t (by omega)]
    simp only [a, z, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
    congr 2; ring
  have hb : ∀ x ∈ Set.Icc a (a+1),
      ‖z*(x:ℂ)^(z-1)‖ ≤ ‖z‖*a^(-3/2 : ℝ) := by
    intro x hx
    have hxpos := lt_of_lt_of_le ha hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have he : (z-1).re = (-3/2 : ℝ) := by
      dsimp [z, criticalMaterialExponent]; norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hx.1 (by norm_num)) (norm_nonneg _)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hasDerivAt_ofReal_cpow_const
      (ne_of_gt (lt_of_lt_of_le ha hx.1)) hz).hasDerivWithinAt)
    hb (convex_Icc a (a+1))
    (by constructor <;> linarith : a ∈ Set.Icc a (a+1))
    (by constructor <;> linarith : a+1 ∈ Set.Icc a (a+1))
  rw [hfun]
  simpa only [show a+1-a = (1:ℝ) by ring, norm_one, mul_one] using h

theorem summable_norm_criticalMaterialGradient (t : ℝ) :
    Summable (fun n => ‖criticalMaterialGradient t n‖) := by
  have hp : Summable (fun n : ℕ => ((n+1 : ℕ):ℝ)^(-3/2 : ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (criticalMaterialGradient_norm_le t) (hp.mul_left _)

/-- Ordinary completed channel, in its absolutely summable presentation. -/
abbrev MaterialGradientL1 : Type := ℓ¹(ℕ, ℂ)

def baseTwoCompletedMaterialGradient (t : ℝ) : MaterialGradientL1 :=
  ⟨criticalMaterialGradient t, by
    change Memℓp (criticalMaterialGradient t) 1
    rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
    simpa using summable_norm_criticalMaterialGradient t⟩

@[simp] theorem baseTwoCompletedMaterialGradient_apply (t : ℝ) (n : ℕ) :
    baseTwoCompletedMaterialGradient t n = criticalMaterialGradient t n := rfl

/-- The same completed ordinary coordinates also belong to the standard ℓ²
space. This does not extend the ℓ¹ summation readout continuously to ℓ². -/
def baseTwoCompletedMaterialGradientL2 (t : ℝ) : ℓ²(ℕ, ℂ) :=
  ⟨criticalMaterialGradient t,
    (lp.memℓp (baseTwoCompletedMaterialGradient t)).of_exponent_ge (by norm_num)⟩

@[simp] theorem baseTwoCompletedMaterialGradientL2_apply (t : ℝ) (n : ℕ) :
    baseTwoCompletedMaterialGradientL2 t n = baseTwoCompletedMaterialGradient t n := rfl

/-- No material coordinate is discarded: the seed and all consecutive slopes
recover the original samples. -/
theorem criticalMaterialSample_eq_seed_add_gradientPrefix (t : ℝ) (n : ℕ) :
    criticalMaterialSample t (n+1) = criticalMaterialSample t 1 +
      ∑ k ∈ Finset.range n, criticalMaterialGradient t k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih, criticalMaterialGradient]
    abel

/-- Standard product carrier, with the incoming material seed retained. -/
abbrev BaseTwoSeededGradientCarrier := ℂ × MaterialGradientL1

def baseTwoCompletedUndressedState (t : ℝ) : BaseTwoSeededGradientCarrier :=
  (criticalMaterialSample t 1, baseTwoCompletedMaterialGradient t)

theorem baseTwoCompletedUndressedState_recover (t : ℝ) (n : ℕ) :
    (baseTwoCompletedUndressedState t).1 +
      ∑ k ∈ Finset.range n, (baseTwoCompletedUndressedState t).2 k =
        criticalMaterialSample t (n+1) :=
  (criticalMaterialSample_eq_seed_add_gradientPrefix t n).symm

/-- Consecutive material edges of the already defined C2 cell. -/
def baseTwoCellLeftEdge (k : ℕ) : ℕ := baseTwoLeftLeg k - 1
def baseTwoCellRightEdge (k : ℕ) : ℕ := baseTwoCenter k - 1

@[simp] theorem baseTwoCellLeftEdge_eq (k : ℕ) : baseTwoCellLeftEdge k = 4*k+2 := by
  simp only [baseTwoCellLeftEdge, baseTwo_leftLeg_eq]; omega
@[simp] theorem baseTwoCellRightEdge_eq (k : ℕ) : baseTwoCellRightEdge k = 4*k+3 := by
  simp only [baseTwoCellRightEdge, baseTwo_center_eq]; omega

theorem baseTwoCriticalCenterCell_eq_gradientEdges (t : ℝ) (k : ℕ) :
    baseTwoCriticalCenterCell t k =
      criticalMaterialGradient t (baseTwoCellRightEdge k) -
        criticalMaterialGradient t (baseTwoCellLeftEdge k) := by
  simp only [baseTwoCriticalCenterCell, criticalMaterialGradient,
    baseTwoCellRightEdge_eq, baseTwoCellLeftEdge_eq, baseTwo_leftLeg_eq,
    baseTwo_center_eq, baseTwo_rightLeg_eq]
  have hl : 4*(k+1)-1 = 4*k+3 := by omega
  have hc : 4*(k+1) = 4*k+4 := by omega
  rw [hl, hc]
  have h1 : 4*k+4+1 = 4*k+5 := by omega
  have h2 : 4*k+3+2 = 4*k+5 := by omega
  have h3 : 4*k+3+1 = 4*k+4 := by omega
  have h4 : 4*k+2+2 = 4*k+4 := by omega
  have h5 : 4*k+2+1 = 4*k+3 := by omega
  rw [h1, h2, h3, h4, h5]
  ring

private theorem norm_summable (g : MaterialGradientL1) : Summable (fun n => ‖g n‖) := by
  simpa using g.2.summable

private def sampleGradient (e : ℕ → ℕ) (he : Function.Injective e)
    (g : MaterialGradientL1) : MaterialGradientL1 :=
  ⟨fun k => g (e k), by
    change Memℓp (fun k => g (e k)) 1
    rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_one, Real.rpow_one, Function.comp_def] using
      (norm_summable g).comp_injective he⟩

private def sampleGradientCLM (e : ℕ → ℕ) (he : Function.Injective e) :
    MaterialGradientL1 →L[ℂ] MaterialGradientL1 :=
  LinearMap.mkContinuous
    { toFun := sampleGradient e he
      map_add' _ _ := by apply lp.ext; rfl
      map_smul' _ _ := by apply lp.ext; rfl }
    1 (fun g => by
      have h := Summable.tsum_le_tsum_of_inj e he (fun _ _ => norm_nonneg _)
        (fun _ => le_rfl) ((norm_summable g).comp_injective he) (norm_summable g)
      simpa only [sampleGradient, LinearMap.coe_mk, AddHom.coe_mk, lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
        ENNReal.toReal_one, Real.rpow_one, one_div_one, one_mul] using h)

private def cellEdgeDifferenceCLM : MaterialGradientL1 →L[ℂ] MaterialGradientL1 :=
  sampleGradientCLM baseTwoCellRightEdge (by intro i j h; simp at h; omega) -
    sampleGradientCLM baseTwoCellLeftEdge (by intro i j h; simp at h; omega)

/-- The readout acts only after the complete seeded gradient vector is present.
It is bounded on ℓ¹; no claim is made that the same sum is bounded on ℓ². -/
def baseTwoCompletedUndressedReadout : BaseTwoSeededGradientCarrier →L[ℂ] ℂ :=
  ContinuousLinearMap.fst ℂ ℂ MaterialGradientL1 +
    (lp.tsumCLM ℂ ℕ ℂ).comp
      (cellEdgeDifferenceCLM.comp (ContinuousLinearMap.snd ℂ ℂ MaterialGradientL1))

theorem baseTwoCompletedUndressedReadout_apply (x : BaseTwoSeededGradientCarrier) :
    baseTwoCompletedUndressedReadout x = x.1 +
      ∑' k : ℕ, (x.2 (baseTwoCellRightEdge k) - x.2 (baseTwoCellLeftEdge k)) := by
  change x.1 + (lp.tsumCLM ℂ ℕ ℂ) (cellEdgeDifferenceCLM x.2) = _
  rw [lp.tsumCLM_apply]
  rfl

/-- Signal lift, proved locally from the existing samples and exact cells.
It is neither an assumed moment identity nor an embedding of the scalar S. -/
theorem baseTwoCompletedUndressedReadout_eq_signal (t : ℝ) :
    baseTwoCompletedUndressedReadout (baseTwoCompletedUndressedState t) =
      baseTwoCriticalCompleteSignal t := by
  rw [baseTwoCompletedUndressedReadout_apply]
  simp only [baseTwoCompletedUndressedState, baseTwoCompletedMaterialGradient_apply,
    ← baseTwoCriticalCenterCell_eq_gradientEdges]
  rfl

/-- Concrete dressing of this signal lift, using the already proved gate.
No spectral first column is inferred from the linear readout. -/
theorem baseTwoCompletedUndressedReadout_dressed_eq_response (t : ℝ) :
    baseTwoCompletedUndressedReadout
      (baseTwoVectorDressing t (baseTwoCompletedUndressedState t)) =
        baseTwoCanonicalResponse t := by
  exact (baseTwoVectorDressing_readout_eq_response_iff
    baseTwoCompletedUndressedReadout.toLinearMap _ t).mpr
    (baseTwoCompletedUndressedReadout_eq_signal t)

end GeometryOfNumbers.Analysis.BaseTwoCompletion
