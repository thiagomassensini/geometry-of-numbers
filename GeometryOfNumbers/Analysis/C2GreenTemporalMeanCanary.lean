import GeometryOfNumbers.Analysis.C2BaseTwoGreenLedger
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Temporal ledger on the existing provenance-correct source. No metric normalization. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ENNReal lp ComplexConjugate
open Filter MeasureTheory
namespace GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
open GeometryOfNumbers.Analysis GreenFrame.Concrete
open C2GlobalGreenBridge C2GreenPreStencilCanary C2BaseTwoGreenLedger

/-- Unit-modulus coordinate packaging; this does not define the source. -/
def phaseFactor (angle : ℝ) : ℂ := Complex.exp ((angle : ℂ) * Complex.I)

@[simp] theorem phaseFactor_zero : phaseFactor 0 = 1 := by simp [phaseFactor]

theorem phaseFactor_norm (angle : ℝ) : ‖phaseFactor angle‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I angle

theorem phaseFactor_add (a b : ℝ) : phaseFactor (a+b) = phaseFactor a * phaseFactor b := by
  simp [phaseFactor, add_mul, Complex.exp_add]

theorem phaseFactor_conj (a : ℝ) : conj (phaseFactor a) = phaseFactor (-a) := by
  simp [phaseFactor, ← Complex.exp_conj]

theorem phaseFactor_eq_mk (a : ℝ) :
    phaseFactor a = ⟨Real.cos a, Real.sin a⟩ := by
  apply Complex.ext
  · exact Complex.exp_ofReal_mul_I_re a
  · exact Complex.exp_ofReal_mul_I_im a

theorem realPlanePackaging_rotate (angle : ℝ) (v : RealPlaneState) :
    realPlaneToComplexIsometry (realPlaneHilbertEquiv (rotateRealPlane angle v)) =
      phaseFactor angle * realPlaneToComplexIsometry (realPlaneHilbertEquiv v) := by
  have h := realPlaneToComplexIsometry_scale_rotate 1 angle v
  simpa only [scaleRealPlane, one_mul, Complex.ofReal_one, phaseFactor_eq_mk] using h

set_option backward.isDefEq.respectTransparency false in
/-- The original source obeys its material log orbit at every material coordinate. -/
theorem c2Source_phase (t : ℝ) (V : CoreState) (n : PNat) :
    c2GlobalGreenInputIsometry t V n =
      phaseFactor (-t * Real.log (n : ℝ)) * c2GlobalGreenInputIsometry 0 V n := by
  by_cases hn : Odd (n : ℕ) ∧ 3 ≤ (n : ℕ)
  · let p : OddMaterialIndex := ⟨n,hn⟩
    change c2GlobalGreenInputIsometry t V p.val =
      phaseFactor (-t * Real.log (p.val : ℝ)) * c2GlobalGreenInputIsometry 0 V p.val
    rw [c2GlobalGreenInput_closed_form, c2GlobalGreenInput_closed_form]
    simp only [phaseFactor_eq_mk, zero_mul, neg_zero, Real.cos_zero, Real.sin_zero]
    have hmk : (⟨(1 : ℝ), (0 : ℝ)⟩ : ℂ) = 1 := rfl
    rw [hmk, mul_one]
    ring
  · have hz (s : ℝ) : c2GlobalGreenInputIsometry s V n = 0 :=
      oddMaterialToGreenState_apply_off_sector _ n hn
    rw [hz t, hz 0, mul_zero]

theorem c2Source_normSq_time (t : ℝ) (V : CoreState) (n : PNat) :
    Complex.normSq (c2GlobalGreenInputIsometry t V n) =
      Complex.normSq (c2GlobalGreenInputIsometry 0 V n) := by
  rw [c2Source_phase, Complex.normSq_mul, ← Complex.sq_norm, phaseFactor_norm]
  norm_num

theorem c2Source_coordinate_continuous (V : CoreState) (n : PNat) :
    Continuous (fun t => c2GlobalGreenInputIsometry t V n) := by
  rw [show (fun t => c2GlobalGreenInputIsometry t V n) =
    (fun t => phaseFactor (-t * Real.log (n : ℝ)) * c2GlobalGreenInputIsometry 0 V n) from
      funext (fun t => c2Source_phase t V n)]
  unfold phaseFactor
  fun_prop

def eventGreenDefect (t : ℝ) (V : CoreState) (e : GreenEvent) : ℝ :=
  Complex.normSq (greenCoordinate canonicalCarryInfinitePartition e (c2GlobalGreenInputIsometry t V)) -
  Complex.normSq (directGreenCoordinate canonicalCarryInfinitePartition e (c2GlobalGreenInputIsometry t V))

/-- Only the first- and second-ancestor quadratic energies remain on the diagonal. -/
def eventDiagonalDefect (V : CoreState) (e : GreenEvent) : ℝ :=
  greenEventMass canonicalCarryInfinitePartition e *
    (Complex.normSq (parentTerm e (c2GlobalGreenInputIsometry 0 V)) +
     Complex.normSq (grandparentTerm e (c2GlobalGreenInputIsometry 0 V)))

def eventCrossDefect (t : ℝ) (V : CoreState) (e : GreenEvent) : ℝ :=
  let f := c2GlobalGreenInputIsometry t V
  2 * greenEventMass canonicalCarryInfinitePartition e *
    ((currentTerm e f * conj (parentTerm e f)).re +
     (currentTerm e f * conj (grandparentTerm e f)).re +
     (parentTerm e f * conj (grandparentTerm e f)).re)

theorem eventDiagonalDefect_nonneg (V : CoreState) (e : GreenEvent) :
    0 ≤ eventDiagonalDefect V e := by
  exact mul_nonneg (greenEventMass_nonneg _ _) (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

private theorem ancestor_normSq_time (t : ℝ) (V : CoreState) (e : GreenEvent) :
    Complex.normSq (parentTerm e (c2GlobalGreenInputIsometry t V)) +
      Complex.normSq (grandparentTerm e (c2GlobalGreenInputIsometry t V)) =
    Complex.normSq (parentTerm e (c2GlobalGreenInputIsometry 0 V)) +
      Complex.normSq (grandparentTerm e (c2GlobalGreenInputIsometry 0 V)) := by
  unfold parentTerm grandparentTerm
  split_ifs <;> simp only [Complex.normSq_neg, Complex.normSq_mul, c2Source_normSq_time]

private theorem normSq_three (x y z : ℂ) :
    Complex.normSq (x+y+z) - Complex.normSq x =
      Complex.normSq y + Complex.normSq z +
        2*((x*conj y).re+(x*conj z).re+(y*conj z).re) := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
  ring

theorem eventGreenDefect_eq_diagonal_add_cross (t : ℝ) (V : CoreState) (e : GreenEvent) :
    eventGreenDefect t V e = eventDiagonalDefect V e + eventCrossDefect t V e := by
  unfold eventGreenDefect eventDiagonalDefect eventCrossDefect
  rw [greenCoordinate_normSq_eq, directGreenCoordinate_normSq_eq]
  rw [← mul_sub, verticalGreenStencil, ← currentTerm, normSq_three, mul_add,
    ancestor_normSq_time]
  ring

theorem eventDiagonalDefect_eq_explicit (V : CoreState) (e : GreenEvent) :
    eventDiagonalDefect V e = greenEventMass canonicalCarryInfinitePartition e *
      (4 * carryRatio e.1 ^ 2 * Complex.normSq (c2GlobalGreenInputIsometry 0 V e.2) +
       if HasGrandparent e then carryRatio e.1 ^ 4 *
         Complex.normSq (c2GlobalGreenInputIsometry 0 V (grandparentIndex e)) else 0) := by
  unfold eventDiagonalDefect parentTerm grandparentTerm
  split_ifs <;> simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal, Complex.normSq_zero] <;> ring

/-- Cesaro mean on the interval from zero to positive time; its value at zero is harmless. -/
def temporalMean (h : ℝ → ℝ) (T : ℝ) : ℝ := T⁻¹ * ∫ t in 0..T, h t

def complexTemporalMean (h : ℝ → ℂ) (T : ℝ) : ℂ := (T : ℂ)⁻¹ * ∫ t in 0..T, h t

/-- Every nonzero real frequency has zero complex temporal mean. -/
theorem phaseFactor_timeAverage (omega : ℝ) (hw : omega ≠ 0) :
    Tendsto (complexTemporalMean (fun t => phaseFactor (omega*t))) atTop (nhds 0) := by
  let c : ℂ := (omega : ℂ) * Complex.I
  have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hw) Complex.I_ne_zero
  have hlim : Tendsto (fun T : ℝ => (2 / ‖c‖) * T⁻¹) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (nhds 0)).const_mul (2 / ‖c‖)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hex : (fun t : ℝ => phaseFactor (omega*t)) = (fun t : ℝ => Complex.exp (c*t)) := by
    funext t
    simp only [phaseFactor, c, Complex.ofReal_mul]
    congr 1
    ring
  unfold complexTemporalMean
  rw [hex, integral_exp_mul_complex hc, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hT.le, norm_div]
  have hn : ‖Complex.exp (c*T) - Complex.exp (c*0)‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (c*T)‖ + ‖Complex.exp (c*0)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [← congrFun hex T]
        norm_num [phaseFactor_norm]
  have hcpos := norm_pos_iff.mpr hc
  calc
    T⁻¹ * (‖Complex.exp (c*T) - Complex.exp (c*0)‖ / ‖c‖) ≤
      T⁻¹ * (2 / ‖c‖) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn hcpos.le) (inv_nonneg.mpr hT.le)
    _ = _ := by ring

/-- Cross energy at a single fixed, nonzero frequency averages to zero. -/
def oscillatoryCross (omega : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  (phaseFactor (-t*omega) * z).re

theorem oscillatoryCross_continuous (omega : ℝ) (z : ℂ) : Continuous (oscillatoryCross omega z) := by
  unfold oscillatoryCross phaseFactor
  fun_prop

theorem oscillatoryCross_timeAverage (omega : ℝ) (hw : omega ≠ 0) (z : ℂ) :
    Tendsto (temporalMean (oscillatoryCross omega z)) atTop (nhds 0) := by
  have hh : Tendsto (fun T => complexTemporalMean (fun t => phaseFactor ((-omega)*t)) T * z)
      atTop (nhds (0 : ℂ)) := by
    simpa using (phaseFactor_timeAverage (-omega) (neg_ne_zero.mpr hw)).mul_const z
  have hr : Tendsto (fun T => (complexTemporalMean (fun t => phaseFactor ((-omega)*t)) T * z).re)
      atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, Complex.zero_re] using (Complex.continuous_re.tendsto 0).comp hh
  convert hr using 1
  funext T
  have hi : IntervalIntegrable (fun t : ℝ => phaseFactor ((-omega)*t) * z) volume 0 T := by
    apply Continuous.intervalIntegrable
    unfold phaseFactor
    fun_prop
  have hre := Complex.reCLM.intervalIntegral_comp_comm hi
  change T⁻¹ * (∫ t in 0..T, (phaseFactor (-t*omega)*z).re) =
    (((T : ℂ)⁻¹ * (∫ t in 0..T, phaseFactor ((-omega)*t))) * z).re
  rw [mul_assoc, ← intervalIntegral.integral_mul_const, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change _ = T⁻¹ * Complex.reCLM (∫ t in 0..T, phaseFactor ((-omega)*t)*z)
  rw [← hre]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change (phaseFactor (-t*omega)*z).re = (phaseFactor ((-omega)*t)*z).re
  congr 3
  ring

private theorem rotatingProduct (t a b : ℝ) (x y : ℂ) :
    (phaseFactor (-t*a)*x) * conj (phaseFactor (-t*b)*y) =
      phaseFactor (-t*(a-b)) * (x*conj y) := by
  rw [map_mul, phaseFactor_conj]
  calc
    _ = (phaseFactor (-t*a)*phaseFactor (-(-t*b))) * (x*conj y) := by ring
    _ = _ := by rw [← phaseFactor_add]; congr 2; ring

private theorem log_current (e : GreenEvent) :
    Real.log (eventNumber e : ℝ) = Real.log (baseReal e.1) + Real.log (e.2 : ℝ) := by
  change Real.log (((baseNat e.1 * (e.2 : ℕ) : ℕ) : ℝ)) = _
  rw [Nat.cast_mul]
  exact Real.log_mul (baseReal_pos e.1).ne' (by exact_mod_cast (PNat.ne_zero e.2))

private theorem log_parent {e : GreenEvent} (h : HasGrandparent e) :
    Real.log (e.2 : ℝ) = Real.log (baseReal e.1) + Real.log (grandparentIndex e : ℝ) := by
  rw [← base_mul_grandparentIndex h]
  change Real.log (((baseNat e.1 * (grandparentIndex e : ℕ) : ℕ) : ℝ)) = _
  rw [Nat.cast_mul]
  exact Real.log_mul (baseReal_pos e.1).ne' (by exact_mod_cast (PNat.ne_zero (grandparentIndex e)))

theorem camera_log_frequency_pos (r : ℕ) : 0 < Real.log (baseReal r) := by
  apply Real.log_pos
  change (1 : ℝ) < ((baseNat r : ℕ) : ℝ)
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (baseNat_ge_two r))

private theorem parent_phase (t : ℝ) (V : CoreState) (e : GreenEvent) :
    parentTerm e (c2GlobalGreenInputIsometry t V) =
      phaseFactor (-t * Real.log (e.2 : ℝ)) * parentTerm e (c2GlobalGreenInputIsometry 0 V) := by
  unfold parentTerm
  rw [c2Source_phase]
  ring

private theorem grandparent_phase (t : ℝ) (V : CoreState) (e : GreenEvent) :
    grandparentTerm e (c2GlobalGreenInputIsometry t V) =
      phaseFactor (-t * Real.log (grandparentIndex e : ℝ)) *
        grandparentTerm e (c2GlobalGreenInputIsometry 0 V) := by
  unfold grandparentTerm
  split_ifs
  · rw [c2Source_phase]; ring
  · simp

/-- Exactly the two nonzero material frequencies log(b) and 2 log(b). -/
theorem eventCrossDefect_eq_frequencies (t : ℝ) (V : CoreState) (e : GreenEvent) :
    eventCrossDefect t V e = 2 * greenEventMass canonicalCarryInfinitePartition e *
      (oscillatoryCross (Real.log (baseReal e.1))
        (currentTerm e (c2GlobalGreenInputIsometry 0 V) * conj (parentTerm e (c2GlobalGreenInputIsometry 0 V))) t +
       if HasGrandparent e then
         oscillatoryCross (2 * Real.log (baseReal e.1))
           (currentTerm e (c2GlobalGreenInputIsometry 0 V) * conj (grandparentTerm e (c2GlobalGreenInputIsometry 0 V))) t +
         oscillatoryCross (Real.log (baseReal e.1))
           (parentTerm e (c2GlobalGreenInputIsometry 0 V) * conj (grandparentTerm e (c2GlobalGreenInputIsometry 0 V))) t
       else 0) := by
  unfold eventCrossDefect
  simp only [currentTerm]
  rw [c2Source_phase t V (eventNumber e), parent_phase, grandparent_phase]
  rw [rotatingProduct, rotatingProduct, rotatingProduct]
  have hc : Real.log (eventNumber e : ℝ) - Real.log (e.2 : ℝ) = Real.log (baseReal e.1) := by
    rw [log_current]; ring
  rw [hc]
  by_cases h : HasGrandparent e
  · have hcgp : Real.log (eventNumber e : ℝ) - Real.log (grandparentIndex e : ℝ) = 2*Real.log (baseReal e.1) := by
      rw [log_current, log_parent h]; ring
    have hpgp : Real.log (e.2 : ℝ) - Real.log (grandparentIndex e : ℝ) = Real.log (baseReal e.1) := by
      rw [log_parent h]; ring
    simp only [h, if_pos, hcgp, hpgp, oscillatoryCross]
    ring
  · simp [h, grandparentTerm, oscillatoryCross]

private theorem temporalMean_add (h g : ℝ → ℝ) (hc : Continuous h) (gc : Continuous g) (T : ℝ) :
    temporalMean (fun t => h t + g t) T = temporalMean h T + temporalMean g T := by
  unfold temporalMean
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (gc.intervalIntegrable _ _)]
  ring

private theorem temporalMean_const_mul (a : ℝ) (h : ℝ → ℝ) (T : ℝ) :
    temporalMean (fun t => a * h t) T = a * temporalMean h T := by
  unfold temporalMean
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem temporalMean_const_limit (a : ℝ) :
    Tendsto (temporalMean (fun _ => a)) atTop (nhds a) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp [temporalMean, intervalIntegral.integral_const, hT.ne']

theorem eventCrossDefect_continuous (V : CoreState) (e : GreenEvent) :
    Continuous (fun t => eventCrossDefect t V e) := by
  simp_rw [eventCrossDefect_eq_frequencies]
  by_cases h : HasGrandparent e
  · simp only [h, ↓reduceIte]
    exact continuous_const.mul ((oscillatoryCross_continuous _ _).add
      ((oscillatoryCross_continuous _ _).add (oscillatoryCross_continuous _ _)))
  · simp only [h, ↓reduceIte, add_zero]
    exact continuous_const.mul (oscillatoryCross_continuous _ _)

/-- No assumption about independence between logarithms is needed. -/
theorem eventCrossDefect_timeAverage (V : CoreState) (e : GreenEvent) :
    Tendsto (temporalMean (fun t => eventCrossDefect t V e)) atTop (nhds 0) := by
  change Tendsto (fun T => temporalMean (fun t => eventCrossDefect t V e) T) atTop (nhds 0)
  have hw := (camera_log_frequency_pos e.1).ne'
  have h2w : 2 * Real.log (baseReal e.1) ≠ 0 := mul_ne_zero (by norm_num) hw
  simp_rw [eventCrossDefect_eq_frequencies, temporalMean_const_mul]
  by_cases h : HasGrandparent e
  · simp only [h, ↓reduceIte]
    let a := oscillatoryCross (Real.log (baseReal e.1))
      (currentTerm e (c2GlobalGreenInputIsometry 0 V) * conj (parentTerm e (c2GlobalGreenInputIsometry 0 V)))
    let b := oscillatoryCross (2 * Real.log (baseReal e.1))
      (currentTerm e (c2GlobalGreenInputIsometry 0 V) * conj (grandparentTerm e (c2GlobalGreenInputIsometry 0 V)))
    let c := oscillatoryCross (Real.log (baseReal e.1))
      (parentTerm e (c2GlobalGreenInputIsometry 0 V) * conj (grandparentTerm e (c2GlobalGreenInputIsometry 0 V)))
    have ha : Continuous a := oscillatoryCross_continuous _ _
    have hb : Continuous b := oscillatoryCross_continuous _ _
    have hc : Continuous c := oscillatoryCross_continuous _ _
    change Tendsto (fun T => 2*greenEventMass canonicalCarryInfinitePartition e *
      temporalMean (fun t => a t + (b t + c t)) T) atTop (nhds 0)
    simp_rw [temporalMean_add a (fun t => b t + c t) ha (hb.add hc),
      temporalMean_add b c hb hc]
    have hla : Tendsto (temporalMean a) atTop (nhds 0) := oscillatoryCross_timeAverage _ hw _
    have hlb : Tendsto (temporalMean b) atTop (nhds 0) := oscillatoryCross_timeAverage _ h2w _
    have hlc : Tendsto (temporalMean c) atTop (nhds 0) := oscillatoryCross_timeAverage _ hw _
    simpa only [add_zero, mul_zero] using (hla.add (hlb.add hlc)).const_mul
      (2 * greenEventMass canonicalCarryInfinitePartition e)

  · simp only [h, ↓reduceIte, add_zero]
    simpa using (oscillatoryCross_timeAverage _ hw _).const_mul
      (2 * greenEventMass canonicalCarryInfinitePartition e)

theorem eventGreenDefect_continuous (V : CoreState) (e : GreenEvent) :
    Continuous (fun t => eventGreenDefect t V e) := by
  simp_rw [eventGreenDefect_eq_diagonal_add_cross]
  exact continuous_const.add (eventCrossDefect_continuous _ _)

theorem eventGreenDefect_timeAverage (V : CoreState) (e : GreenEvent) :
    Tendsto (temporalMean (fun t => eventGreenDefect t V e)) atTop (nhds (eventDiagonalDefect V e)) := by
  change Tendsto (fun T => temporalMean (fun t => eventGreenDefect t V e) T) atTop (nhds _)
  simp_rw [eventGreenDefect_eq_diagonal_add_cross,
    temporalMean_add _ _ continuous_const (eventCrossDefect_continuous _ _)]
  simpa using (temporalMean_const_limit (eventDiagonalDefect V e)).add (eventCrossDefect_timeAverage V e)

/-- Finite-section temporal mean, including all three cross terms. -/
theorem finiteGreenDefect_timeAverage (F : Finset GreenEvent) (V : CoreState) :
    Tendsto (temporalMean (fun t => ∑ e ∈ F, eventGreenDefect t V e)) atTop
      (nhds (∑ e ∈ F, eventDiagonalDefect V e)) := by
  change Tendsto (fun T => temporalMean (fun t => ∑ e ∈ F, eventGreenDefect t V e) T) atTop (nhds _)
  have heq (T : ℝ) : temporalMean (fun t => ∑ e ∈ F, eventGreenDefect t V e) T =
      ∑ e ∈ F, temporalMean (fun t => eventGreenDefect t V e) T := by
    unfold temporalMean
    rw [intervalIntegral.integral_finsetSum (fun e _ => (eventGreenDefect_continuous V e).intervalIntegrable _ _)]
    exact Finset.mul_sum _ _ _
  simp_rw [heq]
  exact tendsto_finsetSum F (fun e _ => eventGreenDefect_timeAverage V e)

/-- The existing Bessel majorant has a time-independent profile on this source. -/
theorem greenMajorant_c2Source_time (t : ℝ) (V : CoreState) (e : GreenEvent) :
    greenCoordinateMajorant canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V) e =
    greenCoordinateMajorant canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry 0 V) e := by
  unfold greenCoordinateMajorant currentGreenMajorant currentCameraMajorant
    parentGreenMajorant grandparentGreenMajorant stateEnergy
  simp only [c2Source_normSq_time]

private theorem direct_normSq_le_majorant (f : State) (e : GreenEvent) :
    Complex.normSq (directGreenCoordinate canonicalCarryInfinitePartition e f) ≤
      greenCoordinateMajorant canonicalCarryInfinitePartition f e := by
  have he : currentGreenMajorant canonicalCarryInfinitePartition f e =
      3 * Complex.normSq (directGreenCoordinate canonicalCarryInfinitePartition e f) := by
    rw [directGreenCoordinate_normSq_eq]
    unfold currentGreenMajorant currentCameraMajorant greenEventMass stateEnergy
    ring
  have hp := parentGreenMajorant_nonneg canonicalCarryInfinitePartition f e
  have hg := grandparentGreenMajorant_nonneg canonicalCarryInfinitePartition f e
  have hn := Complex.normSq_nonneg (directGreenCoordinate canonicalCarryInfinitePartition e f)
  unfold greenCoordinateMajorant
  rw [he]
  linarith

/-- Uniform in all real times, with a summable bound inherited from Green Bessel. -/
def eventUniformBound (V : CoreState) (e : GreenEvent) : ℝ :=
  2 * greenCoordinateMajorant canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry 0 V) e

theorem eventUniformBound_summable (V : CoreState) : Summable (eventUniformBound V) :=
  (greenCoordinateMajorant_summable canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry 0 V)).mul_left 2

theorem eventGreenDefect_uniform_bound (t : ℝ) (V : CoreState) (e : GreenEvent) :
    ‖eventGreenDefect t V e‖ ≤ eventUniformBound V e := by
  unfold eventGreenDefect eventUniformBound
  calc
    _ ≤ ‖Complex.normSq (greenCoordinate canonicalCarryInfinitePartition e (c2GlobalGreenInputIsometry t V))‖ +
      ‖Complex.normSq (directGreenCoordinate canonicalCarryInfinitePartition e (c2GlobalGreenInputIsometry t V))‖ := norm_sub_le _ _
    _ ≤ 2 * greenCoordinateMajorant canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V) e := by
      rw [Real.norm_of_nonneg (Complex.normSq_nonneg _), Real.norm_of_nonneg (Complex.normSq_nonneg _)]
      have ha := greenCoordinate_normSq_le_majorant canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V) e
      have hd := direct_normSq_le_majorant (c2GlobalGreenInputIsometry t V) e
      linarith
    _ = _ := by rw [greenMajorant_c2Source_time]

private theorem temporalMean_uniform_bound (h : ℝ → ℝ) (B T : ℝ) (hT : 0 < T)
    (hb : ∀ t, ‖h t‖ ≤ B) : ‖temporalMean h T‖ ≤ B := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (fun t _ => hb t)
  simp only [sub_zero, abs_of_pos hT] at hi
  unfold temporalMean
  rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
  calc
    _ ≤ T⁻¹ * (B * T) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hT.le)
    _ = B := by field_simp

theorem eventDiagonalDefect_summable (V : CoreState) : Summable (eventDiagonalDefect V) := by
  apply (eventUniformBound_summable V).of_norm_bounded
  intro e
  apply le_of_tendsto ((eventGreenDefect_timeAverage V e).norm)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact temporalMean_uniform_bound _ _ _ hT (fun t => eventGreenDefect_uniform_bound t V e)

theorem eventGreenDefect_summable (t : ℝ) (V : CoreState) : Summable (eventGreenDefect t V) :=
  (eventUniformBound_summable V).of_norm_bounded (fun e => eventGreenDefect_uniform_bound t V e)

/-- The event ledger sums to exactly the original restricted raw metric defect. -/
theorem rawGreenDefect_eq_tsum_event (t : ℝ) (V : CoreState) :
    c2GlobalRawGreenDefect t V = ∑' e, eventGreenDefect t V e := by
  rw [c2GlobalRawGreenDefect_eq_stencil_defect]
  rw [← residualL2_normSq_tsum_eq_norm_sq, ← residualL2_normSq_tsum_eq_norm_sq]
  rw [← (residualL2_normSq_summable (greenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V))).tsum_sub
    (residualL2_normSq_summable (directGreenAnalysis canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t V)))]
  rfl

/-- A uniformly summable majorant justifies exchanging integral and event sum. -/
private theorem temporalMean_tsum {ι : Type*} [Countable ι]
    (h : ι → ℝ → ℝ) (B : ι → ℝ) (hc : ∀ i, Continuous (h i))
    (hs : Summable B) (hb : ∀ i t, ‖h i t‖ ≤ B i) (T : ℝ) (hT : 0 < T) :
    temporalMean (fun t => ∑' i, h i t) T = ∑' i, temporalMean (h i) T := by
  have hi (i : ι) : Integrable (h i) (volume.restrict (Set.Ioc 0 T)) :=
    ((hc i).intervalIntegrable 0 T).1
  have hsn : Summable (fun i => ∫ t in Set.Ioc 0 T, ‖h i t‖) := by
    apply (hs.mul_right T).of_nonneg_of_le
    · intro i
      exact integral_nonneg (fun t => norm_nonneg _)
    · intro i
      calc
        _ ≤ ‖∫ t in Set.Ioc 0 T, ‖h i t‖‖ := Real.le_norm_self _
        _ = ‖∫ t in 0..T, ‖h i t‖‖ := by rw [intervalIntegral.integral_of_le hT.le]
        _ ≤ B i * T := by
          simpa only [sub_zero, abs_of_pos hT] using
            (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
              (fun t _ => by simpa only [norm_norm] using hb i t))
  unfold temporalMean
  rw [intervalIntegral.integral_of_le hT.le,
    ← integral_tsum_of_summable_integral_norm hi hsn, tsum_mul_left]
  congr 1
  apply tsum_congr
  intro i
  rw [intervalIntegral.integral_of_le hT.le]

/-- Global temporal mean: the infinite exchange uses a proved uniform Bessel bound. -/
theorem globalGreenDefect_timeAverage (V : CoreState) :
    Tendsto (temporalMean (fun t => c2GlobalRawGreenDefect t V)) atTop
      (nhds (∑' e, eventDiagonalDefect V e)) := by
  have hlim : Tendsto (fun T => ∑' e, temporalMean (fun t => eventGreenDefect t V e) T) atTop
      (nhds (∑' e, eventDiagonalDefect V e)) := by
    apply tendsto_tsum_of_dominated_convergence (eventUniformBound_summable V)
      (fun e => eventGreenDefect_timeAverage V e)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT e
    exact temporalMean_uniform_bound _ _ _ hT (fun t => eventGreenDefect_uniform_bound t V e)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [temporalMean, rawGreenDefect_eq_tsum_event]
  exact (temporalMean_tsum (fun e t => eventGreenDefect t V e) (eventUniformBound V)
    (eventGreenDefect_continuous V) (eventUniformBound_summable V)
    (fun e t => eventGreenDefect_uniform_bound t V e) T hT).symm


theorem eventDiagonalDefect_uniform_bound (V : CoreState) (e : GreenEvent) :
    ‖eventDiagonalDefect V e‖ ≤ eventUniformBound V e := by
  apply le_of_tendsto ((eventGreenDefect_timeAverage V e).norm)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact temporalMean_uniform_bound _ _ _ hT (fun t => eventGreenDefect_uniform_bound t V e)

/-- The oscillatory terms themselves also have a summable bound, uniform in time. -/
theorem eventCrossDefect_uniform_bound (t : ℝ) (V : CoreState) (e : GreenEvent) :
    ‖eventCrossDefect t V e‖ ≤ 2 * eventUniformBound V e := by
  have he := eventGreenDefect_eq_diagonal_add_cross t V e
  have hx : eventCrossDefect t V e = eventGreenDefect t V e - eventDiagonalDefect V e := by linarith
  rw [hx]
  exact (norm_sub_le _ _).trans (by
    have h1 := eventGreenDefect_uniform_bound t V e
    have h2 := eventDiagonalDefect_uniform_bound V e
    linarith)

theorem eventCrossDefect_summable (t : ℝ) (V : CoreState) : Summable (eventCrossDefect t V) :=
  ((eventUniformBound_summable V).mul_left 2).of_norm_bounded (fun e => eventCrossDefect_uniform_bound t V e)

theorem rawGreenDefect_eq_diagonal_add_cross_tsum (t : ℝ) (V : CoreState) :
    c2GlobalRawGreenDefect t V =
      (∑' e, eventDiagonalDefect V e) + ∑' e, eventCrossDefect t V e := by
  rw [rawGreenDefect_eq_tsum_event]
  simp_rw [eventGreenDefect_eq_diagonal_add_cross]
  exact (eventDiagonalDefect_summable V).tsum_add (eventCrossDefect_summable t V)

/-- Even the complete infinite cross ledger averages to zero. -/
theorem globalCrossDefect_timeAverage (V : CoreState) :
    Tendsto (temporalMean (fun t => ∑' e, eventCrossDefect t V e)) atTop (nhds 0) := by
  have hlim : Tendsto (fun T => ∑' e, temporalMean (fun t => eventCrossDefect t V e) T) atTop (nhds 0) := by
    have hz : (∑' _ : GreenEvent, (0 : ℝ)) = 0 := tsum_zero
    rw [← hz]
    apply tendsto_tsum_of_dominated_convergence ((eventUniformBound_summable V).mul_left 2)
      (fun e => eventCrossDefect_timeAverage V e)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT e
    exact temporalMean_uniform_bound _ _ _ hT (fun t => eventCrossDefect_uniform_bound t V e)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact (temporalMean_tsum (fun e t => eventCrossDefect t V e) (fun e => 2*eventUniformBound V e)
    (eventCrossDefect_continuous V) ((eventUniformBound_summable V).mul_left 2)
    (fun e t => eventCrossDefect_uniform_bound t V e) T hT).symm

/-- Camera two is constant in time, and the temporal mean reproduces its earlier ledger. -/
theorem baseTwoDefect_timeAverage (V : CoreState) :
    Tendsto (temporalMean (fun t => baseTwoDefect t V)) atTop (nhds (baseTwoDefect 0 V)) := by
  have he : (fun t => baseTwoDefect t V) = (fun _ => baseTwoDefect 0 V) :=
    funext (fun t => baseTwoDefect_independent_time t 0 V)
  rw [he]
  exact temporalMean_const_limit _

/-- On camera two no cross product survives: current is even and either parent
is even or the second-ancestor term is absent. -/
theorem eventCrossDefect_baseTwo_eq_zero (t : ℝ) (V : CoreState) (p : PNat) :
    eventCrossDefect t V (0,p) = 0 := by
  have hc : currentTerm (0,p) (c2GlobalGreenInputIsometry t V) = 0 :=
    c2GlobalGreenInput_even_eq_zero t V p
  dsimp only [eventCrossDefect]
  rw [hc]
  by_cases h : HasGrandparent (0,p)
  · have hp : parentTerm (0,p) (c2GlobalGreenInputIsometry t V) = 0 := by
      unfold parentTerm
      rw [← base_mul_grandparentIndex h]
      simp only [baseTwo_positive_code, c2GlobalGreenInput_even_eq_zero, mul_zero, neg_zero]
    simp [hp]
  · simp [grandparentTerm, h]

theorem eventDiagonalDefect_baseTwo_eq_green (V : CoreState) (p : PNat) :
    eventDiagonalDefect V (0,p) =
      Complex.normSq (greenCoordinate canonicalCarryInfinitePartition (0,p) (c2GlobalGreenInputIsometry 0 V)) := by
  have he := eventGreenDefect_eq_diagonal_add_cross 0 V (0,p)
  rw [eventCrossDefect_baseTwo_eq_zero, add_zero] at he
  unfold eventGreenDefect at he
  rw [directGreenCoordinate_baseTwo_c2Source_eq_zero, Complex.normSq_zero, sub_zero] at he
  exact he.symm

/-- The earlier positive camera-two ledger is a sub-ledger of the temporal diagonal. -/
theorem baseTwoDefect_le_totalDiagonal (V : CoreState) :
    baseTwoDefect 0 V ≤ ∑' e, eventDiagonalDefect V e := by
  rw [baseTwoDefect_eq_stencilEnergy, ← residualL2_normSq_tsum_eq_norm_sq]
  apply (residualL2_normSq_summable _).tsum_le_tsum _ (eventDiagonalDefect_summable V)
  intro e
  rcases e with ⟨r,p⟩
  by_cases hr : r = 0
  · subst r
    change Complex.normSq (greenCoordinate canonicalCarryInfinitePartition (0,p)
      (c2GlobalGreenInputIsometry 0 V)) ≤ eventDiagonalDefect V (0,p)
    exact (eventDiagonalDefect_baseTwo_eq_green V p).symm.le
  · rw [baseTwoGreenProjection_apply, if_neg hr, Complex.normSq_zero]
    exact eventDiagonalDefect_nonneg V (r,p)

theorem totalDiagonal_pos (V : CoreState) (hV : V ≠ 0) :
    0 < ∑' e, eventDiagonalDefect V e :=
  lt_of_lt_of_le (baseTwoDefect_pos 0 V hV) (baseTwoDefect_le_totalDiagonal V)

/-- The global mean is strictly positive for every nonzero upstream core state. -/
theorem globalGreenDefect_timeAverage_positive (V : CoreState) (hV : V ≠ 0) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (temporalMean (fun t => c2GlobalRawGreenDefect t V)) atTop (nhds L) :=
  ⟨∑' e, eventDiagonalDefect V e, totalDiagonal_pos V hV, globalGreenDefect_timeAverage V⟩

/-- A positive mean rules out compensation at every time; a positive witness exists. -/
theorem exists_time_rawGreenDefect_pos (V : CoreState) (hV : V ≠ 0) :
    ∃ t : ℝ, 0 < c2GlobalRawGreenDefect t V := by
  by_contra h
  have hd (t : ℝ) : c2GlobalRawGreenDefect t V ≤ 0 :=
    le_of_not_gt (fun ht => h ⟨t,ht⟩)
  have hmean : ∀ᶠ T : ℝ in atTop, temporalMean (fun t => c2GlobalRawGreenDefect t V) T ≤ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume) hT.le (fun t => neg_nonneg.mpr (hd t))
    rw [intervalIntegral.integral_neg] at hi
    unfold temporalMean
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hT.le) (by linarith)
  have hl := le_of_tendsto (globalGreenDefect_timeAverage V) hmean
  exact (not_le_of_gt (totalDiagonal_pos V hV)) hl

theorem exists_time_rawGreenDefect_ne_zero (V : CoreState) (hV : V ≠ 0) :
    ∃ t : ℝ, c2GlobalRawGreenDefect t V ≠ 0 := by
  obtain ⟨t,ht⟩ := exists_time_rawGreenDefect_pos V hV
  exact ⟨t,ht.ne'⟩

theorem exists_time_restrictedGram_ne_identity (V : CoreState) (hV : V ≠ 0) :
    ∃ t : ℝ, c2GlobalRestrictedGreenGram t ≠ 1 := by
  obtain ⟨t,ht⟩ := exists_time_rawGreenDefect_ne_zero V hV
  refine ⟨t,fun hg => ht ?_⟩
  exact (c2GlobalRestrictedGreenGram_eq_one_iff_defect_zero t).mp hg V

/-- Uniform raw isometry is impossible. This makes no claim at each fixed time. -/
theorem not_forall_restrictedGram_eq_identity :
    ¬ (∀ t : ℝ, c2GlobalRestrictedGreenGram t = 1) := by
  let m : PositiveOddCore := ⟨1, by norm_num, by norm_num⟩
  let v : RealPlaneHilbert := realPlaneHilbertEquiv (1,0)
  let V : CoreState := lp.single 2 m v
  have hV : V ≠ 0 := by
    intro hz
    have h := congrArg (fun X : CoreState => realPlaneHilbertEquiv.symm (X m)) hz
    simp [V, v] at h
  obtain ⟨t,ht⟩ := exists_time_restrictedGram_ne_identity V hV
  exact fun hall => ht (hall t)

end GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
