import GeometryOfNumbers.Analysis.FiniteMaterialClockJets
import GeometryOfNumbers.Analysis.RealDiscreteValve
import GeometryOfNumbers.Analysis.OddCameraQuadraticCrosswalk
import GeometryOfNumbers.Analysis.PrimeCarryVoice
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries

/-! Exact completion of the existing critical material head by whole camera cells.
The material amplitude here is the existing historicalInitialState, not a
branch-depth amplitude. No downstream scalar completion is identified. -/

noncomputable section
open scoped BigOperators
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GeometryOfNumbers.Geometry
open GeometryOfNumbers.Analysis.NativeMaterialClock
open GeometryOfNumbers.Analysis.FiniteClockJets

/-- Pointwise extension of the existing finite initial-state orbit. -/
def criticalMaterialSample (t : ℝ) (n : ℕ) : ℂ :=
  ((Real.sqrt (n : ℝ))⁻¹ : ℝ) *
    Complex.exp (-(((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I))

theorem criticalMaterialSample_eq_finiteMaterialOrbit {N : ℕ} (t : ℝ) (j : Fin N) :
    criticalMaterialSample t (j.val + 1) =
      finiteMaterialOrbit N t (historicalInitialState N) j := by
  simp only [criticalMaterialSample, finiteMaterialOrbit, finiteRealSpectralEvolution_apply,
    historicalInitialState, finiteRealSpectralPhase, finiteRealSpectralFrequency]
  exact mul_comm _ _

/-- Center spacing is inherited from the existing exceptional camera convention. -/
def baseTwoCenter (k : ℕ) : ℕ := historicalCameraPeriod 2 * (k + 1)
def baseTwoLeftLeg (k : ℕ) : ℕ :=
  (leftLeg (baseTwoCenter k : ℤ) (positiveCameraRadius (0 : Fin 1))).toNat
def baseTwoRightLeg (k : ℕ) : ℕ :=
  (rightLeg (baseTwoCenter k : ℤ) (positiveCameraRadius (0 : Fin 1))).toNat

@[simp] theorem baseTwo_center_eq (k : ℕ) : baseTwoCenter k = 4 * (k + 1) := rfl
@[simp] theorem baseTwo_leftLeg_eq (k : ℕ) : baseTwoLeftLeg k = 4 * (k + 1) - 1 := by
  unfold baseTwoLeftLeg leftLeg positiveCameraRadius
  simp only [Fin.val_zero, Nat.zero_add, Int.natCast_one, baseTwo_center_eq]
  omega
@[simp] theorem baseTwo_rightLeg_eq (k : ℕ) : baseTwoRightLeg k = 4 * (k + 1) + 1 := by
  unfold baseTwoRightLeg rightLeg positiveCameraRadius
  simp only [Fin.val_zero, Nat.zero_add, Int.natCast_one, baseTwo_center_eq]
  omega

/-- Read the geometric legs and center, before any analytic estimate. -/
def baseTwoCriticalCenterCell (t : ℝ) (k : ℕ) : ℂ :=
  criticalMaterialSample t (baseTwoLeftLeg k) -
    2 * criticalMaterialSample t (baseTwoCenter k) +
    criticalMaterialSample t (baseTwoRightLeg k)

theorem baseTwoCriticalCenterCell_eq_causalUnitBracket (t : ℝ) (k : ℕ) :
    baseTwoCriticalCenterCell t k =
      causalUnitBracket (criticalMaterialSample t) (baseTwoLeftLeg k) := by
  have hc : baseTwoLeftLeg k + 1 = baseTwoCenter k := by simp; omega
  have hr : baseTwoLeftLeg k + 2 = baseTwoRightLeg k := by simp; omega
  simp only [baseTwoCriticalCenterCell, causalUnitBracket, hc, hr, nsmul_eq_mul, Nat.cast_ofNat]

/-- Seed and a prefix of complete geometric cells. -/
def baseTwoFiniteHead (cutoff : ℕ) (t : ℝ) : ℂ :=
  criticalMaterialSample t 1 + ∑ k ∈ Finset.range cutoff, baseTwoCriticalCenterCell t k

@[simp] theorem baseTwo_headDimension (M : ℕ) : historicalHeadDimension 2 M = 4 * M + 1 := rfl

theorem baseTwo_retained_cell_in_head {M k : ℕ} (hk : k < M) :
    1 ≤ baseTwoLeftLeg k ∧ baseTwoRightLeg k ≤ historicalHeadDimension 2 M := by
  simp only [baseTwo_leftLeg_eq, baseTwo_rightLeg_eq, baseTwo_headDimension]
  omega

/-- C2 has no shared endpoint: the first omitted LEFT leg is two places later. -/
theorem baseTwo_endpoint_incidence (M : ℕ) :
    baseTwoLeftLeg M = historicalHeadDimension 2 M + 2 ∧
      (∀ k, M ≤ k → historicalHeadDimension 2 M < baseTwoLeftLeg k) ∧
      (0 < M → baseTwoRightLeg (M - 1) = historicalHeadDimension 2 M) := by
  simp only [baseTwo_leftLeg_eq, baseTwo_rightLeg_eq, baseTwo_headDimension]
  refine ⟨by omega, ?_, ?_⟩
  · intro k hk; omega
  · intro hM; omega

private theorem weighted_coordinate (N n : ℕ) (c : ℝ) (f : ℕ → ℂ)
    (hn : 1 ≤ n) (hN : n ≤ N) :
    (∑ j : Fin N, ((if j.val + 1 = n then c else 0 : ℝ) : ℂ) * f (j.val + 1)) =
      (c : ℂ) * f n := by
  let i : Fin N := ⟨n - 1, by omega⟩
  have hi : i.val + 1 = n := by dsimp [i]; omega
  rw [Finset.sum_eq_single i]
  · simp only [hi, if_true]
  · intro j _ hji
    have hj : j.val + 1 ≠ n := by
      intro hj
      apply hji
      apply Fin.ext
      dsimp [i]
      omega
    simp [hj]
  · simp

private theorem baseTwo_historical_weight (M n : ℕ) :
    historicalCameraWeight 2 M n =
      (if n = 1 then 1 else 0) + ∑ k ∈ Finset.range M,
        ((if n = baseTwoLeftLeg k then 1 else 0) +
         (if n = baseTwoCenter k then -2 else 0) +
         (if n = baseTwoRightLeg k then 1 else 0)) := by
  simp only [historicalCameraWeight, historicalCameraPeriod, historicalCameraRadiiCount,
    if_true, Finset.sum_range_one, Nat.zero_add, baseTwo_leftLeg_eq,
    baseTwo_center_eq, baseTwo_rightLeg_eq, Nat.cast_one, mul_one]
  have hseed : (1 ≤ n ∧ n ≤ 1) ↔ n = 1 := by omega
  simp only [hseed]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  abel_nf

private theorem baseTwo_weighted_readout (M : ℕ) (f : ℕ → ℂ) :
    (∑ j : Fin (historicalHeadDimension 2 M),
      (historicalCameraWeights 2 M j : ℂ) * f (j.val+1)) =
      f 1 + ∑ k ∈ Finset.range M,
        (f (baseTwoLeftLeg k) - 2 * f (baseTwoCenter k) + f (baseTwoRightLeg k)) := by
  simp_rw [historicalCameraWeights, baseTwo_historical_weight]
  simp only [Complex.ofReal_add, Complex.ofReal_sum, add_mul, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_add_distrib]

  have hs := weighted_coordinate (historicalHeadDimension 2 M) 1 1 f (by omega) (by simp)
  simp only [Complex.ofReal_one, one_mul] at hs
  rw [hs]
  simp_rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hl := baseTwo_retained_cell_in_head (Finset.mem_range.mp hk)
  have hc : 1 ≤ baseTwoCenter k ∧ baseTwoCenter k ≤ historicalHeadDimension 2 M := by
    simp only [baseTwo_center_eq, baseTwo_headDimension]; have := Finset.mem_range.mp hk; omega
  have hr : 1 ≤ baseTwoRightLeg k := by simp
  simp only [Finset.sum_add_distrib]
  rw [weighted_coordinate _ _ 1 f hl.1 (by simp at hl ⊢; omega),
      weighted_coordinate _ _ (-2) f hc.1 hc.2,
      weighted_coordinate _ _ 1 f hr hl.2]
  push_cast
  ring

/-- Literal equality with the existing production head readout, including the seed. -/
theorem baseTwoFiniteHead_eq_historicalFiniteHeadReadout (M : ℕ) (t : ℝ) :
    baseTwoFiniteHead M t =
      finiteHeadReadout (historicalCameraWeights 2 M)
        (finiteMaterialOrbit (historicalHeadDimension 2 M) t
          (historicalInitialState (historicalHeadDimension 2 M))) := by
  simp only [finiteHeadReadout, LinearMap.coe_mk, AddHom.coe_mk,
    ← criticalMaterialSample_eq_finiteMaterialOrbit]
  exact (baseTwo_weighted_readout M (criticalMaterialSample t)).symm

/-- Existing iterated clock derivatives are the derivatives of this geometric head. -/
theorem baseTwoFiniteHead_iteratedDerivative (M r : ℕ) :
    iteratedDeriv r (baseTwoFiniteHead M) 0 =
      finiteHeadReadout (historicalCameraWeights 2 M)
        ((finiteClockStrongGenerator (historicalHeadDimension 2 M) ^ r)
          (historicalInitialState (historicalHeadDimension 2 M))) := by
  have he : baseTwoFiniteHead M = fun t =>
      finiteHeadReadout (historicalCameraWeights 2 M)
        (finiteMaterialOrbit (historicalHeadDimension 2 M) t
          (historicalInitialState (historicalHeadDimension 2 M))) :=
    funext (baseTwoFiniteHead_eq_historicalFiniteHeadReadout M)
  rw [he]
  exact finiteHeadReadout_iteratedDerivative _ _ r

theorem baseTwoFiniteHead_normalizedClockJet (M r : ℕ) :
    historicalFiniteHeadCoefficient (historicalCameraWeights 2 M) r =
      (r.factorial : ℂ)⁻¹ * iteratedDeriv r (baseTwoFiniteHead M) 0 := by
  rw [finiteClockJets_to_head, normalizedClockJet,
    map_smul, baseTwoFiniteHead_iteratedDerivative, smul_eq_mul]


def criticalMaterialExponent (t : ℝ) : ℂ := -1 / 2 - (t : ℂ) * Complex.I

private theorem criticalMaterialExponent_ne_zero (t : ℝ) : criticalMaterialExponent t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [criticalMaterialExponent] at this

private theorem criticalMaterialExponent_sub_one_ne_zero (t : ℝ) : criticalMaterialExponent t - 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [criticalMaterialExponent] at this

/-- Analytic representation of the existing sample; used only to estimate complete cells. -/
theorem criticalMaterialSample_eq_cpow (t : ℝ) {n : ℕ} (hn : 0 < n) :
    criticalMaterialSample t n = (n : ℂ) ^ criticalMaterialExponent t := by
  have hx : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : (Real.sqrt (n : ℝ))⁻¹ = Real.exp (Real.log (n : ℝ) * (-1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le, Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [criticalMaterialSample, ha, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn)),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log hx.le, ← Complex.exp_add]
  congr 1
  simp only [criticalMaterialExponent]
  push_cast
  ring

/-- The same existing material amplitude written with the standard real exponent. -/
theorem criticalMaterialSample_eq_rpow_phase (t : ℝ) {n : ℕ} (hn : 0 < n) :
    criticalMaterialSample t n = (((n : ℝ) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (-(((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  unfold criticalMaterialSample
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt (Nat.cast_pos.mpr hn))]
  norm_num

/-- Two applications of the mean-value bound preserve the full second difference. -/
private theorem secondDifference_norm_le (f f' f'' : ℝ → ℂ) (a C : ℝ)
    (hf : ∀ x ∈ Set.Icc a (a + 2), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a (a + 2), HasDerivAt f' (f'' x) x)
    (hb : ∀ x ∈ Set.Icc a (a + 2), ‖f'' x‖ ≤ C) :
    ‖f (a + 2) - 2 * f (a + 1) + f a‖ ≤ C := by
  have hi : ∀ x ∈ Set.Icc a (a + 1),
      ‖f' (x + 1) - f' x‖ ≤ C := by
    intro x hx
    have hx0 : x ∈ Set.Icc a (a + 2) := by constructor <;> linarith [hx.1, hx.2]
    have hx1 : x + 1 ∈ Set.Icc a (a + 2) := by constructor <;> linarith [hx.1, hx.2]
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hf' y hy).hasDerivWithinAt) hb (convex_Icc a (a+2)) hx0 hx1
    simpa using h
  have hg : ∀ x ∈ Set.Icc a (a + 1),
      HasDerivAt (fun y => f (y + 1) - f y) (f' (x + 1) - f' x) x := by
    intro x hx
    have hx0 : x ∈ Set.Icc a (a + 2) := by constructor <;> linarith [hx.1, hx.2]
    have hx1 : x + 1 ∈ Set.Icc a (a + 2) := by constructor <;> linarith [hx.1, hx.2]
    have hshift : HasDerivAt (fun y : ℝ => f (y+1)) (f' (x+1)) x := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hf (x+1) hx1).scomp x ((hasDerivAt_id x).add_const (1 : ℝ))
    exact hshift.sub (hf x hx0)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hg y hy).hasDerivWithinAt) hi (convex_Icc a (a+1))
    (by constructor <;> linarith : a ∈ Set.Icc a (a+1))
    (by constructor <;> linarith : a+1 ∈ Set.Icc a (a+1))
  have he : (f (a+1+1) - f (a+1)) - (f (a+1) - f a) =
      f (a+2) - 2 * f (a+1) + f a := by
    rw [show a+1+1 = a+2 by ring]
    ring
  simpa only [he, show a+1-a = (1 : ℝ) by ring, norm_one, mul_one] using h

/-- Absolute bound on the COMPLETE cell, not on its individual legs. -/
theorem baseTwoCriticalCenterCell_norm_le (t : ℝ) (k : ℕ) :
    ‖baseTwoCriticalCenterCell t k‖ ≤
      ‖criticalMaterialExponent t * (criticalMaterialExponent t - 1)‖ *
        ((k + 1 : ℕ) : ℝ) ^ (-5 / 2 : ℝ) := by
  let z := criticalMaterialExponent t
  let a : ℝ := (baseTwoLeftLeg k : ℕ)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (show 0 < baseTwoLeftLeg k by simp only [baseTwo_leftLeg_eq]; omega)
  have hfun : baseTwoCriticalCenterCell t k =
      ((a+2 : ℝ) : ℂ) ^ z - 2 * ((a+1 : ℝ) : ℂ) ^ z + (a : ℂ) ^ z := by
    have hc : baseTwoCenter k = baseTwoLeftLeg k + 1 := by simp; omega
    have hr : baseTwoRightLeg k = baseTwoLeftLeg k + 2 := by simp; omega
    rw [baseTwoCriticalCenterCell, hc, hr]
    rw [criticalMaterialSample_eq_cpow t (by simp only [baseTwo_leftLeg_eq]; omega),
      criticalMaterialSample_eq_cpow t (by simp only [baseTwo_leftLeg_eq]; omega),
      criticalMaterialSample_eq_cpow t (by simp only [baseTwo_leftLeg_eq]; omega)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, a, z, Complex.ofReal_natCast,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hbound : ∀ x ∈ Set.Icc a (a+2),
      ‖z * (z-1) * (x : ℂ) ^ (z-2)‖ ≤
        ‖z * (z-1)‖ * a ^ (-5/2 : ℝ) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have he : (z-2).re = (-5/2 : ℝ) := by dsimp [z, criticalMaterialExponent]; norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hx.1 (by norm_num)) (norm_nonneg _)
  have hb := secondDifference_norm_le
    (fun x => (x : ℂ)^z) (fun x => z * (x : ℂ)^(z-1))
    (fun x => z*(z-1)*(x : ℂ)^(z-2)) a (‖z*(z-1)‖ * a^(-5/2 : ℝ))
    (fun x hx => hasDerivAt_ofReal_cpow_const
      (ne_of_gt (lt_of_lt_of_le ha hx.1)) (criticalMaterialExponent_ne_zero t))
    (by
      intro x hx
      have h := (hasDerivAt_ofReal_cpow_const (r := z-1)
        (ne_of_gt (lt_of_lt_of_le ha hx.1)) (criticalMaterialExponent_sub_one_ne_zero t)).const_mul z
      simpa only [show z-1-1 = z-2 by ring, mul_assoc] using h)
    hbound
  rw [hfun]
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
  dsimp [a]
  rw [baseTwo_leftLeg_eq]
  have hnat : k+1 ≤ 4*(k+1)-1 := by omega
  exact_mod_cast hnat

/-- The cancelling cells are absolutely summable for every real time. -/
theorem summable_norm_baseTwoCriticalCenterCell (t : ℝ) :
    Summable (fun k => ‖baseTwoCriticalCenterCell t k‖) := by
  have hp : Summable (fun k : ℕ => ((k+1 : ℕ) : ℝ)^(-5/2 : ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num))
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) (baseTwoCriticalCenterCell_norm_le t)
    (hp.mul_left _)

theorem summable_baseTwoCriticalCenterCell (t : ℝ) :
    Summable (baseTwoCriticalCenterCell t) :=
  (summable_norm_baseTwoCriticalCenterCell t).of_norm

/-- Starts at the next WHOLE omitted cell, retaining both legs and its center. -/
def baseTwoCriticalCompleteTail (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, baseTwoCriticalCenterCell t (k + cutoff)

/-- Complete bracket signal, with the existing unit-material seed kept separate. -/
def baseTwoCriticalCompleteSignal (t : ℝ) : ℂ :=
  criticalMaterialSample t 1 + ∑' k : ℕ, baseTwoCriticalCenterCell t k

theorem baseTwoFiniteHead_add_completeTail (M : ℕ) (t : ℝ) :
    baseTwoFiniteHead M t + baseTwoCriticalCompleteTail M t =
      baseTwoCriticalCompleteSignal t := by
  unfold baseTwoFiniteHead baseTwoCriticalCompleteTail baseTwoCriticalCompleteSignal
  rw [add_assoc, (summable_baseTwoCriticalCenterCell t).sum_add_tsum_nat_add M]

theorem baseTwoCompletedSignal_cutoff_independent (M N : ℕ) (t : ℝ) :
    baseTwoFiniteHead M t + baseTwoCriticalCompleteTail M t =
      baseTwoFiniteHead N t + baseTwoCriticalCompleteTail N t := by
  rw [baseTwoFiniteHead_add_completeTail, baseTwoFiniteHead_add_completeTail]

@[simp] theorem criticalMaterialSample_one (t : ℝ) : criticalMaterialSample t 1 = 1 := by
  simp [criticalMaterialSample]

/-- The first omitted cell is the complete triple beyond the emitted horizon. -/
theorem baseTwo_firstOmittedCell_points (M : ℕ) :
    baseTwoLeftLeg M = 4*M+3 ∧ baseTwoCenter M = 4*M+4 ∧ baseTwoRightLeg M = 4*M+5 := by
  simp only [baseTwo_leftLeg_eq, baseTwo_center_eq, baseTwo_rightLeg_eq]
  omega

theorem baseTwoCriticalCompleteTail_hasSum (M : ℕ) (t : ℝ) :
    HasSum (fun k => baseTwoCriticalCenterCell t (k+M)) (baseTwoCriticalCompleteTail M t) :=
  ((summable_nat_add_iff M).2 (summable_baseTwoCriticalCenterCell t)).hasSum

/-- Also exposes the exact identity at the preexisting finite readout interface. -/
theorem baseTwoHistoricalReadout_add_completeTail (M : ℕ) (t : ℝ) :
    finiteHeadReadout (historicalCameraWeights 2 M)
        (finiteMaterialOrbit (historicalHeadDimension 2 M) t
          (historicalInitialState (historicalHeadDimension 2 M))) +
      baseTwoCriticalCompleteTail M t = baseTwoCriticalCompleteSignal t := by
  rw [← baseTwoFiniteHead_eq_historicalFiniteHeadReadout]
  exact baseTwoFiniteHead_add_completeTail M t

end GeometryOfNumbers.Analysis.BaseTwoCompletion
