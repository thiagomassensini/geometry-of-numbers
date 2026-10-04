import GeometryOfNumbers.Analysis.CompletedBoundaryTransportedClock
import GeometryOfNumbers.Analysis.C2GlobalGreenBridge

/-! Necessary tests for geometric clock intertwiners. The obstructions concern
specified representations, not all enriched TFVD realizations. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProduct lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GeometryOfNumbers.Analysis C2GlobalGreenBridge

/-- The historical amplitude is material, not a depth amplitude. -/
theorem criticalMaterialSample_norm_sq (t : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖criticalMaterialSample t n‖ ^ 2 = (n : ℝ)⁻¹ := by
  have hnR : 0 ≤ (n : ℝ) := le_of_lt (Nat.cast_pos.mpr hn)
  have hp : ‖Complex.exp (-(((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, neg_zero, Real.exp_zero]
  rw [criticalMaterialSample, norm_mul, hp, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    inv_pow, Real.sq_sqrt hnR]

/-- Raw reconstructed critical samples do not belong to material ℓ². -/
theorem criticalMaterialSample_not_memℓp (t : ℝ) :
    ¬ Memℓp (fun j : ℕ => criticalMaterialSample t (j + 1)) 2 := by
  intro h
  have hs := h.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two,
    criticalMaterialSample_norm_sq t _ (Nat.succ_pos _)] at hs
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp hs)

/-- Two successive depths in the same physical core force a dyadic energy ratio. -/
theorem c2PhysicalSource_unitCore_left_energy_ratio (t : ℝ) (V : CoreState) :
    2 * Complex.normSq (c2GlobalGreenInputIsometry t V (7 : PNat)) =
      Complex.normSq (c2GlobalGreenInputIsometry t V (3 : PNat)) := by
  let m : PositiveOddCore := ⟨1, by decide, by decide⟩
  let i : GlobalC2BranchAddress := (m, (0, 0))
  let j : GlobalC2BranchAddress := (m, (0, 1))
  have h3 : globalC2OddMaterialAddress i = ⟨(3 : PNat), by decide, by decide⟩ := by
    apply Subtype.ext; apply PNat.eq; rfl
  have h7 : globalC2OddMaterialAddress j = ⟨(7 : PNat), by decide, by decide⟩ := by
    apply Subtype.ext; apply PNat.eq; rfl
  have henergy (a : GlobalC2BranchAddress) :
      Complex.normSq (c2GlobalGreenInputIsometry t V (globalC2MaterialAddress a)) =
        ((2 : ℝ) ^ (-(c2BranchDepth a.2 : ℝ) / 2)) ^ 2 *
          realPlaneEnergy (realPlaneHilbertEquiv.symm (V a.1)) := by
    change Complex.normSq (c2GlobalGreenInputIsometry t V (globalC2OddMaterialAddress a).val) = _
    rw [c2GlobalGreenInput_apply, realPlaneToComplexIsometry_normSq,
      LinearEquiv.symm_apply_apply, scaleRealPlane_energy, rotateRealPlane_energy,
      oddMaterialC2Address_encode]
  have hsq (k : ℝ) : ((2 : ℝ) ^ (-k / 2)) ^ 2 = (2 : ℝ) ^ (-k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hi := henergy i
  have hj := henergy j
  change Complex.normSq (c2GlobalGreenInputIsometry t V (3 : PNat)) = _ at hi
  change Complex.normSq (c2GlobalGreenInputIsometry t V (7 : PNat)) = _ at hj
  rw [hi, hj, hsq, hsq]
  norm_num [i, j, c2BranchDepth, Real.rpow_neg, Real.rpow_natCast]
  change 2 * (1 / 8 * realPlaneEnergy (realPlaneHilbertEquiv.symm (V m))) =
    1 / 4 * realPlaneEnergy (realPlaneHilbertEquiv.symm (V m))
  ring

/-- Already on odd material points 3 and 7, direct identification is impossible.
Both belong to core 1, left sign, depths 2 and 3 respectively. -/
theorem no_direct_c2PhysicalSource_match (t : ℝ) (V : CoreState) :
    ¬ (c2GlobalGreenInputIsometry t V (3 : PNat) = criticalMaterialSample t 3 ∧
       c2GlobalGreenInputIsometry t V (7 : PNat) = criticalMaterialSample t 7) := by
  rintro ⟨h3, h7⟩
  have h := c2PhysicalSource_unitCore_left_energy_ratio t V
  rw [h3, h7, ← Complex.sq_norm, ← Complex.sq_norm,
    criticalMaterialSample_norm_sq t 3 (by decide),
    criticalMaterialSample_norm_sq t 7 (by decide)] at h
  norm_num at h

/-- Keeping the standard product metric by an isometric embedding cannot turn
this clock into a symmetric clock. Domain preservation is explicit. -/
theorem completedClock_isometric_intertwiner_impossible
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (J : BaseTwoCompletedBoundaryHilbertCarrier →ₗᵢ[ℂ] K)
    (A : K →ₗ.[ℂ] K) (hA : A.IsFormalAdjoint A)
    (hdom : ∀ x : completedBoundaryTransportedClock.domain, J x.val ∈ A.domain) :
    ¬ (∀ x : completedBoundaryTransportedClock.domain,
      A ⟨J x.val, hdom x⟩ = J (completedBoundaryTransportedClock x)) := by
  intro hcomm
  apply completedBoundaryTransportedClock_not_standard_symmetric
  intro x y
  have h := hA ⟨J x.val, hdom x⟩ ⟨J y.val, hdom y⟩
  rw [hcomm x, hcomm y, J.inner_map_map, J.inner_map_map] at h
  exact h

end GeometryOfNumbers.Analysis.BaseTwoCompletion
