import GeometryOfNumbers.Analysis.BaseTwoSampledHardy
import Batteries.Tactic.OpenPrivate

/-! Uniform boundedness of the existing geometric center coupling.
The source and target retain their standard Hilbert norms. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open private log_step_bound from GeometryOfNumbers.Analysis.BaseTwoPhysicalCenterClockDefect

private theorem seed_reciprocal_step (m : ℝ) (hm : 3 ≤ m) :
    (m⁻¹)^2 ≤ m⁻¹ - (m+4)⁻¹ := by
  have hp : 0 < m := by linarith
  have hq : 0 < m+4 := by linarith
  have he : m⁻¹ - (m+4)⁻¹ = 4 / (m*(m+4)) := by field_simp; ring
  rw [he, inv_pow, ← one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hp) (mul_pos hp hq)).mpr
  nlinarith

/-- A uniform seed bound, obtained from the same geometric subsequence. -/
theorem baseTwoCenterCoupling_seed_finite (N : ℕ) :
    (∑ k ∈ Finset.range N, ((4*k+3 : ℝ)⁻¹)^2) ≤ 1 := by
  have h : (∑ k ∈ Finset.range N, ((4*k+3 : ℝ)⁻¹)^2) ≤
      (3 : ℝ)⁻¹ - (4*N+3 : ℝ)⁻¹ := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hs := seed_reciprocal_step (4*(N:ℝ)+3) (by have := Nat.cast_nonneg (α:=ℝ) N; linarith)
      push_cast
      rw [show 4*(N:ℝ)+3+4=4*((N:ℝ)+1)+3 by ring] at hs
      linarith
  have hp : 0 ≤ (4*N+3 : ℝ)⁻¹ := by positivity
  norm_num at h ⊢
  linarith

/-- The seed's infinite energy is finite with a certified bound 1. -/
theorem baseTwoCenterCoupling_seed_tsum :
    (∑' k : ℕ, ((4*k+3:ℝ)⁻¹)^2) ≤ 1 :=
  Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) baseTwoCenterCoupling_seed_finite

/-- Actual left/right gaps, uniformly controlled by the material prefix length. -/
theorem baseTwoCenterLogGap_bound (e : BaseTwoPhysicalEdge) :
    0 ≤ baseTwoCenterLogGap e ∧ baseTwoCenterLogGap e ≤ (4*e.1+3 : ℝ)⁻¹ := by
  rcases e with ⟨k,a⟩
  have hc : baseTwoCenter k = 4*k+4 := by simp [baseTwo_center_eq]; omega
  fin_cases a
  · change 0 ≤ Real.log (baseTwoCenter k : ℝ) - Real.log ((baseTwoCenter k-1:ℕ):ℝ) ∧
      Real.log (baseTwoCenter k:ℝ)-Real.log ((baseTwoCenter k-1:ℕ):ℝ) ≤ (4*k+3:ℝ)⁻¹
    have hm : baseTwoCenter k - 1 = 4*k+3 := by omega
    have he : baseTwoCenter k = (4*k+3)+1 := by omega
    rw [hm,he]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using log_step_bound (4*k+3) (by omega)
  · change 0 ≤ Real.log ((baseTwoCenter k+1:ℕ):ℝ) - Real.log (baseTwoCenter k:ℝ) ∧ _
    have hs := log_step_bound (baseTwoCenter k) (by omega)
    constructor
    · exact hs.1
    · have hi : (baseTwoCenter k:ℝ)⁻¹ ≤ (4*k+3:ℝ)⁻¹ :=
        (inv_le_inv₀ (by rw [hc]; positivity) (by positivity)).mpr (by rw [hc]; push_cast; linarith)
      exact hs.2.trans hi

private theorem raw_coordinate_bound (y : BaseTwoSeededMaterialHilbert) (k : ℕ) (a : Fin 2) :
    ‖baseTwoCenterCouplingRaw y (k,a)‖^2 ≤
      2 * ((4*k+3:ℝ)⁻¹)^2 *
        (‖y.fst‖^2 + ‖∑ j ∈ Finset.range (4*k+3), y.snd j‖^2) := by
  have hc : baseTwoCenter k - 1 = 4*k+3 := by simp [baseTwo_center_eq]; omega
  have hg := baseTwoCenterLogGap_bound (k,a)
  have hn : ‖baseTwoCenterCouplingRaw y (k,a)‖ ≤
      (4*k+3:ℝ)⁻¹ * (‖y.fst‖ + ‖∑ j ∈ Finset.range (4*k+3), y.snd j‖) := by
    change ‖(baseTwoCenterLogGap (k,a):ℂ) *
      (y.fst + ∑ j ∈ Finset.range (baseTwoCenter k-1), y.snd j)‖ ≤ _
    rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg.1]
    exact mul_le_mul hg.2 (norm_add_le _ _) (norm_nonneg _) (by positivity)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hab : (‖y.fst‖ + ‖∑ j ∈ Finset.range (4*k+3), y.snd j‖)^2 ≤
      2 * (‖y.fst‖^2 + ‖∑ j ∈ Finset.range (4*k+3), y.snd j‖^2) := by
    nlinarith [sq_nonneg (‖y.fst‖ - ‖∑ j ∈ Finset.range (4*k+3), y.snd j‖)]
  calc
    _ ≤ _ := hs
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hab (sq_nonneg ((4*k+3:ℝ)⁻¹))]

private theorem raw_cell_bound (y : BaseTwoSeededMaterialHilbert) (k : ℕ) :
    (∑ a : Fin 2, ‖baseTwoCenterCouplingRaw y (k,a)‖^2) ≤
      4 * ((4*k+3:ℝ)⁻¹)^2 * ‖y.fst‖^2 +
      4 * (‖∑ j ∈ Finset.range (4*k+3), y.snd j‖^2 / (4*k+3:ℝ)^2) := by
  have hl := raw_coordinate_bound y k 0
  have hr := raw_coordinate_bound y k 1
  simp only [Fin.sum_univ_succ, Finset.sum_singleton, Finset.univ_unique] at ⊢
  change ‖baseTwoCenterCouplingRaw y (k,0)‖^2 + ‖baseTwoCenterCouplingRaw y (k,1)‖^2 ≤ _
  simp only [div_eq_mul_inv, inv_pow] at hl hr ⊢
  nlinarith

/-- Uniform squared bound for all seeded inputs, not just the critical orbit. -/
theorem baseTwoCenterCouplingRaw_finite_bound (y : BaseTwoSeededMaterialHilbert) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ a : Fin 2, ‖baseTwoCenterCouplingRaw y (k,a)‖^2) ≤
      16 * ‖y‖^2 := by
  have hg : Summable (fun j => ‖y.snd j‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp y.snd).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)
  have hn : (∑ j ∈ Finset.range (4*N+3), ‖y.snd j‖^2) ≤ ‖y.snd‖^2 := by
    have ht := hg.sum_le_tsum (Finset.range (4*N+3)) (fun _ _ => sq_nonneg _)
    have he := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) y.snd
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at he
    rw [he]
    exact ht
  have hh := (baseTwoSampledHardy_finite (fun j => y.snd j) N).trans
    (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ) ≤ 4))
  have hs := mul_le_mul_of_nonneg_left (baseTwoCenterCoupling_seed_finite N)
    (show 0 ≤ 4*‖y.fst‖^2 by positivity)
  have hb := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range N) => raw_cell_bound y k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
  have hz : (∑ k ∈ Finset.range N, 4 * ((4*k+3:ℝ)⁻¹)^2 * ‖y.fst‖^2) =
      4 * ‖y.fst‖^2 * ∑ k ∈ Finset.range N, ((4*k+3:ℝ)⁻¹)^2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  rw [hz] at hb
  rw [WithLp.prod_norm_sq_eq_of_L2]
  nlinarith [sq_nonneg ‖y.fst‖]

/-- Arbitrary-input finite energy, with no orbit-specific amplitude bound. -/
theorem baseTwoCenterCouplingRaw_summable_sq (y : BaseTwoSeededMaterialHilbert) :
    Summable (fun e => ‖baseTwoCenterCouplingRaw y e‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simp only [tsum_fintype]
  exact summable_of_sum_range_le (fun k => Finset.sum_nonneg (fun a _ => sq_nonneg _))
    (baseTwoCenterCouplingRaw_finite_bound y)

theorem baseTwoCenterCouplingRaw_memℓp (y : BaseTwoSeededMaterialHilbert) :
    Memℓp (baseTwoCenterCouplingRaw y) 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using baseTwoCenterCouplingRaw_summable_sq y

/-- The same raw geometric coupling, now bundled in the physical Hilbert space. -/
def baseTwoCenterCouplingL2 : BaseTwoSeededMaterialHilbert →ₗ[ℂ] PhysicalEdgeL2 where
  toFun y := ⟨baseTwoCenterCouplingRaw y, baseTwoCenterCouplingRaw_memℓp y⟩
  map_add' x y := by apply lp.ext; exact baseTwoCenterCouplingRaw.map_add x y
  map_smul' a y := by apply lp.ext; exact baseTwoCenterCouplingRaw.map_smul a y

@[simp] theorem baseTwoCenterCouplingL2_apply (y : BaseTwoSeededMaterialHilbert)
    (e : BaseTwoPhysicalEdge) : baseTwoCenterCouplingL2 y e = baseTwoCenterCouplingRaw y e := rfl

/-- A certified constant 4; no optimal-constant claim is needed. -/
theorem baseTwoCenterCouplingL2_norm_le (y : BaseTwoSeededMaterialHilbert) :
    ‖baseTwoCenterCouplingL2 y‖ ≤ 4 * ‖y‖ := by
  have ht := (baseTwoCenterCouplingRaw_summable_sq y).tsum_prod
  simp only [tsum_fintype] at ht
  have hb := Real.tsum_le_of_sum_range_le
    (fun k => Finset.sum_nonneg (fun a _ => sq_nonneg (‖baseTwoCenterCouplingRaw y (k,a)‖)))
    (baseTwoCenterCouplingRaw_finite_bound y)
  have he := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    (baseTwoCenterCouplingL2 y)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, baseTwoCenterCouplingL2_apply] at he
  rw [← ht, ← he] at hb
  nlinarith [norm_nonneg (baseTwoCenterCouplingL2 y), norm_nonneg y]

/-- Bounded center coupling, with the original source and target metrics. -/
def baseTwoCenterCouplingOperator : BaseTwoSeededMaterialHilbert →L[ℂ] PhysicalEdgeL2 :=
  baseTwoCenterCouplingL2.mkContinuous 4 baseTwoCenterCouplingL2_norm_le

@[simp] theorem baseTwoCenterCouplingOperator_apply (y : BaseTwoSeededMaterialHilbert)
    (e : BaseTwoPhysicalEdge) : baseTwoCenterCouplingOperator y e = baseTwoCenterCouplingRaw y e := rfl

theorem baseTwoCenterCouplingOperator_norm_le (y : BaseTwoSeededMaterialHilbert) :
    ‖baseTwoCenterCouplingOperator y‖ ≤ 4 * ‖y‖ := baseTwoCenterCouplingL2_norm_le y

/-- The certified orbit defect is literally the image of the bounded coupling. -/
theorem baseTwoCenterCouplingOperator_concrete (t : ℝ) :
    baseTwoCenterCouplingOperator (baseTwoConcreteSeededGradientState t) =
      baseTwoPhysicalCenterClockDefectL2 t := by
  apply lp.ext
  exact baseTwoCenterCouplingRaw_concrete t

end GeometryOfNumbers.Analysis.BaseTwoCompletion
