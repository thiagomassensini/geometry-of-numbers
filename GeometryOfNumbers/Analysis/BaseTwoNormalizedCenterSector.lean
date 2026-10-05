import GeometryOfNumbers.Analysis.BaseTwoBoundedPhysicalCenterCoupling

/-! Center normalization is determined by the two existing geometric log gaps.
The center sector and physical sector keep their standard l2 metrics. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

abbrev BaseTwoCenterL2 := ℓ²(ℕ,ℂ)

def baseTwoCenterGapNorm (k : ℕ) : ℝ :=
  Real.sqrt ((baseTwoCenterLogGap (k,0))^2 + (baseTwoCenterLogGap (k,1))^2)

theorem baseTwoCenterLogGap_right_pos (k : ℕ) : 0 < baseTwoCenterLogGap (k,1) := by
  change 0 < Real.log ((baseTwoCenter k+1:ℕ):ℝ) - Real.log (baseTwoCenter k:ℝ)
  apply sub_pos.mpr
  apply Real.log_lt_log
  · simp only [baseTwo_center_eq]; positivity
  · exact_mod_cast Nat.lt_succ_self (baseTwoCenter k)

theorem baseTwoCenterGapNorm_pos (k : ℕ) : 0 < baseTwoCenterGapNorm k := by
  apply Real.sqrt_pos.mpr
  have h := sq_pos_of_pos (baseTwoCenterLogGap_right_pos k)
  nlinarith [sq_nonneg (baseTwoCenterLogGap (k,0))]

theorem baseTwoCenterGapNorm_sq (k : ℕ) :
    (baseTwoCenterGapNorm k)^2 =
      (baseTwoCenterLogGap (k,0))^2 + (baseTwoCenterLogGap (k,1))^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

def baseTwoCenterLegUnit (k : ℕ) (a : Fin 2) : ℝ :=
  baseTwoCenterLogGap (k,a) / baseTwoCenterGapNorm k

theorem baseTwoCenterLegUnit_sum_sq (k : ℕ) :
    (∑ a : Fin 2, (baseTwoCenterLegUnit k a)^2) = 1 := by
  simp only [Fin.sum_univ_succ, Finset.sum_singleton, Finset.univ_unique]
  change (baseTwoCenterLogGap (k,0) / baseTwoCenterGapNorm k)^2 +
    (baseTwoCenterLogGap (k,1) / baseTwoCenterGapNorm k)^2 = 1
  rw [div_pow,div_pow,← add_div,← baseTwoCenterGapNorm_sq]
  exact div_self (pow_ne_zero 2 (ne_of_gt (baseTwoCenterGapNorm_pos k)))

private theorem unit_row_energy (k : ℕ) (z : ℂ) :
    (∑ a : Fin 2, ‖(baseTwoCenterLegUnit k a : ℂ) * z‖^2) = ‖z‖^2 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.sum_mul,baseTwoCenterLegUnit_sum_sq,one_mul]

private def centerLegSynthesisLinear : BaseTwoCenterL2 →ₗ[ℂ] PhysicalEdgeL2 where
  toFun h := ⟨fun e => (baseTwoCenterLegUnit e.1 e.2 : ℂ) * h e.1, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simp only [tsum_fintype,unit_row_energy]
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp h).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)⟩
  map_add' x y := by apply lp.ext; funext e; simp [mul_add]
  map_smul' a x := by apply lp.ext; funext e; simp; ring

private theorem centerLegSynthesis_norm (h : BaseTwoCenterL2) :
    ‖centerLegSynthesisLinear h‖ = ‖h‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hs := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (centerLegSynthesisLinear h)
  have hh := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) h
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hs hh
  rw [hs,hh]
  have ht := ((lp.memℓp (centerLegSynthesisLinear h)).summable
    (by norm_num : 0 < (2:ℝ≥0∞).toReal)).tsum_prod
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,tsum_fintype] at ht
  rw [ht]
  congr 1
  funext k
  exact unit_row_energy k (h k)

/-- Isometric synthesis along the geometrically fixed real two-leg direction. -/
def baseTwoCenterLegSynthesis : BaseTwoCenterL2 →ₗᵢ[ℂ] PhysicalEdgeL2 :=
  { centerLegSynthesisLinear with norm_map' := centerLegSynthesis_norm }

@[simp] theorem baseTwoCenterLegSynthesis_apply (h : BaseTwoCenterL2) (k : ℕ) (a : Fin 2) :
    baseTwoCenterLegSynthesis h (k,a) = (baseTwoCenterLegUnit k a : ℂ) * h k := rfl

theorem baseTwoCenterLegSynthesis_norm (h : BaseTwoCenterL2) :
    ‖baseTwoCenterLegSynthesis h‖ = ‖h‖ := baseTwoCenterLegSynthesis.norm_map h

/-- Only gap-normalized center reconstruction is promoted to l2. -/
def baseTwoNormalizedCenterReconstructionRaw :
    BaseTwoSeededMaterialHilbert →ₗ[ℂ] (ℕ → ℂ) where
  toFun y k := (baseTwoCenterGapNorm k : ℂ) * baseTwoCenterReconstruction y k
  map_add' x y := by funext k; simp [map_add,mul_add]
  map_smul' a x := by funext k; simp [map_smul]; ring

theorem baseTwoCenterCoupling_normalized_coordinate (y : BaseTwoSeededMaterialHilbert)
    (k : ℕ) (a : Fin 2) : baseTwoCenterCouplingOperator y (k,a) =
      (baseTwoCenterLegUnit k a : ℂ) * baseTwoNormalizedCenterReconstructionRaw y k := by
  have he : (baseTwoCenterLegUnit k a : ℂ) * (baseTwoCenterGapNorm k : ℂ) =
      (baseTwoCenterLogGap (k,a) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    exact div_mul_cancel₀ _ (ne_of_gt (baseTwoCenterGapNorm_pos k))
  change (baseTwoCenterLogGap (k,a):ℂ) * baseTwoCenterReconstruction y k =
    (baseTwoCenterLegUnit k a:ℂ) * ((baseTwoCenterGapNorm k:ℂ) * baseTwoCenterReconstruction y k)
  rw [← mul_assoc,he]

private theorem normalized_center_row_energy (y : BaseTwoSeededMaterialHilbert) (k : ℕ) :
    (∑ a : Fin 2, ‖baseTwoCenterCouplingOperator y (k,a)‖^2) =
      ‖baseTwoNormalizedCenterReconstructionRaw y k‖^2 := by
  simp only [baseTwoCenterCoupling_normalized_coordinate,unit_row_energy]

theorem baseTwoNormalizedCenterReconstructionRaw_summable_sq (y : BaseTwoSeededMaterialHilbert) :
    Summable (fun k => ‖baseTwoNormalizedCenterReconstructionRaw y k‖^2) := by
  have hs := ((summable_prod_of_nonneg (fun e =>
    sq_nonneg (‖baseTwoCenterCouplingOperator y e‖))).mp
    (baseTwoCenterCouplingRaw_summable_sq y)).2
  simpa only [tsum_fintype,normalized_center_row_energy] using hs

theorem baseTwoNormalizedCenterReconstructionRaw_energy (y : BaseTwoSeededMaterialHilbert) :
    (∑' k, ‖baseTwoNormalizedCenterReconstructionRaw y k‖^2) =
      ∑' e, ‖baseTwoCenterCouplingOperator y e‖^2 := by
  have ht := (baseTwoCenterCouplingRaw_summable_sq y).tsum_prod
  simpa only [tsum_fintype,← baseTwoCenterCouplingOperator_apply,
    normalized_center_row_energy] using ht.symm

theorem baseTwoNormalizedCenterReconstructionRaw_memℓp (y : BaseTwoSeededMaterialHilbert) :
    Memℓp (baseTwoNormalizedCenterReconstructionRaw y) 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    baseTwoNormalizedCenterReconstructionRaw_summable_sq y

private def normalizedCenterLinear : BaseTwoSeededMaterialHilbert →ₗ[ℂ] BaseTwoCenterL2 where
  toFun y := ⟨baseTwoNormalizedCenterReconstructionRaw y, baseTwoNormalizedCenterReconstructionRaw_memℓp y⟩
  map_add' x y := by apply lp.ext; exact baseTwoNormalizedCenterReconstructionRaw.map_add x y
  map_smul' a y := by apply lp.ext; exact baseTwoNormalizedCenterReconstructionRaw.map_smul a y

private theorem normalizedCenter_norm (y : BaseTwoSeededMaterialHilbert) :
    ‖normalizedCenterLinear y‖ = ‖baseTwoCenterCouplingOperator y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have ht := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (normalizedCenterLinear y)
  have hk := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (baseTwoCenterCouplingOperator y)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at ht hk
  rw [ht,hk]
  exact baseTwoNormalizedCenterReconstructionRaw_energy y

/-- Boundedness follows from the existing coupling by exact equality of energies. -/
def baseTwoNormalizedCenterReconstruction :
    BaseTwoSeededMaterialHilbert →L[ℂ] BaseTwoCenterL2 :=
  normalizedCenterLinear.mkContinuous 4 (fun y => by
    rw [normalizedCenter_norm]; exact baseTwoCenterCouplingOperator_norm_le y)

@[simp] theorem baseTwoNormalizedCenterReconstruction_apply (y : BaseTwoSeededMaterialHilbert) (k : ℕ) :
    baseTwoNormalizedCenterReconstruction y k =
      (baseTwoCenterGapNorm k:ℂ) * baseTwoCenterReconstruction y k := rfl

theorem baseTwoNormalizedCenterReconstruction_norm (y : BaseTwoSeededMaterialHilbert) :
    ‖baseTwoNormalizedCenterReconstruction y‖ = ‖baseTwoCenterCouplingOperator y‖ :=
  normalizedCenter_norm y

theorem baseTwoNormalizedCenterReconstruction_norm_le (y : BaseTwoSeededMaterialHilbert) :
    ‖baseTwoNormalizedCenterReconstruction y‖ ≤ 4*‖y‖ :=
  (baseTwoNormalizedCenterReconstruction_norm y).trans_le (baseTwoCenterCouplingOperator_norm_le y)

/-- Exact factorization of the unchanged bounded geometric coupling. -/
theorem baseTwoCenterCoupling_factorization : baseTwoCenterCouplingOperator =
    baseTwoCenterLegSynthesis.toContinuousLinearMap.comp baseTwoNormalizedCenterReconstruction := by
  ext y e
  exact baseTwoCenterCoupling_normalized_coordinate y e.1 e.2

/-- The concrete orbit has a finite-energy normalized center state. -/
theorem baseTwoNormalizedCenterReconstruction_concrete (t : ℝ) (k : ℕ) :
    baseTwoNormalizedCenterReconstruction (baseTwoConcreteSeededGradientState t) k =
      (baseTwoCenterGapNorm k:ℂ) * criticalMaterialSample t (baseTwoCenter k) := by
  rw [baseTwoNormalizedCenterReconstruction_apply,baseTwoCenterReconstruction_concrete]

end GeometryOfNumbers.Analysis.BaseTwoCompletion
