import PolarizedGreen

/-! A source-specific obstruction to LOCAL pointwise Hilbert factorization
of the unmodified theta moment density. This is not a no-go for integration,
for a nonlocal transform, or for the complete Carry geometry. -/
namespace CarryThetaPolarized
open CarrySelfAdjointOperator Polynomial Filter MeasureTheory Set XiThetaCosine
noncomputable section
set_option autoImplicit false

local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0
local notation "c₁" => completedNativeRealEvenCharacteristicCoefficient 1
local notation "c₂" => completedNativeRealEvenCharacteristicCoefficient 2

theorem moment_zero_eval (u : ℝ) :
    (nativeThetaMomentPolynomial 0).eval u = u^2 / (2*c₀) := by
  rw [nativeThetaMomentPolynomial_eq]
  norm_num [nativeThetaMomentTopCoefficient, Polynomial.eval_smul,
    Polynomial.eval_sub, Polynomial.eval_monomial, smul_eq_mul]
  ring

theorem moment_one_eval (u : ℝ) :
    (nativeThetaMomentPolynomial 1).eval u =
      -u^4 / (12*c₀) - c₁*u^2 / (2*c₀^2) := by
  rw [nativeThetaMomentPolynomial_eq]
  norm_num [nativeThetaMomentTopCoefficient, Finset.sum_range_succ,
    Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_monomial,
    smul_eq_mul, moment_zero_eval]
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]

theorem moment_two_eval (u : ℝ) :
    (nativeThetaMomentPolynomial 2).eval u =
      u^6 / (240*c₀) + c₁*u^4 / (12*c₀^2) +
        (c₁^2/(2*c₀^3) - c₂/(2*c₀^2))*u^2 := by
  rw [nativeThetaMomentPolynomial_eq]
  norm_num [nativeThetaMomentTopCoefficient, Finset.sum_range_succ,
    Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_monomial, smul_eq_mul, moment_zero_eval, moment_one_eval]
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  ring

/-- Diagnostic determinant of the ORIGINAL density; no replacement source. -/
def thetaDensityDeterminant : ℝ[X] :=
  nativeThetaMomentPolynomial 0 * nativeThetaMomentPolynomial 2 -
    nativeThetaMomentPolynomial 1 ^ 2

theorem thetaDensityDeterminant_formula :
    thetaDensityDeterminant =
      Polynomial.monomial 8 (-7/(1440*c₀^2)) +
        Polynomial.monomial 6 (-c₁/(24*c₀^3)) +
          Polynomial.monomial 4 (-c₂/(4*c₀^3)) := by
  apply Polynomial.funext
  intro u
  simp only [thetaDensityDeterminant, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_monomial,
    moment_zero_eval, moment_one_eval, moment_two_eval]
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  ring

theorem thetaDensityDeterminant_coeff_eight :
    thetaDensityDeterminant.coeff 8 = -7/(1440*c₀^2) := by
  norm_num [thetaDensityDeterminant_formula, Polynomial.coeff_add,
    Polynomial.coeff_monomial]

theorem thetaDensityDeterminant_coeff_eight_neg :
    thetaDensityDeterminant.coeff 8 < 0 := by
  rw [thetaDensityDeterminant_coeff_eight]
  apply div_neg_of_neg_of_pos (by norm_num)
  exact mul_pos (by norm_num)
    (sq_pos_of_ne_zero completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero)

theorem thetaDensityDeterminant_natDegree :
    thetaDensityDeterminant.natDegree = 8 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    simp only [thetaDensityDeterminant_formula, Polynomial.coeff_add,
      Polynomial.coeff_monomial, if_neg (by omega : 8 ≠ d),
      if_neg (by omega : 6 ≠ d), if_neg (by omega : 4 ≠ d), add_zero]
  · exact thetaDensityDeterminant_coeff_eight_neg.ne

theorem thetaDensityDeterminant_tendsto_atBot :
    Tendsto (fun u : ℝ => thetaDensityDeterminant.eval u) atTop atBot := by
  apply Polynomial.tendsto_atBot_of_leadingCoeff_nonpos
  · rw [← Polynomial.natDegree_pos_iff_degree_pos, thetaDensityDeterminant_natDegree]
    norm_num
  · rw [← Polynomial.coeff_natDegree, thetaDensityDeterminant_natDegree]
    exact thetaDensityDeterminant_coeff_eight_neg.le

theorem thetaDensityDeterminant_eventually_neg :
    ∀ᶠ u : ℝ in atTop, thetaDensityDeterminant.eval u < 0 :=
  thetaDensityDeterminant_tendsto_atBot.eventually (eventually_lt_atBot 0)

/-- The failure occurs on a half-line, not on an exceptional null set. -/
theorem thetaDensityDeterminant_not_ae_nonneg :
    ¬(∀ᵐ u : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ thetaDensityDeterminant.eval u) := by
  intro h
  obtain ⟨a, ha⟩ := eventually_atTop.mp thetaDensityDeterminant_eventually_neg
  let b : ℝ := max a 0
  have hb : Ioi b ⊆ Ioi (0 : ℝ) := by
    intro u hu
    exact lt_of_le_of_lt (le_max_right a 0) hu
  have hpos := ae_restrict_of_ae_restrict_of_subset hb h
  have hneg : ∀ᵐ u : ℝ ∂volume.restrict (Ioi b),
      thetaDensityDeterminant.eval u < 0 := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    exact ha u (le_trans (le_max_left a 0) hu.le)
  have hf : ∀ᵐ u : ℝ ∂volume.restrict (Ioi b), False := by
    filter_upwards [hpos, hneg] with u hp hn
    exact (not_lt_of_ge hp) hn
  have hz : volume (Ioi b) = 0 := by
    simpa only [ae_iff, not_false_eq_true, Set.setOf_true,
      Measure.restrict_apply_univ] using hf
  simp only [Real.volume_Ioi, ENNReal.top_ne_zero] at hz

/-- Even the first two even-sector density vectors cannot have these three
pairings at every nonnegative theta coordinate. The cross term is essential. -/
theorem no_pointwise_theta_density_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v₀ v₁ : ℝ → E) :
    ¬(∀ u : ℝ, 0 ≤ u →
      inner ℝ (v₀ u) (v₀ u) = (nativeThetaMomentPolynomial 0).eval u ∧
      inner ℝ (v₀ u) (v₁ u) = (nativeThetaMomentPolynomial 1).eval u ∧
      inner ℝ (v₁ u) (v₁ u) = (nativeThetaMomentPolynomial 2).eval u) := by
  intro h
  obtain ⟨u, hu, hu0⟩ :=
    (thetaDensityDeterminant_eventually_neg.and (eventually_ge_atTop (0 : ℝ))).exists
  obtain ⟨h00, h01, h11⟩ := h u hu0
  have hcs := real_inner_mul_inner_self_le (v₀ u) (v₁ u)
  rw [h00, h01, h11] at hcs
  simp only [thetaDensityDeterminant, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow] at hu
  nlinarith

/-- Multiplying by the original strictly positive kernel does not repair the
cross obstruction. This also excludes local L2 density factors up to null sets. -/
theorem no_ae_weighted_theta_density_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v₀ v₁ : ℝ → E) :
    ¬(∀ᵐ u : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      inner ℝ (v₀ u) (v₀ u) =
          (nativeThetaMomentPolynomial 0).eval u * completedNativeXiCosineKernel u ∧
      inner ℝ (v₀ u) (v₁ u) =
          (nativeThetaMomentPolynomial 1).eval u * completedNativeXiCosineKernel u ∧
      inner ℝ (v₁ u) (v₁ u) =
          (nativeThetaMomentPolynomial 2).eval u * completedNativeXiCosineKernel u) := by
  intro h
  apply thetaDensityDeterminant_not_ae_nonneg
  filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with u hu hu0
  obtain ⟨h00, h01, h11⟩ := hu
  have hcs := real_inner_mul_inner_self_le (v₀ u) (v₁ u)
  rw [h00, h01, h11] at hcs
  have hphi := completedNativeXiCosineKernel_pos hu0.le
  have hm : 0 ≤ completedNativeXiCosineKernel u ^ 2 * thetaDensityDeterminant.eval u := by
    simp only [thetaDensityDeterminant, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow]
    nlinarith only [hcs]
  exact nonneg_of_mul_nonneg_right hm (sq_pos_of_pos hphi)

/-- The obstruction is truly in the crosses: both diagonal densities are
eventually positive, while their 2-by-2 determinant is negative. -/
theorem even_density_diagonals_pos_but_determinant_neg :
    ∀ᶠ u : ℝ in atTop,
      0 < (nativeThetaMomentPolynomial 0).eval u ∧
      0 < (nativeThetaMomentPolynomial 2).eval u ∧
      thetaDensityDeterminant.eval u < 0 := by
  have hc : 0 < c₀ := by
    rw [completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment]
    exact completedNativeXiCosineMoment_pos 0
  have htop : (nativeThetaMomentPolynomial 2).coeff 6 = c₀⁻¹ * (1/240 : ℝ) := by
    have h := nativeThetaMomentPolynomial_coeff_top 2
    norm_num [nativeThetaMomentTopCoefficient] at h
    exact h
  have hcoeff : 0 < (nativeThetaMomentPolynomial 2).coeff 6 := by
    rw [htop]
    positivity
  have hdeg : (nativeThetaMomentPolynomial 2).natDegree = 6 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro d hd
      exact nativeThetaMomentPolynomial_coeff_above 2 d (by omega)
    · exact hcoeff.ne'
  have hlim : Tendsto (fun u : ℝ => (nativeThetaMomentPolynomial 2).eval u) atTop atTop := by
    apply Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
    · rw [← Polynomial.natDegree_pos_iff_degree_pos, hdeg]
      norm_num
    · rw [← Polynomial.coeff_natDegree, hdeg]
      exact hcoeff.le
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hlim.eventually (eventually_gt_atTop (0 : ℝ)),
    thetaDensityDeterminant_eventually_neg] with u hu hp hd
  refine ⟨?_, hp, hd⟩
  rw [moment_zero_eval]
  exact div_pos (sq_pos_of_pos hu) (mul_pos (by norm_num) hc)

end
end CarryThetaPolarized
