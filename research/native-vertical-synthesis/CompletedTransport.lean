import Quadratures

namespace CarryVerticalSynthesis
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- Native tower synthesis reproduces the ORIGINAL incident state, at every
finite order and radial index, before either pairing is taken. -/
theorem radial_incident_vector {N : ℕ} (k : ℕ) (c : Fin N → ℂ) :
    (Real.sqrt ((k : ℝ) + 1) : ℂ) • quadratureSynthesis (finiteQuadratures c) =
      ∑ j, c j • completedNativeRadialChiralCauchyState k j.val := by
  rw [quadrature_synthesis_finite, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp only [completedNativeRadialChiralCauchyState, smul_smul]
  rw [mul_comm]

/-- No return or completion term is replaced by a tower contraction. The
unchanged completed quotient acts on both finite coefficient quadratures. -/
theorem radial_return_vector {N : ℕ} (k : ℕ) (c : Fin N → ℂ) :
    (Real.sqrt ((k : ℝ) + 1) : ℂ) • quadratureSynthesis
      (finiteQuadratures (fun j => c j * completedNativeHermiteBiehlerChiralQuotient
        (canonicalCompletedC3RadialTiltPoint k j.val))) =
      ∑ j, c j • completedNativeRadialChiralMultiplierState k j.val := by
  rw [quadrature_synthesis_finite, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp only [completedNativeRadialChiralMultiplierState,
    completedNativeRadialChiralCauchyState, smul_smul]
  congr 1
  ring

/-- The exact completed polarized Green defect, with independent arguments and
all ordered crosses, transported through the new bounded forward synthesis. -/
theorem completed_native_tower_pairing {N : ℕ} (k : ℕ) (c d : Fin N → ℂ) :
    inner ℂ
      ((Real.sqrt ((k : ℝ) + 1) : ℂ) • quadratureSynthesis (finiteQuadratures c))
      ((Real.sqrt ((k : ℝ) + 1) : ℂ) • quadratureSynthesis (finiteQuadratures d)) -
    inner ℂ
      ((Real.sqrt ((k : ℝ) + 1) : ℂ) • quadratureSynthesis
        (finiteQuadratures (fun j => c j * completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k j.val))))
      ((Real.sqrt ((k : ℝ) + 1) : ℂ) • quadratureSynthesis
        (finiteQuadratures (fun j => d j * completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k j.val)))) =
      ∑ i, ∑ j, conj (c i) * d j *
        canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N i j := by
  rw [radial_incident_vector, radial_incident_vector, radial_return_vector,
    radial_return_vector]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [canonicalCompletedNativeRadialChiralMultiplierDefectMatrix,
    Matrix.sub_apply, Matrix.gram_apply]
  ring

/-- The forward map is not the isometry that would transport the vertical
prime-contraction estimate unchanged. This uses the literal center column. -/
theorem native_center_energy :
    ‖nativeSynthesis (lp.single 2 0 (1 : ℝ))‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [native_synthesis_column, norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_completedNativeChiralCauchyFeature]
  norm_num

theorem native_synthesis_not_isometry : ¬ Isometry nativeSynthesis := by
  intro h
  have hn := h.norm_map_of_map_zero (map_zero nativeSynthesis) (lp.single 2 0 (1 : ℝ))
  have he := native_center_energy
  rw [hn] at he
  norm_num [lp.norm_single] at he

/-- Native vertical norm contraction alone does not control synthesized energy:
the literal first and center columns have the same tower norm but different
Cauchy energies. This is a two-state test, not the actual chiral return. -/
theorem equal_vertical_norm_negative_synthesized_balance :
    ‖(lp.single 2 1 (1 : ℝ) : NativeGpreTowerHilbert)‖ =
      ‖(lp.single 2 0 (1 : ℝ) : NativeGpreTowerHilbert)‖ ∧
    ‖nativeSynthesis (lp.single 2 1 (1 : ℝ))‖ ^ 2 -
      ‖nativeSynthesis (lp.single 2 0 (1 : ℝ))‖ ^ 2 = -(1 / 4 : ℝ) := by
  constructor
  · simp [lp.norm_single]
  · rw [native_synthesis_column, native_synthesis_column,
      norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_completedNativeChiralCauchyFeature, inner_completedNativeChiralCauchyFeature]
    norm_num

end
end CarryVerticalSynthesis
