import CanonicalComparison
import CarrySelfAdjointOperator.CompletedNativeChiralPickHankel
import Mathlib.Tactic

/-!
# Radial C2 determinants at arbitrary finite order

Use the existing binomial congruence and all-order mixed Taylor limit.
The normalized determinant has a source limit without a positivity premise.
-/

namespace CarrySelfAdjointOperator

open Filter Topology CarryMaterialPhysicalRadialMultiplierGate
open scoped Matrix ComplexConjugate
noncomputable section
set_option autoImplicit false

theorem completedGreenComplexForwardDifferenceTransform_det (h : ℂ) (N : ℕ) :
    (completedGreenComplexForwardDifferenceTransform h N).det =
      ∏ i : Fin N, (((i.val.factorial : ℂ) * h ^ i.val)⁻¹) := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_congr rfl
    intro i _
    simp [completedGreenComplexForwardDifferenceTransform,
      completedGreenComplexForwardDifferenceCoefficient]
  · intro i j hij
    exact completedGreenComplexForwardDifferenceCoefficient_eq_zero_of_lt hij

/-- Exact positive normalization, expressed through the original
triangular stencil determinant. -/
def radialC2DeterminantScale (k N : ℕ) : ℝ :=
  (Complex.normSq (completedGreenComplexForwardDifferenceTransform
    (canonicalCompletedC3RadialSecondStep k) N).det)⁻¹

theorem radialC2DeterminantScale_pos (k N : ℕ) :
    0 < radialC2DeterminantScale k N := by
  unfold radialC2DeterminantScale
  apply inv_pos.mpr
  apply Complex.normSq_pos.mpr
  rw [completedGreenComplexForwardDifferenceTransform_det]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    inv_ne_zero (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i.val)
      (pow_ne_zero _ (canonicalCompletedC3RadialSecondStep_ne_zero k)))

private theorem radialDslope_eq_shiftedSample (k N : ℕ) :
    canonicalCompletedNativeRadialDslopeSampleMatrix k N =
      completedGreenComplexShiftedKernelSampleMatrix
        canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialSecondStep k) N := by
  ext i j
  simp only [canonicalCompletedNativeRadialDslopeSampleMatrix, Matrix.of_apply,
    completedGreenComplexShiftedKernelSampleMatrix,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  congr 1 <;> push_cast <;> simp [nsmul_eq_mul] <;> ring

/-- At any finite order the binomial congruence coincides entrywise with
the canonical analytic differences, so the whole matrix converges. -/
theorem radialDslopeConfluent_tendsto (N : ℕ) :
    Tendsto (fun k : ℕ => completedGreenComplexShiftedKernelForwardDifferenceMatrix
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k) N) atTop
      (nhds (Matrix.of fun i j : Fin N => polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment i j)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simp only [completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply, Matrix.of_apply]
  have hd : Tendsto (fun k : ℕ => (k, k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  simpa only [Function.comp_def] using
    (completedNativePolarizedDslope_shiftedRadial_tendsto i.val j.val).comp hd

theorem radialDslope_det_div_scale (k N : ℕ) :
    (canonicalCompletedNativeRadialDslopeSampleMatrix k N).det /
      (radialC2DeterminantScale k N : ℂ) =
      (completedGreenComplexShiftedKernelForwardDifferenceMatrix
        canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialSecondStep k) N).det := by
  rw [radialDslope_eq_shiftedSample, completedGreenComplexShiftedKernelForwardDifferenceMatrix,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [radialC2DeterminantScale, Complex.ofReal_inv, div_inv_eq_mul]
  rw [← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

/-- All-order normalized determinant limit on the original physical C2
radial Pick samples. No Hankel or Pick positivity hypothesis is used. -/
theorem physicalC2RadialPick_det_div_scale_tendsto (N : ℕ) :
    Tendsto (fun k : ℕ => (physicalC2RadialPickMatrix k N).det /
      (radialC2DeterminantScale k N : ℂ)) atTop
      (nhds ((Matrix.of fun i j : Fin N => polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment i j).det)) := by
  refine ((continuous_id.matrix_det.tendsto _).comp
    (radialDslopeConfluent_tendsto N)).congr' ?_
  filter_upwards [physicalC2RadialPickMatrix_eventually_eq_native_dslope N] with k hk
  simpa only [Function.comp_def, id_eq, hk] using (radialDslope_det_div_scale k N).symm

private def radialParityMap (N : ℕ) :
    Fin ((N + 1) / 2) ⊕ Fin (N / 2) → Fin N
  | .inl i => ⟨2 * i.val, by have := i.isLt; omega⟩
  | .inr j => ⟨2 * j.val + 1, by have := j.isLt; omega⟩

private def radialParityEquiv (N : ℕ) :
    Fin ((N + 1) / 2) ⊕ Fin (N / 2) ≃ Fin N :=
  Equiv.ofBijective (radialParityMap N) (by
    constructor
    · intro a b hab
      have hv := congrArg Fin.val hab
      rcases a with a | a <;> rcases b with b | b <;>
        simp only [radialParityMap] at hv
      · exact congrArg Sum.inl (Fin.ext (by omega))
      · omega
      · omega
      · exact congrArg Sum.inr (Fin.ext (by omega))
    · intro i
      have hi := i.isLt
      by_cases hp : i.val % 2 = 0
      · refine ⟨.inl ⟨i.val / 2, by omega⟩, Fin.ext ?_⟩
        change 2 * (i.val / 2) = i.val
        omega
      · refine ⟨.inr ⟨i.val / 2, by omega⟩, Fin.ext ?_⟩
        change 2 * (i.val / 2) + 1 = i.val
        omega)

theorem polarizedGreenMomentCoefficient_det_parity (h : ℕ → ℝ) (N : ℕ) :
    (Matrix.of fun i j : Fin N => polarizedGreenMomentCoefficient h i j).det =
      (((hankelGram h ((N + 1) / 2)).det *
        (shiftedHankel h (N / 2)).det : ℝ) : ℂ) := by
  let M := Matrix.of fun i j : Fin N => polarizedGreenMomentCoefficient h i j
  let E := Complex.ofRealHom.mapMatrix (hankelGram h ((N + 1) / 2))
  let O := Complex.ofRealHom.mapMatrix (shiftedHankel h (N / 2))
  let e := radialParityEquiv N
  have hReindex : M.submatrix e e = Matrix.fromBlocks E 0 0 O := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · change evenMomentDiagonalCoefficient h (2 * i.val + 2 * j.val) =
        (h (i.val + j.val) : ℂ)
      rw [evenMomentDiagonalCoefficient, if_pos (show Even (2 * i.val + 2 * j.val) from
        ⟨i.val + j.val, by omega⟩), show (2 * i.val + 2 * j.val) / 2 = i.val + j.val by omega]
    · change evenMomentDiagonalCoefficient h (2 * i.val + (2 * j.val + 1)) = 0
      rw [evenMomentDiagonalCoefficient, if_neg (by rintro ⟨a, ha⟩; omega)]
    · change evenMomentDiagonalCoefficient h (2 * i.val + 1 + 2 * j.val) = 0
      rw [evenMomentDiagonalCoefficient, if_neg (by rintro ⟨a, ha⟩; omega)]
    · change evenMomentDiagonalCoefficient h (2 * i.val + 1 + (2 * j.val + 1)) =
        (h (i.val + j.val + 1) : ℂ)
      rw [evenMomentDiagonalCoefficient, if_pos
        (show Even (2 * i.val + 1 + (2 * j.val + 1)) from
          ⟨i.val + j.val + 1, by omega⟩),
        show (2 * i.val + 1 + (2 * j.val + 1)) / 2 = i.val + j.val + 1 by omega]
  change M.det = _
  rw [← Matrix.det_submatrix_equiv_self e M, hReindex, Matrix.det_fromBlocks_zero₂₁]
  change E.det * O.det = Complex.ofRealHom _
  rw [← Complex.ofRealHom.map_det, ← Complex.ofRealHom.map_det, Complex.ofRealHom.map_mul]

/-- Physical radial determinant limit in the original two source Hankel
towers, including both parities and all finite section sizes. -/
theorem physicalC2RadialPick_det_div_scale_tendsto_hankel (N : ℕ) :
    Tendsto (fun k : ℕ => (physicalC2RadialPickMatrix k N).det /
      (radialC2DeterminantScale k N : ℂ)) atTop
      (nhds ((((hankelGram canonicalCompletedNativeLogDerivativeMoment ((N + 1) / 2)).det *
        (shiftedHankel canonicalCompletedNativeLogDerivativeMoment (N / 2)).det : ℝ) : ℂ))) := by
  simpa only [polarizedGreenMomentCoefficient_det_parity] using
    physicalC2RadialPick_det_div_scale_tendsto N

/-- Product of the original even and odd source determinants at total
radial section size `N`. The empty sector has determinant one. -/
def radialC2SourceDeterminant (N : ℕ) : ℝ :=
  (hankelGram canonicalCompletedNativeLogDerivativeMoment ((N + 1) / 2)).det *
    (shiftedHankel canonicalCompletedNativeLogDerivativeMoment (N / 2)).det

/-- The extra factor in the radial determinant scale is exactly the new
binomial-stencil diagonal, squared. -/
theorem radialC2DeterminantScale_succ (k N : ℕ) :
    radialC2DeterminantScale k (N + 1) =
      radialC2DeterminantScale k N *
        Complex.normSq ((N.factorial : ℂ) * canonicalCompletedC3RadialSecondStep k ^ N) := by
  unfold radialC2DeterminantScale
  rw [completedGreenComplexForwardDifferenceTransform_det,
    completedGreenComplexForwardDifferenceTransform_det, Fin.prod_univ_castSucc]
  simp [Complex.normSq_mul, mul_inv_rev, mul_comm]

/-- The ratio of consecutive physical determinants is the next scalar Schur
pivot whenever the preceding physical section is invertible. Its normalized
limit is the ratio of the unchanged source determinants. -/
theorem physicalC2RadialPick_pivot_div_scale_tendsto (N : ℕ)
    (hSource : radialC2SourceDeterminant N ≠ 0) :
    Tendsto (fun k : ℕ =>
      ((physicalC2RadialPickMatrix k (N + 1)).det /
        (physicalC2RadialPickMatrix k N).det) /
      (Complex.normSq ((N.factorial : ℂ) * canonicalCompletedC3RadialSecondStep k ^ N) : ℂ))
      atTop (nhds ((radialC2SourceDeterminant (N + 1) / radialC2SourceDeterminant N : ℝ) : ℂ)) := by
  have hLim : ∀ n, Tendsto (fun k : ℕ =>
      (physicalC2RadialPickMatrix k n).det / (radialC2DeterminantScale k n : ℂ))
      atTop (nhds (radialC2SourceDeterminant n : ℂ)) :=
    physicalC2RadialPick_det_div_scale_tendsto_hankel
  have hn : (radialC2SourceDeterminant N : ℂ) ≠ 0 := by exact_mod_cast hSource
  push_cast
  refine ((hLim (N + 1)).div (hLim N) hn).congr' ?_
  filter_upwards with k
  have hs : (radialC2DeterminantScale k N : ℂ) ≠ 0 := by
    exact_mod_cast (radialC2DeterminantScale_pos k N).ne'
  simp only [Pi.div_apply, radialC2DeterminantScale_succ, Complex.ofReal_mul]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    _ = ((radialC2DeterminantScale k N : ℂ) *
      (radialC2DeterminantScale k N : ℂ)⁻¹) *
      ((physicalC2RadialPickMatrix k (N + 1)).det *
        ((physicalC2RadialPickMatrix k N).det)⁻¹ *
        (Complex.normSq ((N.factorial : ℂ) *
          canonicalCompletedC3RadialSecondStep k ^ N) : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hs, one_mul]

/-- Any strictly positive source determinant gives the eventual positive
sign of the original physical determinant of that same section. -/
theorem physicalC2RadialPick_det_eventually_re_pos_of_source_pos (N : ℕ)
    (h : 0 < radialC2SourceDeterminant N) :
    ∀ᶠ k : ℕ in atTop, 0 < (physicalC2RadialPickMatrix k N).det.re := by
  have hlim := (Complex.continuous_re.continuousAt.tendsto.comp
    (physicalC2RadialPick_det_div_scale_tendsto_hankel N))
  have hp := tendsto_const_nhds.eventually_lt hlim
    (show (0 : ℝ) < (radialC2SourceDeterminant N : ℂ).re by simpa using h)
  filter_upwards [hp] with k hk
  have hdiv : 0 < (physicalC2RadialPickMatrix k N).det.re / radialC2DeterminantScale k N := by
    simpa only [Function.comp_def, Complex.div_ofReal_re] using hk
  exact (div_pos_iff_of_pos_right (radialC2DeterminantScale_pos k N)).mp hdiv

/-- A negative source determinant yields a negative physical determinant
eventually on the same grid. A vanishing source determinant gives no sign. -/
theorem physicalC2RadialPick_det_eventually_re_neg_of_source_neg (N : ℕ)
    (h : radialC2SourceDeterminant N < 0) :
    ∀ᶠ k : ℕ in atTop, (physicalC2RadialPickMatrix k N).det.re < 0 := by
  have hlim := (Complex.continuous_re.continuousAt.tendsto.comp
    (physicalC2RadialPick_det_div_scale_tendsto_hankel N))
  have hp := hlim.eventually_lt tendsto_const_nhds
    (show (radialC2SourceDeterminant N : ℂ).re < (0 : ℝ) by simpa using h)
  filter_upwards [hp] with k hk
  have hdiv : (physicalC2RadialPickMatrix k N).det.re / radialC2DeterminantScale k N < 0 := by
    simpa only [Function.comp_def, Complex.div_ofReal_re] using hk
  exact neg_of_div_neg_left hdiv (radialC2DeterminantScale_pos k N).le

#print axioms physicalC2RadialPick_det_eventually_re_pos_of_source_pos
#print axioms physicalC2RadialPick_det_eventually_re_neg_of_source_neg

#print axioms physicalC2RadialPick_pivot_div_scale_tendsto

#print axioms polarizedGreenMomentCoefficient_det_parity
#print axioms physicalC2RadialPick_det_div_scale_tendsto_hankel

#print axioms physicalC2RadialPick_det_div_scale_tendsto
#print axioms completedGreenComplexForwardDifferenceTransform_det

end
end CarrySelfAdjointOperator
