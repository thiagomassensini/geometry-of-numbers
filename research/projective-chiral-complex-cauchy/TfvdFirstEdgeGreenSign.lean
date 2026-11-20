import TfvdMixedGreenExactTransport
import CPFormal.Analytic.CpGenuineFirstOrthogonalMultibaseGreen

/-!
# The first physical TFVD edge and the reflected Green sign

The seeded first vertex is read from the actual gradient trace.
Its amplitude ratio with the reflected vertex recovers the transverse
coefficient before the positive Green energy is multiplied in.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- The seed plus the first actual TFVD trace coordinate. -/
def tfvdSeededFirstVertex (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) : ℂ :=
  CPFormal.Genuine.Cp.seedSum 3 (dirichletTerm s) +
    (nativeGpreFiniteTfvdAnalysisTraceProjection S
    (c2DirichletGradientPrefixEnrichedAnalysis q S s 2)).1

theorem tfvdSeededFirstVertex_eq_dirichletValue
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    tfvdSeededFirstVertex q S s = positiveDirichletValue s 1 := by
  rw [tfvdSeededFirstVertex, seedSum_three_dirichlet_eq_one,
    tfvdNativeGradientActualBoundaryTrace_two]
  change 1 + positiveDirichletGradient s 0 = _
  rw [positiveDirichletGradient_eq_value_sub_value]
  have hseed : positiveDirichletValue s 0 = 1 := by
    simp [positiveDirichletValue]
  rw [hseed]
  ring

theorem norm_tfvdSeededFirstVertex_eq_rpow
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    ‖tfvdSeededFirstVertex q S s‖ = (2 : ℝ) ^ (-s.re) := by
  rw [tfvdSeededFirstVertex_eq_dirichletValue, norm_positiveDirichletValue]
  norm_num

/-- Product conservation comes from the original first reflected endpoint.
The two amplitudes retain their separate transverse factors. -/
theorem tfvdSeededFirstVertex_reflected_norm_mul_eq_half
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    ‖tfvdSeededFirstVertex q S s‖ *
        ‖tfvdSeededFirstVertex q S (reflectedParameter s)‖ = 1 / 2 := by
  rw [norm_tfvdSeededFirstVertex_eq_rpow, norm_tfvdSeededFirstVertex_eq_rpow,
    reflectedParameter_re, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show -s.re + -(1 - s.re) = (-1 : ℝ) by ring, Real.rpow_neg_one]
  norm_num

/-- At the first edge the imbalance has exactly the base-two Green
normalization, independent of the TFVD analysis ratio or atlas. -/
theorem tfvdFirstVertex_reflected_amplitude_sub_eq
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    ‖tfvdSeededFirstVertex q S (reflectedParameter s)‖ -
        ‖tfvdSeededFirstVertex q S s‖ =
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) * cpRadialDifference 2 (criticalDisplacement s.re) := by
  rw [norm_tfvdSeededFirstVertex_eq_rpow, norm_tfvdSeededFirstVertex_eq_rpow,
    reflectedParameter_re, cpRadialDifference, criticalDisplacement]
  push_cast
  rw [mul_sub, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1 <;> congr 1 <;> ring

/-- The signed Green bulk reconstructed at the same TFVD cut with the
base-two coefficient supplied by its first physical vertex. -/
theorem tfvdBaseTwoGreenBulk_eq_firstVertex_amplitude
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (s : ℂ) (M : ℕ) :
    (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        (finiteBracketCoupledCpGreenFlux 2 M s - finiteBracketCoupledSignedBoundary M s) =
      (‖tfvdSeededFirstVertex q S (reflectedParameter s)‖ -
          ‖tfvdSeededFirstVertex q S s‖) *
        (tfvdReconstructedReflectedGradientPairing q hqpos hq1 S s M).re := by
  rw [finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing 2 M (by decide) s,
    add_sub_cancel_right, tfvdFirstVertex_reflected_amplitude_sub_eq,
    tfvdReconstructedReflectedGradientPairing_eq]
  ring

/-- The sign of the Green bulk is the mass deficit from the critical
first-vertex mass. The second factor is the original mixed TFVD pairing. -/
theorem tfvdBaseTwoGreenBulk_eq_firstVertex_mass
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (s : ℂ) (M : ℕ) :
    ‖tfvdSeededFirstVertex q S s‖ * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
        (finiteBracketCoupledCpGreenFlux 2 M s - finiteBracketCoupledSignedBoundary M s) =
      ((1 / 2 : ℝ) - ‖tfvdSeededFirstVertex q S s‖ ^ 2) *
        (tfvdReconstructedReflectedGradientPairing q hqpos hq1 S s M).re := by
  rw [mul_assoc, tfvdBaseTwoGreenBulk_eq_firstVertex_amplitude q hqpos hq1 S s M]
  rw [← mul_assoc, mul_sub, tfvdSeededFirstVertex_reflected_norm_mul_eq_half, pow_two]

/-- The mass deficit and the bulk have precisely the same positive sign
at every nonempty cutoff in the Genuine strip. -/
theorem tfvdBaseTwoGreenBulk_pos_iff_firstVertex_mass_lt_half
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    {M : ℕ} (hM : 0 < M) :
    0 < finiteBracketCoupledCpGreenFlux 2 M s - finiteBracketCoupledSignedBoundary M s ↔
      ‖tfvdSeededFirstVertex q S s‖ ^ 2 < 1 / 2 := by
  have hv : 0 < ‖tfvdSeededFirstVertex q S s‖ := by
    rw [norm_tfvdSeededFirstVertex_eq_rpow]
    positivity
  have hm : 0 < ‖tfvdSeededFirstVertex q S s‖ * (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_pos hv (by positivity)
  have hE := tfvdReconstructedReflectedGradientPairing_re_pos q hqpos hq1 S hs hM
  rw [← mul_pos_iff_of_pos_left hm,
    tfvdBaseTwoGreenBulk_eq_firstVertex_mass q hqpos hq1 S s M,
    mul_pos_iff_of_pos_right hE, sub_pos]

/-- At a Genuine parameter the flux limit is read in the same first vertex
amplitude difference with the positive infinite reflected energy. -/
theorem tfvdBaseTwoScaledGreenFlux_tendsto_firstVertex_amplitude_of_genuine_zero
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) (hzero : genuineContinuation s = 0) :
    Tendsto (fun M : ℕ =>
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) * finiteBracketCoupledCpGreenFlux 2 M s)
      atTop (nhds ((‖tfvdSeededFirstVertex q S (reflectedParameter s)‖ -
        ‖tfvdSeededFirstVertex q S s‖) * infiniteReflectedGreenEnergy s)) := by
  rw [tfvdFirstVertex_reflected_amplitude_sub_eq, mul_assoc]
  exact tendsto_const_nhds.mul
    (finiteBracketCoupledCpGreenFlux_tendsto_infiniteBulk_of_genuine_zero 2 (by decide) hs hzero)

/-- The same first-vertex mass fixes the skew of the quadratic spectral
parameter. The logarithm has positive argument on the entire wave family. -/
theorem im_spectralQuadratic_eq_log_tfvdFirstVertex_mass
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    (s * (1 - s)).im =
      (s.im / Real.log 2) * Real.log (2 * ‖tfvdSeededFirstVertex q S s‖ ^ 2) := by
  have hlog : Real.log (2 * ‖tfvdSeededFirstVertex q S s‖ ^ 2) =
      (1 - 2 * s.re) * Real.log 2 := by
    rw [norm_tfvdSeededFirstVertex_eq_rpow, pow_two,
      Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num)]
    ring
  rw [hlog]
  simp only [Complex.mul_im, Complex.sub_im, Complex.sub_re, Complex.one_im, Complex.one_re]
  have h : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

/-- The first seeded C3 cell for a multiplicative wave has fourth
value `a^2`. Eliminating the third value across reflection gives a single
quadratic in the radial trace `a + 1/(2*a)`. -/
theorem reflectedMultiplicativeFirstCell_polynomial
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    let x := a + 1 / (2 * a)
    let ar := 1 / (2 * a)
    let C := 1 + a + a ^ 2 - 2 * b
    let Cr := 1 + ar + ar ^ 2 - 2 / (3 * b)
    x ^ 2 + (3 / 2 : ℂ) * x - 7 / 12 =
      (1 + ar + ar ^ 2) * C + (2 * b) * Cr := by
  dsimp only
  field_simp [ha, hb]
  ring

/-- The seed and full pointwise reflected conservation in the first cell
allow exact simultaneous bracket closure with unequal masses for sample
pairs. The infinite completion of this example is in the research note. -/
theorem seededFirstCell_conserved_product_counterexample :
    ∃ f g : Fin 4 → ℝ,
      f 0 = 1 ∧ g 0 = 1 ∧
      f 0 + f 1 - 2 * f 2 + f 3 = 0 ∧
      g 0 + g 1 - 2 * g 2 + g 3 = 0 ∧
      (∀ i : Fin 4, f i * g i = 1 / ((i.val : ℝ) + 1)) ∧
      f 1 ^ 2 ≠ 1 / 2 := by
  let f : Fin 4 → ℝ := ![1, 2 / 3, 2 / 3, -1 / 3]
  let g : Fin 4 → ℝ := ![1, 3 / 4, 1 / 2, -3 / 4]
  refine ⟨f, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [f]
  · norm_num [g]
  · change (1 : ℝ) + 2 / 3 - 2 * (2 / 3) + (-1 / 3) = 0
    norm_num
  · change (1 : ℝ) + 3 / 4 - 2 * (1 / 2) + (-3 / 4) = 0
    norm_num
  · intro i
    fin_cases i <;> norm_num [f, g]
  · norm_num [f]

end

end CPFormal.Analytic.Cp

#print axioms CPFormal.Analytic.Cp.tfvdSeededFirstVertex_eq_dirichletValue
#print axioms CPFormal.Analytic.Cp.norm_tfvdSeededFirstVertex_eq_rpow
#print axioms CPFormal.Analytic.Cp.tfvdSeededFirstVertex_reflected_norm_mul_eq_half
#print axioms CPFormal.Analytic.Cp.tfvdFirstVertex_reflected_amplitude_sub_eq
#print axioms CPFormal.Analytic.Cp.tfvdBaseTwoGreenBulk_eq_firstVertex_amplitude
#print axioms CPFormal.Analytic.Cp.tfvdBaseTwoGreenBulk_eq_firstVertex_mass
#print axioms CPFormal.Analytic.Cp.tfvdBaseTwoGreenBulk_pos_iff_firstVertex_mass_lt_half
#print axioms CPFormal.Analytic.Cp.tfvdBaseTwoScaledGreenFlux_tendsto_firstVertex_amplitude_of_genuine_zero
#print axioms CPFormal.Analytic.Cp.im_spectralQuadratic_eq_log_tfvdFirstVertex_mass
#print axioms CPFormal.Analytic.Cp.reflectedMultiplicativeFirstCell_polynomial
#print axioms CPFormal.Analytic.Cp.seededFirstCell_conserved_product_counterexample
