import SigmaZeroPairDecomposition

/-!
# Quantitative bridge from the conditional remainder to moving windows

This file proves the exponential smallness of each fixed normalized remainder
entry. The subsequent determinant and root perturbation estimates are documented
with their exact limiting coefficients in `SIGMA-PADE-REPORT.md`.
-/

open Filter Topology
open scoped NNReal
noncomputable section
set_option autoImplicit false

namespace CarrySigmaPade

/-- One branch of the normalized quadratic roots, written using the real square root
when the discriminant is negative. -/
def sigmaPadeQuadraticRootLower (A B C : ℝ) : ℂ :=
  ((B / (2 * A) : ℝ) : ℂ) +
    Complex.I * (((Real.sqrt (4 * A * C - B ^ 2)) / (2 * A) : ℝ) : ℂ)

/-- The lower quadratic root depends continuously on normalized coefficients wherever
the leading coefficient has a nonzero limit. -/
theorem sigmaPadeQuadraticRootLower_tendsto
    (A B C : ℕ → ℝ) (A₀ B₀ C₀ : ℝ)
    (hA : Tendsto A atTop (𝓝 A₀)) (hB : Tendsto B atTop (𝓝 B₀))
    (hC : Tendsto C atTop (𝓝 C₀)) (hA₀ : A₀ ≠ 0) :
    Tendsto (fun s => sigmaPadeQuadraticRootLower (A s) (B s) (C s))
      atTop (𝓝 (sigmaPadeQuadraticRootLower A₀ B₀ C₀)) := by
  let T : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    sigmaPadeQuadraticRootLower p.1 p.2.1 p.2.2
  have hTcont : ContinuousAt T (A₀, (B₀, C₀)) := by
    have hden : 2 * A₀ ≠ 0 := mul_ne_zero (by norm_num) hA₀
    change ContinuousAt
      (fun p : ℝ × (ℝ × ℝ) =>
        ((p.2.1 / (2 * p.1) : ℝ) : ℂ) +
          Complex.I * ((Real.sqrt (4 * p.1 * p.2.2 - p.2.1 ^ 2) /
            (2 * p.1) : ℝ) : ℂ)) (A₀, (B₀, C₀))
    have hAcont : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => p.1)
        (A₀, (B₀, C₀)) := continuous_fst.continuousAt
    have hBcont : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => p.2.1)
        (A₀, (B₀, C₀)) := (continuous_fst.comp continuous_snd).continuousAt
    have hdencont : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => 2 * p.1)
        (A₀, (B₀, C₀)) := continuousAt_const.mul hAcont
    have hden' : (fun p : ℝ × (ℝ × ℝ) => 2 * p.1)
        (A₀, (B₀, C₀)) ≠ 0 := by simpa using hden
    have hrealpart : ContinuousAt (fun p : ℝ × (ℝ × ℝ) =>
        p.2.1 / (2 * p.1)) (A₀, (B₀, C₀)) := hBcont.div₀ hdencont hden'
    have hcomplexpart : ContinuousAt (fun p : ℝ × (ℝ × ℝ) =>
        ((p.2.1 / (2 * p.1) : ℝ) : ℂ)) (A₀, (B₀, C₀)) :=
      Complex.continuous_ofReal.continuousAt.comp hrealpart
    have hradicand : ContinuousAt
        (fun p : ℝ × (ℝ × ℝ) => 4 * p.1 * p.2.2 - p.2.1 ^ 2)
        (A₀, (B₀, C₀)) := by fun_prop
    have hsqrt : ContinuousAt
        (fun p : ℝ × (ℝ × ℝ) => Real.sqrt (4 * p.1 * p.2.2 - p.2.1 ^ 2))
        (A₀, (B₀, C₀)) := Real.continuous_sqrt.continuousAt.comp hradicand
    have himagpart : ContinuousAt (fun p : ℝ × (ℝ × ℝ) =>
        Real.sqrt (4 * p.1 * p.2.2 - p.2.1 ^ 2) / (2 * p.1))
        (A₀, (B₀, C₀)) := hsqrt.div₀ hdencont hden'
    have himagcomplex : ContinuousAt (fun p : ℝ × (ℝ × ℝ) =>
        ((Real.sqrt (4 * p.1 * p.2.2 - p.2.1 ^ 2) / (2 * p.1) : ℝ) : ℂ))
        (A₀, (B₀, C₀)) :=
      Complex.continuous_ofReal.continuousAt.comp himagpart
    exact hcomplexpart.add (continuousAt_const.mul himagcomplex)
  have hprod : Tendsto (fun s => (A s, (B s, C s))) atTop
      (𝓝 (A₀, (B₀, C₀))) := hA.prodMk_nhds (hB.prodMk_nhds hC)
  simpa [Function.comp_def, T, sigmaPadeQuadraticRootLower] using
    hTcont.tendsto.comp hprod

/-- When the real discriminant is negative, the displayed complex value is
indeed a root of the normalized characteristic quadratic. -/
theorem sigmaPadeQuadraticRootLower_is_root
    (A B C : ℝ) (hA : A ≠ 0) (hdisc : 0 ≤ 4 * A * C - B ^ 2) :
    (A : ℂ) * sigmaPadeQuadraticRootLower A B C ^ 2 -
      (B : ℂ) * sigmaPadeQuadraticRootLower A B C + (C : ℂ) = 0 := by
  have hsqrt : Real.sqrt (4 * A * C - B ^ 2) ^ 2 = 4 * A * C - B ^ 2 :=
    Real.sq_sqrt hdisc
  have hroot : sigmaPadeQuadraticRootLower A B C =
      ((B : ℂ) + Complex.I * (Real.sqrt (4 * A * C - B ^ 2) : ℂ)) /
        (2 * A : ℂ) := by
    unfold sigmaPadeQuadraticRootLower
    push_cast
    field_simp [hA]
  rw [hroot]
  field_simp [hA]
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    nlinarith [hsqrt]
  · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num [Complex.ofReal_im]
    all_goals ring

/-- The original signed-pencil coefficients normalized at the scale `a` of a
conjugate pole pair. -/
def sigmaPadeNormalizedD (d a : ℝ) (s : ℕ) : ℝ :=
  sigmaPadeD d s / a ^ (2 * s + 4)

def sigmaPadeNormalizedB (d a : ℝ) (s : ℕ) : ℝ :=
  sigmaPadeB d s / a ^ (2 * s + 5)

def sigmaPadeNormalizedC (d a : ℝ) (s : ℕ) : ℝ :=
  sigmaPadeC d s / a ^ (2 * s + 6)

/-- Conditional root convergence for the *original* sigma pencil: once its
three source-derived coefficients have the two-pole limits, the selected
quadratic branch converges. The hypotheses are exactly limits of normalized
`sigmaPadeD/B/C`, which are defined from `completedSigmaLogJet`. -/
theorem sigmaPadeOriginalNormalizedRoot_tendsto
    (d a A₀ B₀ C₀ : ℝ)
    (hA : Tendsto (fun s => sigmaPadeNormalizedD d a s) atTop (𝓝 A₀))
    (hB : Tendsto (fun s => sigmaPadeNormalizedB d a s) atTop (𝓝 B₀))
    (hC : Tendsto (fun s => sigmaPadeNormalizedC d a s) atTop (𝓝 C₀))
    (hA₀ : A₀ ≠ 0) :
    Tendsto (fun s => sigmaPadeQuadraticRootLower
      (sigmaPadeNormalizedD d a s) (sigmaPadeNormalizedB d a s)
      (sigmaPadeNormalizedC d a s)) atTop
      (𝓝 (sigmaPadeQuadraticRootLower A₀ B₀ C₀)) :=
  sigmaPadeQuadraticRootLower_tendsto _ _ _ _ _ _ hA hB hC hA₀

/-- Rescaling the normalized root by `a` gives the corresponding limiting
characteristic-root value. -/
theorem sigmaPadeOriginalRoot_tendsto
    (d a A₀ B₀ C₀ : ℝ)
    (hA : Tendsto (fun s => sigmaPadeNormalizedD d a s) atTop (𝓝 A₀))
    (hB : Tendsto (fun s => sigmaPadeNormalizedB d a s) atTop (𝓝 B₀))
    (hC : Tendsto (fun s => sigmaPadeNormalizedC d a s) atTop (𝓝 C₀))
    (hA₀ : A₀ ≠ 0) :
    Tendsto (fun s => (a : ℂ) * sigmaPadeQuadraticRootLower
      (sigmaPadeNormalizedD d a s) (sigmaPadeNormalizedB d a s)
      (sigmaPadeNormalizedC d a s)) atTop
      (𝓝 ((a : ℂ) * sigmaPadeQuadraticRootLower A₀ B₀ C₀)) := by
  simpa using (tendsto_const_nhds.mul
    (sigmaPadeOriginalNormalizedRoot_tendsto d a A₀ B₀ C₀ hA hB hC hA₀))

/-- A remainder bounded by `C * eta^n`, with `eta < a`, vanishes in any fixed
moving Hankel window after normalization by the model's geometric scale. -/
theorem sigmaPadeRemainder_window_normalized_tendsto
    (r : ℕ → ℝ) (C eta a : ℝ) (k : ℕ)
    (heta : 0 ≤ eta) (ha : 0 < a) (heta_a : eta < a)
    (hr : ∀ n, |r n| ≤ C * eta ^ n) :
    Tendsto (fun s : ℕ => r (s + k) / a ^ (s + 1)) atTop (𝓝 0) := by
  let q : ℝ := eta / a
  let K : ℝ := C * eta ^ k / a
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg heta ha.le
  have hq_lt : q < 1 := by
    dsimp [q]
    exact (div_lt_one ha).2 heta_a
  have hpow : Tendsto (fun s : ℕ => q ^ s) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt
  have hmajorant : Tendsto (fun s : ℕ => K * q ^ s) atTop (𝓝 0) := by
    simpa [mul_comm] using hpow.mul_const K
  have hmajorant_eq : (fun s : ℕ => C * eta ^ (s + k) / a ^ (s + 1)) =
      fun s => K * q ^ s := by
    funext s
    dsimp [K, q]
    rw [pow_add, pow_add]
    rw [div_pow]
    field_simp [ha.ne']
  have hmajorant' : Tendsto (fun s : ℕ => C * eta ^ (s + k) / a ^ (s + 1))
      atTop (𝓝 0) := hmajorant_eq ▸ hmajorant
  have hlower : Tendsto (fun s : ℕ => -(C * eta ^ (s + k) / a ^ (s + 1)))
      atTop (𝓝 0) := by simpa using hmajorant'.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun s => r (s + k) / a ^ (s + 1))
    (g := fun s => -(C * eta ^ (s + k) / a ^ (s + 1)))
    (h := fun s => C * eta ^ (s + k) / a ^ (s + 1)) hlower hmajorant' ?_ ?_
  · filter_upwards [] with s
    have hden : 0 < a ^ (s + 1) := pow_pos ha _
    have hscaled : |r (s + k)| / a ^ (s + 1) ≤
        C * eta ^ (s + k) / a ^ (s + 1) := by
      exact div_le_div_of_nonneg_right (hr (s + k)) (le_of_lt hden)
    have habs : |r (s + k) / a ^ (s + 1)| ≤
        C * eta ^ (s + k) / a ^ (s + 1) := by
      simpa [abs_div, abs_of_pos hden] using hscaled
    exact (abs_le.mp habs).1
  · filter_upwards [] with s
    have hden : 0 < a ^ (s + 1) := pow_pos ha _
    have hscaled : |r (s + k)| / a ^ (s + 1) ≤
        C * eta ^ (s + k) / a ^ (s + 1) := by
      exact div_le_div_of_nonneg_right (hr (s + k)) (le_of_lt hden)
    have habs : |r (s + k) / a ^ (s + 1)| ≤
        C * eta ^ (s + k) / a ^ (s + 1) := by
      simpa [abs_div, abs_of_pos hden] using hscaled
    exact (abs_le.mp habs).2

end CarrySigmaPade

end

#print axioms CarrySigmaPade.sigmaPadeRemainder_window_normalized_tendsto
#print axioms CarrySigmaPade.sigmaPadeQuadraticRootLower_tendsto
#print axioms CarrySigmaPade.sigmaPadeQuadraticRootLower_is_root
