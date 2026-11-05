import SigmaZeroPairDecomposition

/-!
# Quantitative bridge from the conditional remainder to moving windows

This file proves the exponential smallness of each fixed normalized remainder
entry. The subsequent determinant and root perturbation estimates are documented
with their exact limiting coefficients in `SIGMA-PADE-REPORT.md`.
-/

open Filter Topology
open CarrySigmaSource
open CarrySigmaObstruction
open scoped NNReal
noncomputable section
set_option autoImplicit false

namespace CarrySigmaPade

/-- One branch of the normalized quadratic roots, written using the real square root
when the discriminant is negative. -/
def sigmaPadeQuadraticRootLower (A B C : ℝ) : ℂ :=
  ((B / (2 * A) : ℝ) : ℂ) +
    Complex.I * (((Real.sqrt (4 * A * C - B ^ 2)) / (2 * A) : ℝ) : ℂ)

/-- On the unit circle, the selected negative-imaginary branch of the limiting
quadratic is the pole `a * theta` when `theta.im < 0`. -/
theorem sigmaPadeQuadraticRootLower_twoPole_limit
    (a x y : ℝ) (ha : 0 < a) (hy : y < 0)
    (hunit : x ^ 2 + y ^ 2 = 1) :
    sigmaPadeQuadraticRootLower (-1) (-(2 * a * x)) (-a ^ 2) =
      (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have hypos : 0 < -y := by linarith
  have hpos : 0 < -2 * a * y := by
    have hpos' : 0 < 2 * a * (-y) := mul_pos (mul_pos (by norm_num) ha) hypos
    nlinarith
  have hrad :
      4 * (-1 : ℝ) * (-a ^ 2) - (-(2 * a * x)) ^ 2 = (-2 * a * y) ^ 2 := by
    have hscaled := congrArg (fun t : ℝ => 4 * a ^ 2 * t) hunit
    nlinarith
  have hsqrt : Real.sqrt (4 * (-1 : ℝ) * (-a ^ 2) - (-(2 * a * x)) ^ 2) =
      -2 * a * y := by
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos hpos]
  unfold sigmaPadeQuadraticRootLower
  rw [hsqrt]
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring

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

/-- The lower characteristic-root branch of the original pencil converges
whenever its source-derived Padé coefficients converge. -/
theorem sigmaPadeAlphaBetaRoot_tendsto
    (d α₀ β₀ : ℝ)
    (hAlpha : Tendsto (fun s => sigmaPadeAlpha d s) atTop (𝓝 α₀))
    (hBeta : Tendsto (fun s => sigmaPadeBeta d s) atTop (𝓝 β₀)) :
    Tendsto (fun s => sigmaPadeQuadraticRootLower (-1)
      (-sigmaPadeAlpha d s) (-sigmaPadeBeta d s)) atTop
      (𝓝 (sigmaPadeQuadraticRootLower (-1) (-α₀) (-β₀))) := by
  apply sigmaPadeQuadraticRootLower_tendsto
  · exact tendsto_const_nhds
  · simpa using hAlpha.neg
  · simpa using hBeta.neg
  · norm_num

/-- If the source pencil has negative quadratic discriminant, the selected
branch is an actual non-real root of its exact complex characteristic. -/
theorem sigmaPadePencil_lowerRoot_is_root
    (d : ℝ) (s : ℕ)
    (hD : sigmaPadeD d s ≠ 0)
    (hdisc : (sigmaPadeAlpha d s) ^ 2 - 4 * sigmaPadeBeta d s < 0) :
    let α := sigmaPadeAlpha d s
    let β := sigmaPadeBeta d s
    let lam := sigmaPadeQuadraticRootLower (-1) (-α) (-β)
    sigmaPencilCharacteristicComplex d s lam = 0 ∧ lam.im ≠ 0 := by
  dsimp
  let α := sigmaPadeAlpha d s
  let β := sigmaPadeBeta d s
  let lam := sigmaPadeQuadraticRootLower (-1) (-α) (-β)
  have hrad : 0 < 4 * β - α ^ 2 := by dsimp [α, β]; linarith
  have hroot : (-1 : ℂ) * lam ^ 2 - (-α : ℂ) * lam + (-β : ℂ) = 0 := by
    simpa [lam] using sigmaPadeQuadraticRootLower_is_root (-1) (-α) (-β)
      (by norm_num) (by dsimp [α, β]; linarith)
  have hpoly : lam ^ 2 - (α : ℂ) * lam + (β : ℂ) = 0 := by
    linear_combination -hroot
  have hAlphaCast : (α : ℂ) = (sigmaPadeB d s : ℂ) /
      (sigmaPadeD d s : ℂ) := by
    simp [α, sigmaPadeAlpha]
  have hBetaCast : (β : ℂ) = (sigmaPadeC d s : ℂ) /
      (sigmaPadeD d s : ℂ) := by
    simp [β, sigmaPadeBeta]
  have hfactor : (sigmaPadeD d s : ℂ) *
      (lam ^ 2 - (α : ℂ) * lam + (β : ℂ)) =
      (sigmaPadeD d s : ℂ) * lam ^ 2 - (sigmaPadeB d s : ℂ) * lam +
        (sigmaPadeC d s : ℂ) := by
    rw [hAlphaCast, hBetaCast]
    field_simp [Complex.ofReal_ne_zero.mpr hD]
  have hchar : sigmaPencilCharacteristicComplex d s lam = 0 := by
    rw [sigmaPencilCharacteristicComplex_eq_quadratic d s lam]
    rw [← hfactor, hpoly]
    simp
  have hdiv : ((Real.sqrt (4 * β - α ^ 2) / (-2) : ℝ) : ℂ) =
      (Real.sqrt (4 * β - α ^ 2) : ℂ) / (-2 : ℂ) := by
    simp [Complex.ofReal_div]
  have hImFormula : lam.im = Real.sqrt (4 * β - α ^ 2) / (-2) := by
    simp [lam, sigmaPadeQuadraticRootLower, Complex.mul_im]
    rw [← hdiv]
    exact Complex.ofReal_re _
  have hIm : lam.im ≠ 0 := by
    rw [hImFormula]
    exact div_ne_zero (Real.sqrt_pos.2 hrad).ne' (by norm_num)
  exact ⟨hchar, hIm⟩

/-- The original signed-pencil coefficients normalized at the scale `a` of a
conjugate pole pair. -/
def sigmaPadeNormalizedD (d a : ℝ) (s : ℕ) : ℝ :=
  sigmaPadeD d s / a ^ (2 * s + 4)

def sigmaPadeNormalizedB (d a : ℝ) (s : ℕ) : ℝ :=
  sigmaPadeB d s / a ^ (2 * s + 5)

def sigmaPadeNormalizedC (d a : ℝ) (s : ℕ) : ℝ :=
  sigmaPadeC d s / a ^ (2 * s + 6)

/-- A source moment in a fixed window, normalized by the geometric scale of
its own index. -/
def sigmaPadeNormalizedMoment (d a : ℝ) (s k : ℕ) : ℝ :=
  completedSigmaLogJet d (s + k) / a ^ (s + k + 1)

/-- Scaling a conjugate-pair moment by `a` scales its `n`th coefficient by
`a^(n+1)`. -/
theorem twoPoleMoment_scale (m a : ℝ) (θ : ℂ) (n : ℕ) (ha : a ≠ 0) :
    twoPoleMoment m ((a : ℂ) * θ) n / a ^ (n + 1) =
      twoPoleMoment m θ n := by
  unfold twoPoleMoment
  have hpow : (((a : ℂ) * θ) ^ (n + 1)).re =
      a ^ (n + 1) * (θ ^ (n + 1)).re := by
    rw [mul_pow]
    have hreal : ((a : ℂ) ^ (n + 1)).re = a ^ (n + 1) := by norm_cast
    have hpowcast : (a : ℂ) ^ (n + 1) = (a ^ (n + 1) : ℝ) := by norm_cast
    have him : ((a : ℂ) ^ (n + 1)).im = 0 := by
      rw [hpowcast]
      exact Complex.ofReal_im _
    rw [Complex.mul_re, hreal, him]
    ring
  rw [hpow]
  field_simp [ha]

/-- A product perturbation tends to zero when both errors vanish and the
unperturbed factors stay bounded. -/
private theorem normalizedProduct_perturbation_tendsto_zero
    (p q e f : ℕ → ℝ) (M : ℝ)
    (hp : ∀ n, |p n| ≤ M) (hq : ∀ n, |q n| ≤ M)
    (he : Tendsto e atTop (𝓝 0)) (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n => (p n + e n) * (q n + f n) - p n * q n)
      atTop (𝓝 0) := by
  have hpBound : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖p n‖) :=
    Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => by
      simpa [Real.norm_eq_abs] using hp n)
  have hqBound : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖q n‖) :=
    Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => by
      simpa [Real.norm_eq_abs] using hq n)
  have heqBound : Tendsto (fun n => e n * q n) atTop (𝓝 0) := by
    simpa [smul_eq_mul] using he.zero_smul_isBoundedUnder_le hqBound
  have hfpBound : Tendsto (fun n => p n * f n) atTop (𝓝 0) := by
    simpa [smul_eq_mul, mul_comm] using hf.zero_smul_isBoundedUnder_le hpBound
  have hef : Tendsto (fun n => e n * f n) atTop (𝓝 0) := by
    simpa using he.mul hf
  have hsum : Tendsto (fun n => e n * q n + p n * f n + e n * f n)
      atTop (𝓝 (0 + 0 + 0)) := heqBound.add hfpBound |>.add hef
  have hidentity : (fun n => (p n + e n) * (q n + f n) - p n * q n) =
      fun n => e n * q n + p n * f n + e n * f n := by
    funext n
    ring
  have hsum0 : Tendsto (fun n => e n * q n + p n * f n + e n * f n)
      atTop (𝓝 0) := by simpa using hsum
  exact hidentity ▸ hsum0

/-- The three coefficient minors of a conjugate-pair model are determined by
its Gram determinant and its second-order recurrence. -/
theorem twoPoleMoment_minor_relations (m : ℝ) (θ : ℂ) (s : ℕ) :
    (twoPoleMoment m θ s * twoPoleMoment m θ (s + 2) -
      twoPoleMoment m θ (s + 1) ^ 2 =
        (twoPoleGram m θ s).det) ∧
    (twoPoleMoment m θ s * twoPoleMoment m θ (s + 3) -
      twoPoleMoment m θ (s + 1) * twoPoleMoment m θ (s + 2) =
        2 * θ.re * (twoPoleGram m θ s).det) ∧
    (twoPoleMoment m θ (s + 1) * twoPoleMoment m θ (s + 3) -
      twoPoleMoment m θ (s + 2) ^ 2 =
        Complex.normSq θ * (twoPoleGram m θ s).det) := by
  let p := twoPoleMoment m θ s
  let q := twoPoleMoment m θ (s + 1)
  let r := twoPoleMoment m θ (s + 2)
  let t := twoPoleMoment m θ (s + 3)
  have hr : r = 2 * θ.re * q - Complex.normSq θ * p := by
    simpa [p, q, r] using twoPoleMoment_recurrence m θ s
  have ht : t = 2 * θ.re * r - Complex.normSq θ * q := by
    simpa [q, r, t, Nat.add_assoc] using twoPoleMoment_recurrence m θ (s + 1)
  have hdet : (twoPoleGram m θ s).det = p * r - q ^ 2 := by
    simp [p, q, r, twoPoleGram, Matrix.det_fin_two]
    ring
  refine ⟨?_, ?_, ?_⟩
  · simpa [p, q, r] using hdet.symm
  · change p * t - q * r = 2 * θ.re * (twoPoleGram m θ s).det
    rw [hdet]
    rw [ht, hr]
    ring
  · change q * t - r ^ 2 = Complex.normSq θ * (twoPoleGram m θ s).det
    rw [hdet]
    rw [ht, hr]
    ring

/-- Unit-circle two-pole minors have the constant values used in the moving
window limits; their individual moments may continue to oscillate with `s`. -/
theorem twoPoleMoment_unitCircle_minors
    (m x y : ℝ) (θ : ℂ) (s : ℕ)
    (hre : θ.re = x) (him : θ.im = y)
    (hunit : Complex.normSq θ = 1) :
    (twoPoleMoment m θ s * twoPoleMoment m θ (s + 2) -
        twoPoleMoment m θ (s + 1) ^ 2 = -m ^ 2 * y ^ 2) ∧
      (twoPoleMoment m θ s * twoPoleMoment m θ (s + 3) -
        twoPoleMoment m θ (s + 1) * twoPoleMoment m θ (s + 2) =
          -2 * m ^ 2 * x * y ^ 2) ∧
      (twoPoleMoment m θ (s + 1) * twoPoleMoment m θ (s + 3) -
        twoPoleMoment m θ (s + 2) ^ 2 = -m ^ 2 * y ^ 2) := by
  obtain ⟨hDminor, hBminor, hCminor⟩ := twoPoleMoment_minor_relations m θ s
  have hGram : (twoPoleGram m θ s).det = -m ^ 2 * y ^ 2 := by
    rw [twoPoleGram_det, him, hunit]
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact hDminor.trans hGram
  · calc
      _ = 2 * θ.re * (twoPoleGram m θ s).det := hBminor
      _ = -2 * m ^ 2 * x * y ^ 2 := by rw [hre, hGram]; ring
  · calc
      _ = Complex.normSq θ * (twoPoleGram m θ s).det := hCminor
      _ = -m ^ 2 * y ^ 2 := by rw [hunit, hGram]; ring

/-- The original Padé coefficient is the scale `a` times the ratio of the
normalized mixed minor and normalized Gram determinant. -/
theorem sigmaPadeAlpha_eq_normalized_ratio (d a : ℝ) (s : ℕ) (ha : a ≠ 0) :
    sigmaPadeAlpha d s = a *
      (sigmaPadeNormalizedB d a s / sigmaPadeNormalizedD d a s) := by
  unfold sigmaPadeAlpha sigmaPadeNormalizedB sigmaPadeNormalizedD
  have hpow : a ^ (2 * s + 5) = a ^ (2 * s + 4) * a := by
    rw [show 2 * s + 5 = (2 * s + 4) + 1 by omega, pow_succ]
  rw [hpow]
  field_simp [ha]

/-- The second original Padé coefficient is the scale `a²` times the ratio
of the shifted determinant and normalized Gram determinant. -/
theorem sigmaPadeBeta_eq_normalized_ratio (d a : ℝ) (s : ℕ) (ha : a ≠ 0) :
    sigmaPadeBeta d s = a ^ 2 *
      (sigmaPadeNormalizedC d a s / sigmaPadeNormalizedD d a s) := by
  unfold sigmaPadeBeta sigmaPadeNormalizedC sigmaPadeNormalizedD
  have hpow : a ^ (2 * s + 6) = a ^ (2 * s + 4) * a ^ 2 := by
    rw [show 2 * s + 6 = (2 * s + 4) + 2 by omega, pow_add]
  rw [hpow]
  field_simp [ha]

/-- Conditional coefficient limits for the original Padé denominator, stated
directly in terms of normalized minors of `completedSigmaLogJet`. -/
theorem sigmaPadeAlpha_tendsto_of_normalized_minors
    (d a A₀ B₀ : ℝ)
    (hA : Tendsto (fun s => sigmaPadeNormalizedD d a s) atTop (𝓝 A₀))
    (hB : Tendsto (fun s => sigmaPadeNormalizedB d a s) atTop (𝓝 B₀))
    (hA₀ : A₀ ≠ 0) (ha : a ≠ 0) :
    Tendsto (fun s => sigmaPadeAlpha d s) atTop (𝓝 (a * (B₀ / A₀))) := by
  have hratio : Tendsto
      (fun s => sigmaPadeNormalizedB d a s / sigmaPadeNormalizedD d a s)
      atTop (𝓝 (B₀ / A₀)) := hB.div hA hA₀
  have hscaled : Tendsto
      (fun s => a * (sigmaPadeNormalizedB d a s / sigmaPadeNormalizedD d a s))
      atTop (𝓝 (a * (B₀ / A₀))) := tendsto_const_nhds.mul hratio
  have heq : (fun s => sigmaPadeAlpha d s) =
      (fun s => a * (sigmaPadeNormalizedB d a s / sigmaPadeNormalizedD d a s)) := by
    funext s
    exact sigmaPadeAlpha_eq_normalized_ratio d a s ha
  exact heq ▸ hscaled

theorem sigmaPadeBeta_tendsto_of_normalized_minors
    (d a A₀ C₀ : ℝ)
    (hA : Tendsto (fun s => sigmaPadeNormalizedD d a s) atTop (𝓝 A₀))
    (hC : Tendsto (fun s => sigmaPadeNormalizedC d a s) atTop (𝓝 C₀))
    (hA₀ : A₀ ≠ 0) (ha : a ≠ 0) :
    Tendsto (fun s => sigmaPadeBeta d s) atTop (𝓝 (a ^ 2 * (C₀ / A₀))) := by
  have hratio : Tendsto
      (fun s => sigmaPadeNormalizedC d a s / sigmaPadeNormalizedD d a s)
      atTop (𝓝 (C₀ / A₀)) := hC.div hA hA₀
  have hscaled : Tendsto
      (fun s => a ^ 2 * (sigmaPadeNormalizedC d a s / sigmaPadeNormalizedD d a s))
      atTop (𝓝 (a ^ 2 * (C₀ / A₀))) := tendsto_const_nhds.mul hratio
  have heq : (fun s => sigmaPadeBeta d s) =
      (fun s => a ^ 2 * (sigmaPadeNormalizedC d a s / sigmaPadeNormalizedD d a s)) := by
    funext s
    exact sigmaPadeBeta_eq_normalized_ratio d a s ha
  exact heq ▸ hscaled

/-- The exact two-pole limits for normalized minors imply the usual Padé
coefficient limits `alpha → 2 Re(zeta)` and `beta → |zeta|²`, writing
`zeta = a * (x + i y)` with `a > 0`. -/
theorem sigmaPadeAlphaBeta_tendsto_of_twoPole_minor_limits
    (d a m x y : ℝ)
    (hD : Tendsto (fun s => sigmaPadeNormalizedD d a s) atTop
      (𝓝 (-m ^ 2 * y ^ 2)))
    (hB : Tendsto (fun s => sigmaPadeNormalizedB d a s) atTop
      (𝓝 (-2 * m ^ 2 * x * y ^ 2)))
    (hC : Tendsto (fun s => sigmaPadeNormalizedC d a s) atTop
      (𝓝 (-m ^ 2 * y ^ 2)) )
    (ha : 0 < a) (hm : m ≠ 0) (hy : y ≠ 0) :
    Tendsto (fun s => sigmaPadeAlpha d s) atTop (𝓝 (2 * a * x)) ∧
      Tendsto (fun s => sigmaPadeBeta d s) atTop (𝓝 (a ^ 2)) := by
  have hA₀ : -m ^ 2 * y ^ 2 ≠ 0 := by
    simpa [neg_mul] using
      (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hm) (pow_ne_zero 2 hy)))
  have hAlpha := sigmaPadeAlpha_tendsto_of_normalized_minors d a
    (-m ^ 2 * y ^ 2) (-2 * m ^ 2 * x * y ^ 2) hD hB hA₀ ha.ne'
  have hBeta := sigmaPadeBeta_tendsto_of_normalized_minors d a
    (-m ^ 2 * y ^ 2) (-m ^ 2 * y ^ 2) hD hC hA₀ ha.ne'
  have hAlphaVal : a * ((-2 * m ^ 2 * x * y ^ 2) / (-m ^ 2 * y ^ 2)) =
      2 * a * x := by
    field_simp [hm, hy]
  have hBetaVal : a ^ 2 * ((-m ^ 2 * y ^ 2) / (-m ^ 2 * y ^ 2)) =
      a ^ 2 := by
    field_simp [hm, hy]
  rw [hAlphaVal] at hAlpha
  rw [hBetaVal] at hBeta
  exact ⟨hAlpha, hBeta⟩

/-- The normalized Padé discriminant inherits the limit of `alpha` and
`beta`. -/
theorem sigmaPadeDiscriminant_tendsto_of_alpha_beta
    (d α₀ β₀ : ℝ)
    (hAlpha : Tendsto (fun s => sigmaPadeAlpha d s) atTop (𝓝 α₀))
    (hBeta : Tendsto (fun s => sigmaPadeBeta d s) atTop (𝓝 β₀)) :
    Tendsto (fun s => (sigmaPadeAlpha d s) ^ 2 - 4 * sigmaPadeBeta d s)
      atTop (𝓝 (α₀ ^ 2 - 4 * β₀)) := by
  have hAlphaSq : Tendsto (fun s => (sigmaPadeAlpha d s) ^ 2)
      atTop (𝓝 (α₀ ^ 2)) := by simpa [pow_two] using hAlpha.mul hAlpha
  have hFourBeta : Tendsto (fun s => 4 * sigmaPadeBeta d s)
      atTop (𝓝 (4 * β₀)) := tendsto_const_nhds.mul hBeta
  simpa using hAlphaSq.sub hFourBeta

/-- A strictly negative limit of the normalized source Gram determinant makes
all sufficiently late original windows have negative determinant. -/
theorem sigmaPadeD_eventually_neg_of_normalized_limit
    (d a D₀ : ℝ)
    (hD : Tendsto (fun s => sigmaPadeNormalizedD d a s) atTop (𝓝 D₀))
    (ha : 0 < a) (hD₀ : D₀ < 0) :
    ∀ᶠ s : ℕ in atTop, sigmaPadeD d s < 0 := by
  have hnorm : ∀ᶠ s : ℕ in atTop, sigmaPadeNormalizedD d a s < 0 :=
    hD.eventually (Iio_mem_nhds hD₀)
  filter_upwards [hnorm] with s hs
  have hden : 0 < a ^ (2 * s + 4) := pow_pos ha _
  have hraw : sigmaPadeD d s / a ^ (2 * s + 4) < 0 := by
    simpa [sigmaPadeNormalizedD] using hs
  by_contra hnot
  have hnonneg : 0 ≤ sigmaPadeD d s := le_of_not_gt hnot
  have hquot : 0 ≤ sigmaPadeD d s / a ^ (2 * s + 4) :=
    div_nonneg hnonneg hden.le
  linarith

/-- Conditional eventual non-real roots for the original sigma pencil. The
hypotheses are the two-pole limits of the three normalized minors, so the
source sequence remains `completedSigmaLogJet`; no auxiliary moments are
substituted for it. -/
theorem sigmaPadeOriginalPencil_eventually_has_nonreal_root
    (d a m x y : ℝ)
    (hD : Tendsto (fun s => sigmaPadeNormalizedD d a s) atTop
      (𝓝 (-m ^ 2 * y ^ 2)))
    (hB : Tendsto (fun s => sigmaPadeNormalizedB d a s) atTop
      (𝓝 (-2 * m ^ 2 * x * y ^ 2)))
    (hC : Tendsto (fun s => sigmaPadeNormalizedC d a s) atTop
      (𝓝 (-m ^ 2 * y ^ 2)))
    (ha : 0 < a) (hm : m ≠ 0) (hy : y ≠ 0)
    (hunit : x ^ 2 + y ^ 2 = 1) :
    ∀ᶠ s : ℕ in atTop,
      sigmaPencilCharacteristicComplex d s
        (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d s)
          (-sigmaPadeBeta d s)) = 0 ∧
      (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d s)
        (-sigmaPadeBeta d s)).im ≠ 0 := by
  obtain ⟨hAlpha, hBeta⟩ := sigmaPadeAlphaBeta_tendsto_of_twoPole_minor_limits
    d a m x y hD hB hC ha hm hy
  have hdisc := sigmaPadeDiscriminant_tendsto_of_alpha_beta d
    (2 * a * x) (a ^ 2) hAlpha hBeta
  have hdiscLimit : (2 * a * x) ^ 2 - 4 * a ^ 2 < 0 := by
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha.ne'
    have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    nlinarith [ha2, hy2, hunit]
  have hdiscEventually : ∀ᶠ s : ℕ in atTop,
      sigmaPadeAlpha d s ^ 2 - 4 * sigmaPadeBeta d s < 0 :=
    hdisc.eventually (Iio_mem_nhds hdiscLimit)
  have hDneg := sigmaPadeD_eventually_neg_of_normalized_limit d a
    (-m ^ 2 * y ^ 2) hD ha (by
      have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
      have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      nlinarith)
  filter_upwards [hdiscEventually, hDneg] with s hsdisc hsD
  exact sigmaPadePencil_lowerRoot_is_root d s (ne_of_lt hsD) hsdisc

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

/-- The Cauchy coefficient bound also kills the remainder after the natural
`a^(s+k+1)` normalization of the `k`th shifted moment. -/
theorem sigmaPadeNormalizedRemainder_tendsto
    (d m a C eta : ℝ) (ζ : ℂ) (k : ℕ)
    (heta : 0 ≤ eta) (ha : 0 < a) (heta_a : eta < a)
    (hr : ∀ n, |sigmaZeroPairRemainderMoment d m ζ n| ≤ C * eta ^ n) :
    Tendsto (fun s : ℕ =>
      sigmaZeroPairRemainderMoment d m ζ (s + k) / a ^ (s + k + 1))
      atTop (𝓝 0) := by
  have hbase := sigmaPadeRemainder_window_normalized_tendsto
    (sigmaZeroPairRemainderMoment d m ζ) C eta a k heta ha heta_a hr
  have hscaled : Tendsto
      (fun s : ℕ => (a ^ k)⁻¹ *
        (sigmaZeroPairRemainderMoment d m ζ (s + k) / a ^ (s + 1)))
      atTop (𝓝 ((a ^ k)⁻¹ * 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (a ^ k)⁻¹) atTop
      (𝓝 ((a ^ k)⁻¹))).mul hbase
  have hpow (s : ℕ) : a ^ (s + k + 1) = a ^ (s + 1) * a ^ k := by
    rw [show s + k + 1 = (s + 1) + k by omega, pow_add]
  have heq : (fun s : ℕ =>
      sigmaZeroPairRemainderMoment d m ζ (s + k) / a ^ (s + k + 1)) =
      fun s => (a ^ k)⁻¹ *
        (sigmaZeroPairRemainderMoment d m ζ (s + k) / a ^ (s + 1)) := by
    funext s
    rw [hpow]
    field_simp [ha.ne']
  exact heq ▸ (by simpa using hscaled)

/-- Under the conditional coefficient decomposition from D, every fixed
normalized source moment differs from its unit-scale two-pole model by a term
that tends to zero. -/
theorem sigmaPadeNormalizedMoment_sub_twoPole_tendsto
    (d m a C eta : ℝ) (ζ θ : ℂ) (k : ℕ)
    (hζ : ζ = (a : ℂ) * θ)
    (heta : 0 ≤ eta) (ha : 0 < a) (heta_a : eta < a)
    (hr : ∀ n, |sigmaZeroPairRemainderMoment d m ζ n| ≤ C * eta ^ n) :
    Tendsto (fun s : ℕ => sigmaPadeNormalizedMoment d a s k -
      twoPoleMoment m θ (s + k)) atTop (𝓝 0) := by
  have herror := sigmaPadeNormalizedRemainder_tendsto d m a C eta ζ k
    heta ha heta_a hr
  have hdecomp (n : ℕ) : completedSigmaLogJet d n =
      twoPoleMoment m ζ n + sigmaZeroPairRemainderMoment d m ζ n := by
    simp [sigmaZeroPairRemainderMoment]
  have hmodel (s : ℕ) : twoPoleMoment m ζ (s + k) / a ^ (s + k + 1) =
      twoPoleMoment m θ (s + k) := by
    rw [hζ]
    exact twoPoleMoment_scale m a θ (s + k) ha.ne'
  have heq : (fun s : ℕ => sigmaPadeNormalizedMoment d a s k -
      twoPoleMoment m θ (s + k)) =
      fun s => sigmaZeroPairRemainderMoment d m ζ (s + k) /
        a ^ (s + k + 1) := by
    funext s
    unfold sigmaPadeNormalizedMoment
    rw [hdecomp (s + k), add_div, hmodel]
    ring
  exact heq ▸ herror

/-- Each normalized source minor is exactly the corresponding minor of its
four naturally normalized source moments. -/
theorem sigmaPadeNormalizedD_eq_normalizedMoments
    (d a : ℝ) (s : ℕ) (ha : a ≠ 0) :
    sigmaPadeNormalizedD d a s =
      sigmaPadeNormalizedMoment d a s 0 *
          sigmaPadeNormalizedMoment d a s 2 -
        sigmaPadeNormalizedMoment d a s 1 ^ 2 := by
  unfold sigmaPadeNormalizedD sigmaPadeD sigmaPadeNormalizedMoment
  have hpow02 : a ^ (2 * s + 4) = a ^ (s + 1) * a ^ (s + 3) := by
    calc
      a ^ (2 * s + 4) = a ^ ((s + 1) + (s + 3)) := by congr 1; omega
      _ = a ^ (s + 1) * a ^ (s + 3) := by rw [pow_add]
  have hpow11 : a ^ (2 * s + 4) = a ^ (s + 2) * a ^ (s + 2) := by
    calc
      a ^ (2 * s + 4) = a ^ ((s + 2) + (s + 2)) := by congr 1; omega
      _ = a ^ (s + 2) * a ^ (s + 2) := by rw [pow_add]
  rw [sub_div]
  have hterm02 : completedSigmaLogJet d s * completedSigmaLogJet d (s + 2) /
      a ^ (2 * s + 4) =
        (completedSigmaLogJet d s / a ^ (s + 1)) *
          (completedSigmaLogJet d (s + 2) / a ^ (s + 3)) := by
    rw [hpow02]
    field_simp [ha]
  have hterm11 : (completedSigmaLogJet d (s + 1)) ^ 2 /
      a ^ (2 * s + 4) =
        (completedSigmaLogJet d (s + 1) / a ^ (s + 2)) ^ 2 := by
    rw [hpow11]
    field_simp [ha]
  rw [hterm02, hterm11]
  simp only [Nat.add_zero]

theorem sigmaPadeNormalizedB_eq_normalizedMoments
    (d a : ℝ) (s : ℕ) (ha : a ≠ 0) :
    sigmaPadeNormalizedB d a s =
      sigmaPadeNormalizedMoment d a s 0 *
          sigmaPadeNormalizedMoment d a s 3 -
        sigmaPadeNormalizedMoment d a s 1 *
          sigmaPadeNormalizedMoment d a s 2 := by
  unfold sigmaPadeNormalizedB sigmaPadeB sigmaPadeNormalizedMoment
  have hpow03 : a ^ (2 * s + 5) = a ^ (s + 1) * a ^ (s + 4) := by
    calc
      a ^ (2 * s + 5) = a ^ ((s + 1) + (s + 4)) := by congr 1; omega
      _ = a ^ (s + 1) * a ^ (s + 4) := by rw [pow_add]
  have hpow12 : a ^ (2 * s + 5) = a ^ (s + 2) * a ^ (s + 3) := by
    calc
      a ^ (2 * s + 5) = a ^ ((s + 2) + (s + 3)) := by congr 1; omega
      _ = a ^ (s + 2) * a ^ (s + 3) := by rw [pow_add]
  rw [sub_div]
  have hterm03 : completedSigmaLogJet d s * completedSigmaLogJet d (s + 3) /
      a ^ (2 * s + 5) =
        (completedSigmaLogJet d s / a ^ (s + 1)) *
          (completedSigmaLogJet d (s + 3) / a ^ (s + 4)) := by
    rw [hpow03]
    field_simp [ha]
  have hterm12 : completedSigmaLogJet d (s + 1) *
      completedSigmaLogJet d (s + 2) / a ^ (2 * s + 5) =
        (completedSigmaLogJet d (s + 1) / a ^ (s + 2)) *
          (completedSigmaLogJet d (s + 2) / a ^ (s + 3)) := by
    rw [hpow12]
    field_simp [ha]
  rw [hterm03, hterm12]
  simp only [Nat.add_zero]

theorem sigmaPadeNormalizedC_eq_normalizedMoments
    (d a : ℝ) (s : ℕ) (ha : a ≠ 0) :
    sigmaPadeNormalizedC d a s =
      sigmaPadeNormalizedMoment d a s 1 *
          sigmaPadeNormalizedMoment d a s 3 -
        sigmaPadeNormalizedMoment d a s 2 ^ 2 := by
  unfold sigmaPadeNormalizedC sigmaPadeC sigmaPadeNormalizedMoment
  have hpow13 : a ^ (2 * s + 6) = a ^ (s + 2) * a ^ (s + 4) := by
    calc
      a ^ (2 * s + 6) = a ^ ((s + 2) + (s + 4)) := by congr 1; omega
      _ = a ^ (s + 2) * a ^ (s + 4) := by rw [pow_add]
  have hpow22 : a ^ (2 * s + 6) = a ^ (s + 3) * a ^ (s + 3) := by
    calc
      a ^ (2 * s + 6) = a ^ ((s + 3) + (s + 3)) := by congr 1; omega
      _ = a ^ (s + 3) * a ^ (s + 3) := by rw [pow_add]
  rw [sub_div]
  have hterm13 : completedSigmaLogJet d (s + 1) *
      completedSigmaLogJet d (s + 3) / a ^ (2 * s + 6) =
        (completedSigmaLogJet d (s + 1) / a ^ (s + 2)) *
          (completedSigmaLogJet d (s + 3) / a ^ (s + 4)) := by
    rw [hpow13]
    field_simp [ha]
  have hterm22 : (completedSigmaLogJet d (s + 2)) ^ 2 /
      a ^ (2 * s + 6) =
        (completedSigmaLogJet d (s + 2) / a ^ (s + 3)) ^ 2 := by
    rw [hpow22]
    field_simp [ha]
  rw [hterm13, hterm22]

/-- A controlled remainder around a unit-circle two-pole model implies all
three normalized source-minor limits. This is the coefficient-to-minor step
needed after the conditional continuation theorem D. -/
theorem sigmaPadeNormalizedMinors_tendsto_of_twoPole_remainder
    (d m a C eta M x y : ℝ) (ζ θ : ℂ)
    (hζ : ζ = (a : ℂ) * θ)
    (hre : θ.re = x) (him : θ.im = y)
    (hunit : Complex.normSq θ = 1)
    (heta : 0 ≤ eta) (ha : 0 < a) (heta_a : eta < a)
    (hmodelBound : ∀ n, |twoPoleMoment m θ n| ≤ M)
    (hr : ∀ n, |sigmaZeroPairRemainderMoment d m ζ n| ≤ C * eta ^ n) :
    Tendsto (fun s => sigmaPadeNormalizedD d a s) atTop
        (𝓝 (-m ^ 2 * y ^ 2)) ∧
      Tendsto (fun s => sigmaPadeNormalizedB d a s) atTop
        (𝓝 (-2 * m ^ 2 * x * y ^ 2)) ∧
      Tendsto (fun s => sigmaPadeNormalizedC d a s) atTop
        (𝓝 (-m ^ 2 * y ^ 2)) := by
  let p₀ : ℕ → ℝ := fun s => twoPoleMoment m θ s
  let p₁ : ℕ → ℝ := fun s => twoPoleMoment m θ (s + 1)
  let p₂ : ℕ → ℝ := fun s => twoPoleMoment m θ (s + 2)
  let p₃ : ℕ → ℝ := fun s => twoPoleMoment m θ (s + 3)
  let e₀ : ℕ → ℝ := fun s => sigmaPadeNormalizedMoment d a s 0 - p₀ s
  let e₁ : ℕ → ℝ := fun s => sigmaPadeNormalizedMoment d a s 1 - p₁ s
  let e₂ : ℕ → ℝ := fun s => sigmaPadeNormalizedMoment d a s 2 - p₂ s
  let e₃ : ℕ → ℝ := fun s => sigmaPadeNormalizedMoment d a s 3 - p₃ s
  have he₀ : Tendsto e₀ atTop (𝓝 0) := by
    simpa [e₀, p₀] using sigmaPadeNormalizedMoment_sub_twoPole_tendsto
      d m a C eta ζ θ 0 hζ heta ha heta_a hr
  have he₁ : Tendsto e₁ atTop (𝓝 0) := by
    simpa [e₁, p₁] using sigmaPadeNormalizedMoment_sub_twoPole_tendsto
      d m a C eta ζ θ 1 hζ heta ha heta_a hr
  have he₂ : Tendsto e₂ atTop (𝓝 0) := by
    simpa [e₂, p₂] using sigmaPadeNormalizedMoment_sub_twoPole_tendsto
      d m a C eta ζ θ 2 hζ heta ha heta_a hr
  have he₃ : Tendsto e₃ atTop (𝓝 0) := by
    simpa [e₃, p₃] using sigmaPadeNormalizedMoment_sub_twoPole_tendsto
      d m a C eta ζ θ 3 hζ heta ha heta_a hr
  have hp₀ : ∀ s, |p₀ s| ≤ M := by intro s; simpa [p₀] using hmodelBound s
  have hp₁ : ∀ s, |p₁ s| ≤ M := by intro s; simpa [p₁] using hmodelBound (s + 1)
  have hp₂ : ∀ s, |p₂ s| ≤ M := by intro s; simpa [p₂] using hmodelBound (s + 2)
  have hp₃ : ∀ s, |p₃ s| ≤ M := by intro s; simpa [p₃] using hmodelBound (s + 3)
  have hE₀₂ := normalizedProduct_perturbation_tendsto_zero p₀ p₂ e₀ e₂ M
    hp₀ hp₂ he₀ he₂
  have hE₁₁ := normalizedProduct_perturbation_tendsto_zero p₁ p₁ e₁ e₁ M
    hp₁ hp₁ he₁ he₁
  have hE₀₃ := normalizedProduct_perturbation_tendsto_zero p₀ p₃ e₀ e₃ M
    hp₀ hp₃ he₀ he₃
  have hE₁₂ := normalizedProduct_perturbation_tendsto_zero p₁ p₂ e₁ e₂ M
    hp₁ hp₂ he₁ he₂
  have hE₁₃ := normalizedProduct_perturbation_tendsto_zero p₁ p₃ e₁ e₃ M
    hp₁ hp₃ he₁ he₃
  have hE₂₂ := normalizedProduct_perturbation_tendsto_zero p₂ p₂ e₂ e₂ M
    hp₂ hp₂ he₂ he₂
  have hv₀ (s : ℕ) : sigmaPadeNormalizedMoment d a s 0 = p₀ s + e₀ s := by
    dsimp [e₀]
    ring
  have hv₁ (s : ℕ) : sigmaPadeNormalizedMoment d a s 1 = p₁ s + e₁ s := by
    dsimp [e₁]
    ring
  have hv₂ (s : ℕ) : sigmaPadeNormalizedMoment d a s 2 = p₂ s + e₂ s := by
    dsimp [e₂]
    ring
  have hv₃ (s : ℕ) : sigmaPadeNormalizedMoment d a s 3 = p₃ s + e₃ s := by
    dsimp [e₃]
    ring
  have hmodel (s : ℕ) :
      (p₀ s * p₂ s - p₁ s ^ 2 = -m ^ 2 * y ^ 2) ∧
        (p₀ s * p₃ s - p₁ s * p₂ s = -2 * m ^ 2 * x * y ^ 2) ∧
        (p₁ s * p₃ s - p₂ s ^ 2 = -m ^ 2 * y ^ 2) := by
    simpa [p₀, p₁, p₂, p₃] using
      twoPoleMoment_unitCircle_minors m x y θ s hre him hunit
  have hDidentity :
      (fun s => sigmaPadeNormalizedD d a s - (-m ^ 2 * y ^ 2)) =
        fun s => ((p₀ s + e₀ s) * (p₂ s + e₂ s) - p₀ s * p₂ s) -
          ((p₁ s + e₁ s) ^ 2 - p₁ s ^ 2) := by
    funext s
    rw [sigmaPadeNormalizedD_eq_normalizedMoments d a s ha.ne',
      hv₀ s, hv₁ s, hv₂ s, ← (hmodel s).1]
    ring
  have hBidentity :
      (fun s => sigmaPadeNormalizedB d a s - (-2 * m ^ 2 * x * y ^ 2)) =
        fun s => ((p₀ s + e₀ s) * (p₃ s + e₃ s) - p₀ s * p₃ s) -
          ((p₁ s + e₁ s) * (p₂ s + e₂ s) - p₁ s * p₂ s) := by
    funext s
    rw [sigmaPadeNormalizedB_eq_normalizedMoments d a s ha.ne',
      hv₀ s, hv₁ s, hv₂ s, hv₃ s, ← (hmodel s).2.1]
    ring
  have hCidentity :
      (fun s => sigmaPadeNormalizedC d a s - (-m ^ 2 * y ^ 2)) =
        fun s => ((p₁ s + e₁ s) * (p₃ s + e₃ s) - p₁ s * p₃ s) -
          ((p₂ s + e₂ s) ^ 2 - p₂ s ^ 2) := by
    funext s
    rw [sigmaPadeNormalizedC_eq_normalizedMoments d a s ha.ne',
      hv₁ s, hv₂ s, hv₃ s, ← (hmodel s).2.2]
    ring
  have hDerr : Tendsto (fun s =>
      ((p₀ s + e₀ s) * (p₂ s + e₂ s) - p₀ s * p₂ s) -
        ((p₁ s + e₁ s) ^ 2 - p₁ s ^ 2)) atTop (𝓝 0) := by
    simpa [pow_two] using hE₀₂.sub hE₁₁
  have hBerr : Tendsto (fun s =>
      ((p₀ s + e₀ s) * (p₃ s + e₃ s) - p₀ s * p₃ s) -
        ((p₁ s + e₁ s) * (p₂ s + e₂ s) - p₁ s * p₂ s)) atTop (𝓝 0) := by
    simpa using hE₀₃.sub hE₁₂
  have hCerr : Tendsto (fun s =>
      ((p₁ s + e₁ s) * (p₃ s + e₃ s) - p₁ s * p₃ s) -
        ((p₂ s + e₂ s) ^ 2 - p₂ s ^ 2)) atTop (𝓝 0) := by
    simpa [pow_two] using hE₁₃.sub hE₂₂
  refine ⟨?_, ?_, ?_⟩
  · have hz := hDidentity ▸ hDerr
    convert hz.add_const (-m ^ 2 * y ^ 2) using 1
    · ext s
      ring_nf
    · ring_nf
  · have hz := hBidentity ▸ hBerr
    convert hz.add_const (-2 * m ^ 2 * x * y ^ 2) using 1
    · ext s
      ring_nf
    · ring_nf
  · have hz := hCidentity ▸ hCerr
    convert hz.add_const (-m ^ 2 * y ^ 2) using 1
    · ext s
      ring_nf
    · ring_nf

/-- A unit-circle two-pole moment sequence is uniformly bounded by its weight. -/
theorem twoPoleMoment_abs_le_of_normSq_eq_one
    (m : ℝ) (θ : ℂ) (n : ℕ) (hunit : Complex.normSq θ = 1) :
    |twoPoleMoment m θ n| ≤ |m| := by
  have hnormSq : ‖θ‖ ^ 2 = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hunit
  have hnorm : ‖θ‖ = 1 := by
    have hnonneg := norm_nonneg θ
    nlinarith
  have hpow : ‖θ ^ (n + 1)‖ = 1 := by
    rw [norm_pow, hnorm]
    norm_num
  have hre : |(θ ^ (n + 1)).re| ≤ 1 := by
    simpa [hpow] using Complex.abs_re_le_norm (θ ^ (n + 1))
  unfold twoPoleMoment
  rw [abs_mul]
  nlinarith [abs_nonneg m]

/-- The boundedness premise in the coefficient-to-minor theorem follows from
the unit-circle condition, so an exponential remainder alone suffices for the
three source-minor limits. -/
theorem sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder
    (d m a C eta x y : ℝ) (ζ θ : ℂ)
    (hζ : ζ = (a : ℂ) * θ)
    (hre : θ.re = x) (him : θ.im = y)
    (hunit : Complex.normSq θ = 1)
    (heta : 0 ≤ eta) (ha : 0 < a) (heta_a : eta < a)
    (hr : ∀ n, |sigmaZeroPairRemainderMoment d m ζ n| ≤ C * eta ^ n) :
    Tendsto (fun s => sigmaPadeNormalizedD d a s) atTop
        (𝓝 (-m ^ 2 * y ^ 2)) ∧
      Tendsto (fun s => sigmaPadeNormalizedB d a s) atTop
        (𝓝 (-2 * m ^ 2 * x * y ^ 2)) ∧
      Tendsto (fun s => sigmaPadeNormalizedC d a s) atTop
        (𝓝 (-m ^ 2 * y ^ 2)) := by
  exact sigmaPadeNormalizedMinors_tendsto_of_twoPole_remainder
    d m a C eta |m| x y ζ θ hζ hre him hunit heta ha heta_a
    (fun n => twoPoleMoment_abs_le_of_normSq_eq_one m θ n hunit) hr

/-- Conditional E theorem for the original sigma pencil: the analytic
two-pole decomposition and exponential tail bound imply an eventually
non-real characteristic root, and the selected root branch converges. -/
theorem sigmaPadeOriginalPencil_root_tendsto_of_twoPole_remainder
    (d m a C eta x y : ℝ) (ζ θ : ℂ)
    (hζ : ζ = (a : ℂ) * θ)
    (hre : θ.re = x) (him : θ.im = y)
    (hunit : Complex.normSq θ = 1)
    (heta : 0 ≤ eta) (ha : 0 < a) (heta_a : eta < a)
    (hm : m ≠ 0) (hy : y ≠ 0)
    (hr : ∀ n, |sigmaZeroPairRemainderMoment d m ζ n| ≤ C * eta ^ n) :
    Tendsto (fun s => sigmaPadeQuadraticRootLower (-1)
      (-sigmaPadeAlpha d s) (-sigmaPadeBeta d s)) atTop
        (𝓝 (sigmaPadeQuadraticRootLower (-1) (-(2 * a * x)) (-a ^ 2))) ∧
      ∀ᶠ s : ℕ in atTop,
        sigmaPencilCharacteristicComplex d s
          (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d s)
            (-sigmaPadeBeta d s)) = 0 ∧
        (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d s)
          (-sigmaPadeBeta d s)).im ≠ 0 := by
  have hminors := sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder
    d m a C eta x y ζ θ hζ hre him hunit heta ha heta_a hr
  have hcoeff := sigmaPadeAlphaBeta_tendsto_of_twoPole_minor_limits
    d a m x y hminors.1 hminors.2.1 hminors.2.2 ha hm hy
  have hroot := sigmaPadeAlphaBetaRoot_tendsto d (2 * a * x) (a ^ 2)
    hcoeff.1 hcoeff.2
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    have := hunit
    have hxy' : x * x + y * y = 1 := by
      simpa [Complex.normSq_apply, hre, him] using this
    nlinarith
  have hnonreal := sigmaPadeOriginalPencil_eventually_has_nonreal_root
    d a m x y hminors.1 hminors.2.1 hminors.2.2 ha hm hy hxy
  exact ⟨hroot, hnonreal⟩

/-- For the orientation `theta.im < 0` arising from a positive transverse
displacement, the selected original-pencil root converges to `zeta` itself. -/
theorem sigmaPadeOriginalPencil_root_tendsto_to_twoPole
    (d m a C eta x y : ℝ) (ζ θ : ℂ)
    (hζ : ζ = (a : ℂ) * θ)
    (hre : θ.re = x) (him : θ.im = y)
    (hunit : Complex.normSq θ = 1)
    (heta : 0 ≤ eta) (ha : 0 < a) (heta_a : eta < a)
    (hm : m ≠ 0) (hy : y < 0)
    (hr : ∀ n, |sigmaZeroPairRemainderMoment d m ζ n| ≤ C * eta ^ n) :
    Tendsto (fun s => sigmaPadeQuadraticRootLower (-1)
      (-sigmaPadeAlpha d s) (-sigmaPadeBeta d s)) atTop (𝓝 ζ) ∧
      ∀ᶠ s : ℕ in atTop,
        sigmaPencilCharacteristicComplex d s
          (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d s)
            (-sigmaPadeBeta d s)) = 0 ∧
        (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d s)
          (-sigmaPadeBeta d s)).im ≠ 0 := by
  have hyne : y ≠ 0 := ne_of_lt hy
  have hgeneric := sigmaPadeOriginalPencil_root_tendsto_of_twoPole_remainder
    d m a C eta x y ζ θ hζ hre him hunit heta ha heta_a hm hyne hr
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    have := hunit
    have hxy' : x * x + y * y = 1 := by
      simpa [Complex.normSq_apply, hre, him] using this
    nlinarith
  have htheta : θ = (x : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hre]
    · simp [him]
  have hlimit : sigmaPadeQuadraticRootLower (-1) (-(2 * a * x)) (-a ^ 2) = ζ := by
    calc
      _ = (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) :=
        sigmaPadeQuadraticRootLower_twoPole_limit a x y ha hy hxy
      _ = (a : ℂ) * θ := by rw [← htheta]
      _ = ζ := hζ.symm
  have hroot : Tendsto (fun s => sigmaPadeQuadraticRootLower (-1)
      (-sigmaPadeAlpha d s) (-sigmaPadeBeta d s)) atTop (𝓝 ζ) := by
    rw [← hlimit]
    exact hgeneric.1
  exact ⟨hroot, hgeneric.2⟩

end CarrySigmaPade

end

#print axioms CarrySigmaPade.sigmaPadeRemainder_window_normalized_tendsto
#print axioms CarrySigmaPade.sigmaPadeQuadraticRootLower_tendsto
#print axioms CarrySigmaPade.sigmaPadeQuadraticRootLower_is_root
