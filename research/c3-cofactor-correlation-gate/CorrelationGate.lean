import GammaHeadCrosswalk
import IntervalGate
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

namespace C3CofactorCorrelation

open CarrySelfAdjointOperator CarryC3Tail CarryC3Boxes CarryC3Gamma CarryTwoEvenJets C3Cofactor
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- The real even coefficient used by the all-order source Bézout kernel. -/
abbrev nativeC := completedNativeRealEvenCharacteristicCoefficient

/-- The auxiliary all-order coefficient is exactly the factorial-normalized
source jet used by the original completed characteristic. -/
theorem nativeC_eq_sourceJet (n : ℕ) :
    (nativeC n : ℂ) = sourceJet (2 * n) completedNativeOperatorCharacteristic := by
  rw [← completedNativeEvenCharacteristicCoefficient_eq_real n]
  simp [completedNativeEvenCharacteristicCoefficient, completedGreenTaylorJet,
    sourceJet, div_eq_mul_inv, smul_eq_mul]
  ring

/-- Rescaling a nonzero Taylor series rescales its reciprocal coefficients
contragrediently. -/
theorem reciprocalJet_scale (a : ℝ) (c : ℕ → ℝ) (ha : a ≠ 0) (n : ℕ) :
    reciprocalJet (fun j => a * c j) n = a⁻¹ * reciprocalJet c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        simp only [reciprocalJet]
        field_simp [ha]
    | succ n =>
        rw [reciprocalJet, reciprocalJet]
        have hsum :
            (∑ j : Fin (n + 1), reciprocalJet (fun j => a * c j) j.val *
                (a * c (n + 1 - j.val))) =
              ∑ j : Fin (n + 1), (a⁻¹ * reciprocalJet c j.val) *
                (a * c (n + 1 - j.val)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih j.val (by omega)]
        rw [hsum]
        simp_rw [show a⁻¹ * reciprocalJet c _ * (a * c _) =
          reciprocalJet c _ * c _ by
            field_simp [ha]]
        have hden : (a * c 0)⁻¹ = a⁻¹ * (c 0)⁻¹ := by
          field_simp [ha]
        calc
          - (∑ x : Fin (n + 1), reciprocalJet c x.val * c (n + 1 - x.val)) /
                (a * c 0) =
              - (∑ x : Fin (n + 1), reciprocalJet c x.val * c (n + 1 - x.val)) *
                (a * c 0)⁻¹ := by rw [div_eq_mul_inv]
          _ = - (∑ x : Fin (n + 1), reciprocalJet c x.val * c (n + 1 - x.val)) *
                (a⁻¹ * (c 0)⁻¹) := by rw [hden]
          _ = a⁻¹ *
                (-(∑ x : Fin (n + 1), reciprocalJet c x.val * c (n + 1 - x.val)) /
                  c 0) := by rw [div_eq_mul_inv]; ring

theorem convolution_scale_both (a b : ℕ → ℝ) (x y : ℝ) (n : ℕ) :
    convolution (fun j => x * a j) (fun j => y * b j) n =
      (x * y) * convolution a b n := by
  unfold convolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem convolution_scale_left (a b : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    convolution (fun j => x * a j) b n = x * convolution a b n := by
  unfold convolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def normalizedPolynomialJet (r : ℕ) : ℝ :=
  if r = 0 then 1 else if r = 2 then -4 else 0

def normalizedExponentialJet (p : ℝ) (r : ℕ) : ℝ :=
  (-p / 2) ^ r / (r.factorial : ℝ)

def chartScale : ℝ := 1 - Real.exp (Real.log 3 / 2)

def chartRatio : ℝ := Real.exp (Real.log 3 / 2) / chartScale

def normalizedChartDenominator (q ell : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 1 else q * (-1 : ℝ) ^ (r + 1) * ell ^ r / (r.factorial : ℝ)

def normalizedChartReciprocal (q ell : ℝ) : ℕ → ℝ :=
  reciprocalJet (normalizedChartDenominator q ell)

theorem chartScale_ne_zero : chartScale ≠ 0 := by
  have hbox := chart_center_interval_negative_tight
  have hcontains := chart_jet_box_tight 0
  have hboxR : ((chartJetBoxTight 0).hi : ℝ) < 0 := by exact_mod_cast hbox
  have hjet : chartRealJet 0 < 0 := lt_of_le_of_lt hcontains.2 hboxR
  have heq : chartRealJet 0 = chartScale := by
    norm_num [chartRealJet, chartScale]
  rw [← heq]
  exact ne_of_lt hjet

theorem chartRatio_mul_scale : chartRatio * chartScale =
    Real.exp (Real.log 3 / 2) := by
  unfold chartRatio
  field_simp [chartScale_ne_zero]

theorem polynomialRealJet_eq_normalized (r : ℕ) :
    polynomialRealJet r = (-1 / 8 : ℝ) * normalizedPolynomialJet r := by
  by_cases h0 : r = 0
  · subst r
    norm_num [polynomialRealJet, normalizedPolynomialJet]
  · by_cases h2 : r = 2
    · subst r
      norm_num [polynomialRealJet, normalizedPolynomialJet]
    · simp [polynomialRealJet, normalizedPolynomialJet, h0, h2]

theorem exponentialRealJet_eq_normalized (r : ℕ) :
    exponentialRealJet r = Real.exp (-Real.log Real.pi / 4) *
      normalizedExponentialJet (Real.log Real.pi) r := by
  unfold exponentialRealJet normalizedExponentialJet
  ring

theorem chartRealJet_eq_normalized (r : ℕ) :
    chartRealJet r = chartScale *
      normalizedChartDenominator chartRatio (Real.log 3) r := by
  cases r with
  | zero =>
      simp [chartRealJet, chartScale, normalizedChartDenominator]
  | succ n =>
      simp only [chartRealJet, normalizedChartDenominator, Nat.succ_ne_zero,
        ↓reduceIte]
      rw [neg_pow]
      have hpow : (-1 : ℝ) ^ (n + 2) = -(-1 : ℝ) ^ (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        norm_num
      rw [show n + 1 + 1 = n + 2 by omega, hpow]
      have hscale : chartScale * chartRatio = Real.exp (Real.log 3 / 2) := by
        rw [mul_comm, chartRatio_mul_scale]
      calc
        0 - Real.exp (Real.log 3 / 2) *
            ((-1 : ℝ) ^ (n + 1) * (Real.log 3) ^ (n + 1)) /
              ((n + 1).factorial : ℝ) =
            -Real.exp (Real.log 3 / 2) *
              ((-1 : ℝ) ^ (n + 1) * (Real.log 3) ^ (n + 1)) /
                ((n + 1).factorial : ℝ) := by ring
        _ = chartScale * (chartRatio *
            (-((-1 : ℝ) ^ (n + 1) * (Real.log 3) ^ (n + 1)) /
              ((n + 1).factorial : ℝ))) := by
              rw [← hscale]
              ring
        _ = chartScale *
            (chartRatio * -(-1 : ℝ) ^ (n + 1) * (Real.log 3) ^ (n + 1) /
              ((n + 1).factorial : ℝ)) := by ring_nf

theorem reciprocalJet_chart_eq_normalized (r : ℕ) :
    reciprocalJet chartRealJet r = chartScale⁻¹ *
      normalizedChartReciprocal chartRatio (Real.log 3) r := by
  have hfun : chartRealJet =
      (fun j => chartScale * normalizedChartDenominator chartRatio (Real.log 3) j) := by
    funext j
    exact chartRealJet_eq_normalized j
  rw [hfun]
  exact reciprocalJet_scale chartScale _ chartScale_ne_zero r

def normalizedOuterBaseJet (p q ell : ℝ) : ℕ → ℝ :=
  fun r => convolution
    (convolution normalizedPolynomialJet (normalizedExponentialJet p))
    (normalizedChartReciprocal q ell) r

def normalizedLeftJet48 : ℝ → ℝ → ℝ → ℕ → ℝ :=
  fun p q ell r => convolution (normalizedOuterBaseJet p q ell) head48RealJet r

def leftJet48Scale : ℝ :=
  (-1 / 8 : ℝ) * Real.exp (-Real.log Real.pi / 4) * chartScale⁻¹

theorem leftRealJet48_eq_normalized (r : ℕ) :
    leftRealJet48 r = leftJet48Scale *
      normalizedLeftJet48 (Real.log Real.pi) chartRatio (Real.log 3) r := by
  have hp : polynomialRealJet = fun j => (-1 / 8 : ℝ) * normalizedPolynomialJet j :=
    funext polynomialRealJet_eq_normalized
  have he : exponentialRealJet =
      fun j => Real.exp (-Real.log Real.pi / 4) * normalizedExponentialJet
        (Real.log Real.pi) j := funext exponentialRealJet_eq_normalized
  have hc : reciprocalJet chartRealJet =
      fun j => chartScale⁻¹ * normalizedChartReciprocal chartRatio (Real.log 3) j :=
    funext reciprocalJet_chart_eq_normalized
  have hinner : convolution polynomialRealJet exponentialRealJet =
      fun j => ((-1 / 8 : ℝ) * Real.exp (-Real.log Real.pi / 4)) *
        convolution normalizedPolynomialJet
          (normalizedExponentialJet (Real.log Real.pi)) j := by
    funext j
    rw [hp, he]
    exact convolution_scale_both normalizedPolynomialJet
      (normalizedExponentialJet (Real.log Real.pi)) (-1 / 8 : ℝ)
      (Real.exp (-Real.log Real.pi / 4)) j
  have hbase : convolution (convolution polynomialRealJet exponentialRealJet)
      (reciprocalJet chartRealJet) =
      fun j => (((-1 / 8 : ℝ) * Real.exp (-Real.log Real.pi / 4)) *
        chartScale⁻¹) * normalizedOuterBaseJet (Real.log Real.pi)
          chartRatio (Real.log 3) j := by
    funext j
    rw [hinner, hc]
    exact convolution_scale_both
      (fun k => convolution normalizedPolynomialJet
        (normalizedExponentialJet (Real.log Real.pi)) k)
      (normalizedChartReciprocal chartRatio (Real.log 3))
      ((-1 / 8 : ℝ) * Real.exp (-Real.log Real.pi / 4)) chartScale⁻¹ j
  unfold leftRealJet48 normalizedLeftJet48 leftJet48Scale
  rw [hbase]
  exact convolution_scale_left (normalizedOuterBaseJet (Real.log Real.pi)
    chartRatio (Real.log 3)) head48RealJet
    (((-1 / 8 : ℝ) * Real.exp (-Real.log Real.pi / 4)) * chartScale⁻¹) r

def normalizedOuterBasePolynomialCoeff (q ell : ℝ) (n e : ℕ) : ℝ :=
  if e ≤ n then
    ∑ i ∈ Finset.range (n + 1),
      if i + e ≤ n then
        normalizedPolynomialJet i *
          (((-1 / 2 : ℝ) ^ e / (e.factorial : ℝ)) *
            normalizedChartReciprocal q ell (n - i - e))
      else 0
  else 0

def normalizedOuterBaseHorner (p q ell : ℝ) (n : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (n + 1),
    normalizedOuterBasePolynomialCoeff q ell n e * p ^ e

theorem normalizedOuterBaseJet_eq_horner (r : Fin 13) (p q ell : ℝ) :
    normalizedOuterBaseJet p q ell r.val = normalizedOuterBaseHorner p q ell r.val := by
  fin_cases r <;>
    simp [normalizedOuterBaseJet, normalizedOuterBaseHorner,
      normalizedOuterBasePolynomialCoeff, normalizedPolynomialJet,
      normalizedExponentialJet, normalizedChartReciprocal, convolution,
      reciprocalJet, Finset.sum_range_succ] <;> ring

theorem convolution_cross_through_twelve (r : Fin 13)
    (a b c : ℕ → ℝ) :
    convolution (convolution a b) c r.val =
      convolution b (convolution a c) r.val := by
  fin_cases r <;> simp [convolution, Finset.sum_range_succ] <;> ring

def normalizedGammaJet (r : ℕ) : ℝ :=
  if hr : r < 13 then
    (gammaRealReference13 ⟨r, hr⟩ : ℝ) /
      (gammaRealReference13 ⟨0, by omega⟩ : ℝ)
  else 0

def gammaReferenceJet (r : ℕ) : ℝ :=
  if hr : r < 13 then (gammaRealReference13 ⟨r, hr⟩ : ℝ) else 0

def gammaReferenceScale : ℝ :=
  (gammaRealReference13 ⟨0, by omega⟩ : ℝ)

theorem gammaReferenceJet_eq_normalized (r : ℕ) (hr : r < 13) :
    gammaReferenceJet r = gammaReferenceScale * normalizedGammaJet r := by
  simp [gammaReferenceJet, normalizedGammaJet, gammaReferenceScale, hr]
  have h0 : ((gammaRealReference13 ⟨0, by omega⟩ : ℚ) : ℝ) ≠ 0 := by
    norm_num [CarryC3Gamma.gammaRealReference13]
  rw [div_eq_mul_inv]
  calc
    (gammaRealReference13 ⟨r, hr⟩ : ℝ) =
        (((gammaRealReference13 ⟨0, by omega⟩ : ℝ) *
          (gammaRealReference13 ⟨0, by omega⟩ : ℝ)⁻¹) *
            (gammaRealReference13 ⟨r, hr⟩ : ℝ)) := by
          rw [mul_inv_cancel₀ h0, one_mul]
    _ = (gammaRealReference13 ⟨0, by omega⟩ : ℝ) *
        ((gammaRealReference13 ⟨0, by omega⟩ : ℝ)⁻¹ *
          (gammaRealReference13 ⟨r, hr⟩ : ℝ)) := by rw [mul_assoc]
    _ = (gammaRealReference13 ⟨0, by omega⟩ : ℝ) *
        ((gammaRealReference13 ⟨r, hr⟩ : ℝ) *
          (gammaRealReference13 ⟨0, by omega⟩ : ℝ)⁻¹) := by
          rw [mul_comm _ (gammaRealReference13 ⟨r, hr⟩ : ℝ)]

def normalizedOuterCompletedJet48 (r : ℕ) : ℝ :=
  convolution (normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3))
    normalizedGammaJet r

def normalizedCompletedJet48 (r : ℕ) : ℝ :=
  convolution head48RealJet normalizedOuterCompletedJet48 r

theorem normalizedCompleted_group (r : Fin 13) :
    convolution (normalizedLeftJet48 (Real.log Real.pi) chartRatio (Real.log 3))
      normalizedGammaJet r.val = normalizedCompletedJet48 r.val := by
  change convolution
      (convolution (normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3))
        head48RealJet) normalizedGammaJet r.val =
    convolution head48RealJet
      (convolution (normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3))
        normalizedGammaJet) r.val
  exact convolution_cross_through_twelve r
    (normalizedOuterBaseJet (Real.log Real.pi) chartRatio (Real.log 3))
    head48RealJet normalizedGammaJet

def completedJet48Scale : ℝ := leftJet48Scale * gammaReferenceScale

theorem finiteCompletedRealJet48_eq_normalized (r : Fin 13) :
    finiteCompletedRealJet48 r = completedJet48Scale *
      normalizedCompletedJet48 r.val := by
  have hg : gammaReferenceJet = fun j => gammaReferenceScale * normalizedGammaJet j := by
    funext j
    by_cases hj : j < 13
    · exact gammaReferenceJet_eq_normalized j hj
    · simp [gammaReferenceJet, normalizedGammaJet, hj]
  have hl : leftRealJet48 = fun j => leftJet48Scale *
      normalizedLeftJet48 (Real.log Real.pi) chartRatio (Real.log 3) j :=
    funext leftRealJet48_eq_normalized
  have hsum : finiteCompletedRealJet48 r =
      convolution leftRealJet48 gammaReferenceJet r.val := by
    unfold finiteCompletedRealJet48 convolution gammaReferenceJet
    apply Finset.sum_congr rfl
    intro j hj
    have hjr : j ≤ r.val := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simp only [dif_pos (by omega : r.val-j < 13)]
  unfold completedJet48Scale
  rw [hsum, hl, hg]
  rw [convolution_scale_both]
  rw [normalizedCompleted_group r]

end
end C3CofactorCorrelation
