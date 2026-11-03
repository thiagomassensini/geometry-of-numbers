import GammaNineReference
namespace CarryOddHeadSource
open CarryC3Gamma CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Rational rectangular boxes, with the exact imaginary/real phase retained. -/
def gammaReference9 (r : Fin 9) : ℂ := Complex.I^r.val*(gammaRealReference9 r:ℂ)

theorem gamma_coefficient_real9 (r : Fin 9) :
    gammaCoefficient r.val (Real.log 3) = Complex.I^r.val*
      (realGammaPolynomial9 r (Real.log 3) (fun j => (rationalCoefficient 512 j.val:ℝ)):ℂ) := by
  unfold gammaCoefficient realGammaPolynomial9
  push_cast
  ring

theorem native_gamma_nine_boxes (r : Fin 9) :
    ‖sourceJet r.val nativeGamma-gammaReference9 r‖ ≤ (1/10^18:ℝ) := by
  let a : Fin 9 → ℝ := fun j => rationalCoefficient 512 j.val
  let b : Fin 9 → ℝ := fun j => coefficientReference9 j
  have hab : ∀ j, |a j-b j| ≤ (1/10^30:ℝ) := by
    intro j
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using
      rat_abs_cast_le (rational_coefficient_boxes9 j)
  have ha : ∀ j, |a j| ≤ 300000 := by
    intro j
    have hb : |b j| ≤ 290000 := by
      simpa only [Rat.cast_ofNat] using rat_abs_cast_le (coefficient_reference9_bound j)
    have hh := (abs_sub_abs_le_abs_sub (a j) (b j)).trans (hab j)
    linarith
  have hU : |(logReference:ℝ)| ≤ 2 := by norm_num [logReference]
  have hL : |Real.log 3| ≤ 2 := by
    have hh := (abs_sub_abs_le_abs_sub (Real.log 3) (logReference:ℝ)).trans log_three_box
    norm_num [logReference] at hh ⊢
    linarith
  have hp := real_gamma_polynomial_error9 r (Real.log 3) logReference (2/10^32) (1/10^30)
    (by positivity) (by positivity) hL hU log_three_box_tight a b ha hab
  have hr : |realGammaPolynomial9 r logReference b-(gammaRealReference9 r:ℝ)| ≤ (1/10^25:ℝ) := by
    have he : (gammaRationalPolynomial9 r:ℝ) = realGammaPolynomial9 r logReference b := by
      unfold gammaRationalPolynomial9 realGammaPolynomial9
      push_cast
      rfl
    rw [← he]
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using
      rat_abs_cast_le (gamma_rational_boxes9 r)
  have hb := (abs_sub_le (realGammaPolynomial9 r (Real.log 3) a)
    (realGammaPolynomial9 r logReference b) (gammaRealReference9 r:ℝ)).trans (add_le_add hp hr)
  have he : ‖sourceJet r.val finiteNativeGamma-gammaReference9 r‖ ≤
      10^13*(2/10^32)+10^7*(1/10^30)+(1/10^25:ℝ) := by
    rw [finite_native_gamma_coefficient,gamma_coefficient_real9,gammaReference9,← mul_sub,norm_mul,
      norm_pow,Complex.norm_I,one_pow,one_mul]
    have hc : (gammaRealReference9 r:ℂ)=((gammaRealReference9 r:ℝ):ℂ) := by simp
    rw [hc,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
    exact hb
  have ht := (norm_sub_le_norm_sub_add_norm_sub (sourceJet r.val nativeGamma) (sourceJet r.val finiteNativeGamma)
    (gammaReference9 r)).trans (add_le_add (native_gamma_jet_error r.val) he)
  have hpow : (4:ℝ)^r.val ≤ 65536 := by
    calc
      (4:ℝ)^r.val ≤ (4:ℝ)^8 := pow_le_pow_right₀ (by norm_num) (show r.val ≤ 8 by omega)
      _ = 65536 := by norm_num
  apply ht.trans
  norm_num
  nlinarith

end
end CarryOddHeadSource
