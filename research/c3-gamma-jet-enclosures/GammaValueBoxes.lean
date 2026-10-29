import LogGammaData

namespace CarryC3Gamma
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def realGammaPolynomial (r : Fin 7) (L : ℝ) (a : Fin 7 → ℝ) : ℝ :=
  3*∑ j ∈ Finset.range (r.val+1), (2*L)^j/(j.factorial:ℝ)*
    (-1/2:ℝ)^(r.val-j)*a ⟨r.val-j,by omega⟩

theorem real_gamma_polynomial_error (r : Fin 7) (L U e : ℝ)
    (he : 0 ≤ e) (hL : |L| ≤ 2) (hU : |U| ≤ 2) (hLU : |L-U| ≤ e)
    (a b : Fin 7 → ℝ) (ha : ∀ j, |a j| ≤ 30000)
    (hab : ∀ j, |a j-b j| ≤ e) :
    |realGammaPolynomial r L a-realGammaPolynomial r U b| ≤ 10^11*e := by
  have hsmall (j : ℕ) (hj : j ≤ 6) : |(2*L)^j-(2*U)^j| ≤ 49152*e := by
    have hm : max |2*L| |2*U| ≤ 4 := by
      apply max_le
      · simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using
          (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ)≤2)).trans_eq (show (2:ℝ)*2=4 by norm_num)
      · simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using
          (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤2)).trans_eq (show (2:ℝ)*2=4 by norm_num)
    have hp : max |2*L| |2*U| ^ (j-1) ≤ (4:ℝ)^6 := by
      apply (pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hm _).trans
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hd : |2*L-2*U| ≤ 2*e := by
      rw [← mul_sub,abs_mul]
      norm_num
      linarith
    have h := abs_pow_sub_pow_le (a:=2*L) (b:=2*U) (n:=j)
    calc
      _ ≤ (2*e)*j*4^6 := h.trans (mul_le_mul
        (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg j)) hp
        (pow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _) (by positivity))
      _ ≤ 49152*e := by
        have hjr : (j:ℝ) ≤ 6 := by exact_mod_cast hj
        norm_num
        nlinarith
  have ht (j : ℕ) (hj : j ∈ Finset.range (r.val+1)) :
      |(2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*a ⟨r.val-j,by omega⟩-
       (2*U)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*b ⟨r.val-j,by omega⟩| ≤
      1500000000*e := by
    have hj6 : j ≤ 6 := by have := Finset.mem_range.mp hj; omega
    let d : Fin 7 := ⟨r.val-j,by omega⟩
    have hp : |(2*U)^j| ≤ 4096 := by
      rw [abs_pow]
      calc
        |2*U|^j ≤ (4:ℝ)^j := by
          gcongr
          simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using
            (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤2)).trans_eq (show (2:ℝ)*2=4 by norm_num)
        _ ≤ 4^6 := pow_le_pow_right₀ (by norm_num) hj6
        _ = _ := by norm_num
    have hc : |(-1/2:ℝ)^(r.val-j)/(j.factorial:ℝ)| ≤ 1 := by
      rw [abs_div,abs_pow]
      norm_num only [abs_of_nonneg (show (0:ℝ)≤j.factorial by positivity),
        abs_neg,abs_div,abs_one,abs_of_pos (show (0:ℝ)<2 by norm_num)]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<j.factorial)).2
      have hf : (1:ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
      exact (pow_le_one₀ (by norm_num) (by norm_num)).trans (by simpa using hf)
    have hi : (2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*a d-
        (2*U)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*b d =
      (((2*L)^j-(2*U)^j)*a d+(2*U)^j*(a d-b d))*
        ((-1/2:ℝ)^(r.val-j)/(j.factorial:ℝ)) := by ring
    change |(2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*a d-
        (2*U)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*b d| ≤ _
    rw [hi,abs_mul]
    calc
      _ ≤ |((2*L)^j-(2*U)^j)*a d+(2*U)^j*(a d-b d)| :=
        mul_le_of_le_one_right (abs_nonneg _) hc
      _ ≤ |(2*L)^j-(2*U)^j| * |a d|+|(2*U)^j| * |a d-b d| := by
        simpa only [abs_mul] using abs_add_le (((2*L)^j-(2*U)^j)*a d) ((2*U)^j*(a d-b d))
      _ ≤ (49152*e)*30000+4096*e := add_le_add
        (mul_le_mul (hsmall j hj6) (ha d) (abs_nonneg _) (by positivity))
        (mul_le_mul hp (hab d) (abs_nonneg _) (by norm_num))
      _ ≤ 1500000000*e := by nlinarith
  unfold realGammaPolynomial
  rw [← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),← Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num : (0:ℝ)≤3)).trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ht) (by norm_num : (0:ℝ)≤3)).trans
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hr : (r.val+1:ℝ) ≤ 7 := by exact_mod_cast (show r.val+1 ≤ 7 by omega)
  norm_num
  nlinarith

/-- Rational rectangular boxes, with the exact imaginary/real phase retained. -/
def gammaReference (r : Fin 7) : ℂ := Complex.I^r.val*(gammaRealReference r:ℂ)

theorem gamma_coefficient_real (r : Fin 7) :
    gammaCoefficient r.val (Real.log 3) = Complex.I^r.val*
      (realGammaPolynomial r (Real.log 3) (fun j => (rationalCoefficient 512 j.val:ℝ)):ℂ) := by
  unfold gammaCoefficient realGammaPolynomial
  push_cast
  ring

theorem native_gamma_seven_boxes (r : Fin 7) :
    ‖sourceJet r.val nativeGamma-gammaReference r‖ ≤ (1/10^18:ℝ) := by
  let a : Fin 7 → ℝ := fun j => rationalCoefficient 512 j.val
  let b : Fin 7 → ℝ := fun j => coefficientReference j
  have hab : ∀ j, |a j-b j| ≤ (1/10^30:ℝ) := by
    intro j
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using
      rat_abs_cast_le (rational_coefficient_boxes j)
  have ha : ∀ j, |a j| ≤ 30000 := by
    intro j
    have hb : |b j| ≤ 20000 := by
      simpa only [Rat.cast_ofNat] using rat_abs_cast_le (coefficient_reference_bound j)
    have hh := (abs_sub_abs_le_abs_sub (a j) (b j)).trans (hab j)
    linarith
  have hU : |(logReference:ℝ)| ≤ 2 := by norm_num [logReference]
  have hL : |Real.log 3| ≤ 2 := by
    have hh := (abs_sub_abs_le_abs_sub (Real.log 3) (logReference:ℝ)).trans log_three_box
    norm_num [logReference] at hh ⊢
    linarith
  have hp := real_gamma_polynomial_error r (Real.log 3) logReference (1/10^30)
    (by positivity) hL hU log_three_box a b ha hab
  have hr : |realGammaPolynomial r logReference b-(gammaRealReference r:ℝ)| ≤ (1/10^25:ℝ) := by
    have he : (gammaRationalPolynomial r:ℝ) = realGammaPolynomial r logReference b := by
      unfold gammaRationalPolynomial realGammaPolynomial
      push_cast
      rfl
    rw [← he]
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using
      rat_abs_cast_le (gamma_rational_boxes r)
  have hb := (abs_sub_le (realGammaPolynomial r (Real.log 3) a)
    (realGammaPolynomial r logReference b) (gammaRealReference r:ℝ)).trans (add_le_add hp hr)
  have he : ‖sourceJet r.val finiteNativeGamma-gammaReference r‖ ≤
      10^11*(1/10^30)+(1/10^25:ℝ) := by
    rw [finite_native_gamma_coefficient,gamma_coefficient_real,gammaReference,← mul_sub,norm_mul,
      norm_pow,Complex.norm_I,one_pow,one_mul]
    have hc : (gammaRealReference r:ℂ)=((gammaRealReference r:ℝ):ℂ) := by simp
    rw [hc,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
    exact hb
  have ht := (norm_sub_le_norm_sub_add_norm_sub (sourceJet r.val nativeGamma) (sourceJet r.val finiteNativeGamma)
    (gammaReference r)).trans (add_le_add (native_gamma_jet_error r.val) he)
  have hpow : (4:ℝ)^r.val ≤ 4096 := by
    calc
      (4:ℝ)^r.val ≤ (4:ℝ)^6 := pow_le_pow_right₀ (by norm_num) (show r.val ≤ 6 by omega)
      _ = 4096 := by norm_num
  apply ht.trans
  norm_num
  nlinarith

end
end CarryC3Gamma
