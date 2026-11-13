import GammaThirteen
import TightGammaJets

namespace CarryC3Gamma

open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
open Set Filter Topology
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 1024

/-- The four finite Gamma denominator jets needed beyond the existing order-12
table. They are rational reference points, not assumed exact coefficients. -/
def coefficientReferenceHigh : Fin 4 → ℚ := ![
  26843545247171230732829769444443560498101940515839004699293/10^50,
  107374182116574311421858737621042192253994661316152572787549/10^50,
  429496729372719237563122715845373968265295194150195457913194/10^50,
  1717986918217927256246884621253529680930688653157179122930616/10^50]

def coefficientReference17 (r : Fin 17) : ℚ :=
  if h : r.val < 13 then coefficientReference13 ⟨r.val, h⟩
  else coefficientReferenceHigh ⟨r.val - 13, by omega⟩

theorem rational_coefficient_high_boxes (r : Fin 4) :
    |rationalCoefficient 512 (r.val + 13) - coefficientReferenceHigh r| ≤
      (1/10^45:ℚ) := by
  fin_cases r <;> decide +kernel

theorem rational_coefficient_boxes17 (r : Fin 17) :
    |rationalCoefficient 512 r.val - coefficientReference17 r| ≤
      (1/10^45:ℚ) := by
  by_cases hr : r.val < 13
  · simpa [coefficientReference17, hr] using
      rational_coefficient_boxes13 ⟨r.val, hr⟩
  · let k : Fin 4 := ⟨r.val - 13, by omega⟩
    have hk := rational_coefficient_high_boxes k
    have hval : k.val + 13 = r.val := by simp [k]; omega
    simpa [coefficientReference17, hr, k, hval] using hk

theorem coefficient_reference17_abs_bound (r : Fin 17) :
    |(coefficientReference17 r : ℝ)| ≤ (4:ℝ)^(r.val+1) := by
  fin_cases r <;>
    norm_num [coefficientReference17, coefficientReference13,
      coefficientReferenceHigh]

def gammaRationalPolynomial17 (r : Fin 17) : ℚ :=
  3*∑ j ∈ Finset.range (r.val+1),
    (2*logReferenceTight)^j/(j.factorial:ℚ)*(-1/2:ℚ)^(r.val-j)*
      coefficientReference17 ⟨r.val-j, by omega⟩

/-- The exact rational Gamma center used by the finite source enclosure.  It is
the polynomial evaluated at the rational log and coefficient centers; the
separate native-Gamma theorem below transports this center to the original
analytic Gamma factor. -/
def gammaRealReference17 (r : Fin 17) : ℚ := gammaRationalPolynomial17 r

theorem gamma_rational_reference_eq17 (r : Fin 17) :
    gammaRationalPolynomial17 r = gammaRealReference17 r := rfl

def realGammaPolynomial17 (r : Fin 17) (L : ℝ)
    (a : Fin 17 → ℝ) : ℝ :=
  3*∑ j ∈ Finset.range (r.val+1),
    (2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*
      a ⟨r.val-j, by omega⟩

theorem real_gamma_polynomial_error17 (r : Fin 17) (L U eL eA : ℝ)
    (heL : 0 ≤ eL) (heA : 0 ≤ eA) (hL : |L| ≤ 2) (hU : |U| ≤ 2)
    (hLU : |L-U| ≤ eL) (a b : Fin 17 → ℝ)
    (ha : ∀ j, |a j| ≤ (4:ℝ)^(j.val+2))
    (hab : ∀ j, |a j-b j| ≤ eA) :
    |realGammaPolynomial17 r L a-realGammaPolynomial17 r U b| ≤
      24*(r.val+1:ℝ)*(r.val:ℝ)*4^r.val*eL+
        3*(r.val+1:ℝ)*4^r.val*eA := by
  have hsmall (j : ℕ) (hj : j ≤ 16) :
      |(2*L)^j-(2*U)^j| ≤ (2*eL)*j*4^(j-1) := by
    have hm : max |2*L| |2*U| ≤ 4 := by
      apply max_le
      · simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
          (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ)≤2)).trans_eq
            (show (2:ℝ)*2=4 by norm_num)
      · simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
          (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤2)).trans_eq
            (show (2:ℝ)*2=4 by norm_num)
    have hp : (max |2*L| |2*U|)^(j-1) ≤ (4:ℝ)^(j-1) := by
      exact pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hm _
    have hd : |2*L-2*U| ≤ 2*eL := by
      rw [← mul_sub, abs_mul]
      norm_num
      linarith
    have h := abs_pow_sub_pow_le (a:=2*L) (b:=2*U) (n:=j)
    calc
      _ ≤ |2*L - 2*U| * j * (max |2*L| |2*U|)^(j-1) := h
      _ ≤ (2*eL)*j*4^(j-1) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg j)) hp
          (pow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _) (by positivity)
  have ht (j : ℕ) (hj : j ∈ Finset.range (r.val+1)) :
      |(2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*
          a ⟨r.val-j,by omega⟩ -
        (2*U)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*
          b ⟨r.val-j,by omega⟩| ≤
        2*eL*(r.val:ℝ)*4^(r.val+1)+4^r.val*eA := by
    have hj16 : j ≤ 16 := by have h := Finset.mem_range.mp hj; omega
    let d : Fin 17 := ⟨r.val-j, by omega⟩
    have hc : |(-1/2:ℝ)^(r.val-j)/(j.factorial:ℝ)| ≤ 1 := by
      rw [abs_div, abs_pow]
      norm_num only [abs_of_nonneg (show (0:ℝ)≤j.factorial by positivity),
        abs_neg, abs_div, abs_one, abs_of_pos (show (0:ℝ)<2 by norm_num)]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<j.factorial)).2
      have hf : (1:ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
      exact (pow_le_one₀ (by norm_num) (by norm_num)).trans (by simpa using hf)
    have hp : |(2*U)^j| ≤ (4:ℝ)^j := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (by positivity) (by
        simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
          (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤2)).trans_eq
            (show (2:ℝ)*2=4 by norm_num)) _
    have hi : (2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*a d-
        (2*U)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*b d =
      (((2*L)^j-(2*U)^j)*a d+(2*U)^j*(a d-b d))*
        ((-1/2:ℝ)^(r.val-j)/(j.factorial:ℝ)) := by ring
    change |(2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*a d-
        (2*U)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*b d| ≤ _
    rw [hi, abs_mul]
    calc
      _ ≤ |((2*L)^j-(2*U)^j)*a d+(2*U)^j*(a d-b d)| :=
        mul_le_of_le_one_right (abs_nonneg _) hc
      _ ≤ |(2*L)^j-(2*U)^j| * |a d| + |(2*U)^j| * |a d-b d| := by
        simpa only [abs_mul] using abs_add_le
          (((2*L)^j-(2*U)^j)*a d) ((2*U)^j*(a d-b d))
      _ ≤ ((2*eL)*j*4^(j-1))*4^(d.val+2)+(4:ℝ)^j*eA := add_le_add
        (mul_le_mul (hsmall j hj16) (ha d) (abs_nonneg _) (by positivity))
        (mul_le_mul hp (hab d) (abs_nonneg _) (by positivity))
      _ ≤ 2*eL*(r.val:ℝ)*4^(r.val+1)+4^r.val*eA := by
        by_cases hj0 : j=0
        · subst j
          simp
          have hpow : (1:ℝ) ≤ 4^r.val := by
            calc
              1 = (1:ℝ)^r.val := by simp
              _ ≤ 4^r.val := pow_le_pow_left₀ (by norm_num) (by norm_num) _
          have hsec : eA ≤ 4^r.val*eA :=
            by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow heA
          have hfirst : 0 ≤ 2*eL*(r.val:ℝ)*4^(r.val+1) := by positivity
          nlinarith [hsec, hfirst]
        · have hpow : (4:ℝ)^(j-1)*(4:ℝ)^(d.val+2) = 4^(r.val+1) := by
            have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
            have hjle : j ≤ r.val := by
              have hmem := Finset.mem_range.mp hj
              omega
            have hd : d.val = r.val-j := by simp [d]
            have hexp : (j-1)+(d.val+2) = r.val+1 := by
              rw [hd]
              omega
            calc
              (4:ℝ)^(j-1)*(4:ℝ)^(d.val+2) =
                  (4:ℝ)^((j-1)+(d.val+2)) := by rw [← pow_add]
              _ = (4:ℝ)^(r.val+1) := by rw [hexp]
          have hjrNat : j ≤ r.val := by
            have hmem := Finset.mem_range.mp hj
            omega
          have hjr : (j:ℝ) ≤ r.val := by exact_mod_cast hjrNat
          have hfirst : (2*eL)*j*4^(j-1)*4^(d.val+2) ≤
              2*eL*(r.val:ℝ)*4^(r.val+1) := by
            calc
              (2*eL)*j*4^(j-1)*4^(d.val+2) =
                  (2*eL)*(j:ℝ)*(4^(j-1)*4^(d.val+2)) := by ring
              _ = (2*eL)*(j:ℝ)*4^(r.val+1) := by rw [hpow]
              _ ≤ (2*eL)*(r.val:ℝ)*4^(r.val+1) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hjr (by positivity)) (by positivity)
          have hpjr : (4:ℝ)^j ≤ (4:ℝ)^r.val :=
            pow_le_pow_right₀ (by norm_num) hjrNat
          have hsecond : (4:ℝ)^j*eA ≤ (4:ℝ)^r.val*eA :=
            mul_le_mul_of_nonneg_right hpjr heA
          have hfirst' : (2*eL)*j*(4^(j-1)*4^(d.val+2)) ≤
              2*eL*(r.val:ℝ)*4^(r.val+1) := by
            simpa only [mul_assoc] using hfirst
          calc
            ((2*eL)*j*4^(j-1)) * 4^(d.val+2) + (4:ℝ)^j*eA =
                (2*eL)*j*(4^(j-1)*4^(d.val+2))+(4:ℝ)^j*eA := by ring
            _ ≤ 2*eL*(r.val:ℝ)*4^(r.val+1)+(4:ℝ)^r.val*eA := by
              exact add_le_add hfirst' hsecond
  unfold realGammaPolynomial17
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<3),
    ← Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (by norm_num : (0:ℝ)≤3)).trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ht)
    (by norm_num : (0:ℝ)≤3)).trans
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  apply le_of_eq
  ring

theorem gamma_coefficient_real17 (r : Fin 17) :
    gammaCoefficient r.val (Real.log 3) = Complex.I^r.val *
      (realGammaPolynomial17 r (Real.log 3)
        (fun j => (rationalCoefficient 512 j.val:ℝ)):ℂ) := by
  unfold gammaCoefficient realGammaPolynomial17
  push_cast
  ring

theorem native_gamma_seventeen_boxes (r : Fin 17) :
    ‖sourceJet r.val nativeGamma -
      Complex.I^r.val*(gammaRealReference17 r:ℂ)‖ ≤
        2*4^r.val/10^34+(1/10^29:ℝ) := by
  let a : Fin 17 → ℝ := fun j => rationalCoefficient 512 j.val
  let b : Fin 17 → ℝ := fun j => coefficientReference17 j
  have hab : ∀ j, |a j-b j| ≤ (1/10^45:ℝ) := by
    intro j
    simpa only [a, b, Rat.cast_sub, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_one] using rat_abs_cast_le (rational_coefficient_boxes17 j)
  have ha : ∀ j, |a j| ≤ (4:ℝ)^(j.val+2) := by
    intro j
    have hbr : |b j| ≤ (4:ℝ)^(j.val+1) := by
      simpa [b] using coefficient_reference17_abs_bound j
    have he : |a j| ≤ |a j-b j|+|b j| := by
      calc
        |a j| = |(a j-b j)+b j| := by congr 1; ring
        _ ≤ |a j-b j|+|b j| := abs_add_le _ _
    have htiny : |a j-b j| ≤ 1 := (hab j).trans (by norm_num)
    have hbig : 1 ≤ (4:ℝ)^(j.val+1) := by
      calc
        1 = (1:ℝ)^(j.val+1) := by simp
        _ ≤ (4:ℝ)^(j.val+1) :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc
      |a j| ≤ |a j-b j|+|b j| := he
      _ ≤ 1+(4:ℝ)^(j.val+1) := add_le_add htiny hbr
      _ ≤ (4:ℝ)^(j.val+2) := by
        have heq : (4:ℝ)^(j.val+2) = 4*(4:ℝ)^(j.val+1) := by
          rw [show j.val+2=(j.val+1)+1 by omega, pow_succ]
          ring
        rw [heq]
        linarith [hbig]
  have hU : |(logReferenceTight:ℝ)| ≤ 2 := by
    norm_num [logReferenceTight]
  have hL : |Real.log 3| ≤ 2 := by
    have h := (abs_sub_abs_le_abs_sub (Real.log 3)
      (logReferenceTight:ℝ)).trans log_three_tight_box
    norm_num [logReferenceTight] at h ⊢
    linarith
  have hp := real_gamma_polynomial_error17 r (Real.log 3) logReferenceTight
    (1/10^44) (1/10^45) (by positivity) (by positivity) hL hU
    log_three_tight_box a b ha hab
  have hr : |realGammaPolynomial17 r logReferenceTight b-
      (gammaRealReference17 r:ℝ)| = 0 := by
    have he : (gammaRationalPolynomial17 r:ℝ) =
        realGammaPolynomial17 r logReferenceTight b := by
      unfold gammaRationalPolynomial17 realGammaPolynomial17
      push_cast
      rfl
    rw [← he]
    simp [gammaRealReference17]
  have hb := (abs_sub_le (realGammaPolynomial17 r (Real.log 3) a)
      (realGammaPolynomial17 r logReferenceTight b)
      (gammaRealReference17 r:ℝ)).trans
    (add_le_add hp (by rw [hr]))
  have hfinite : ‖sourceJet r.val finiteNativeGamma -
      Complex.I^r.val*(gammaRealReference17 r:ℂ)‖ ≤
        24*(r.val+1:ℝ)*(r.val:ℝ)*4^r.val*(1/10^44)+
          3*(r.val+1:ℝ)*4^r.val*(1/10^45) := by
    rw [finite_native_gamma_coefficient, gamma_coefficient_real17,
      ← mul_sub, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
    have hc : (gammaRealReference17 r:ℂ) =
        ((gammaRealReference17 r:ℝ):ℂ) := by simp
    rw [hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa using hb
  have ht := (norm_sub_le_norm_sub_add_norm_sub (sourceJet r.val nativeGamma)
      (sourceJet r.val finiteNativeGamma)
      (Complex.I^r.val*(gammaRealReference17 r:ℂ))).trans
    (add_le_add (native_gamma_jet_error_tight r.val) hfinite)
  have hpow : (4:ℝ)^r.val ≤ 4^16 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ 2*4^r.val/10^34 +
        (24*(r.val+1:ℝ)*(r.val:ℝ)*4^r.val*(1/10^44)+
          3*(r.val+1:ℝ)*4^r.val*(1/10^45)) := ht
    _ ≤ 2*4^r.val/10^34+(1/10^29:ℝ) := by
      have he : 2*(4:ℝ)^r.val/10^34 ≤ 2*4^16/10^34 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
          (by positivity)
      have hrNat : r.val ≤ 16 := by omega
      have hr : (r.val:ℝ) ≤ 16 := by exact_mod_cast hrNat
      have hr1 : (r.val:ℝ)+1 ≤ 17 := by exact_mod_cast (show r.val+1 ≤ 17 by omega)
      have hr1nonneg : 0 ≤ (r.val:ℝ)+1 := by linarith [hr]
      have hprod : (r.val:ℝ)*((r.val:ℝ)+1) ≤ 16*17 :=
        mul_le_mul hr hr1 hr1nonneg (by norm_num)
      have hprodPow : (r.val:ℝ)*((r.val:ℝ)+1)*(4:ℝ)^r.val ≤ 16*17*4^16 :=
        mul_le_mul hprod hpow (by positivity) (by positivity)
      have hlog : 24*(r.val:ℝ)*((r.val:ℝ)+1)*(4:ℝ)^r.val*(1/10^44) ≤ 1/10^30 := by
        have hlogCoeff : 24*(r.val:ℝ)*((r.val:ℝ)+1)*(4:ℝ)^r.val ≤
            24*(16*17*4^16) := by
          calc
            _ = 24*((r.val:ℝ)*((r.val:ℝ)+1)*(4:ℝ)^r.val) := by ring
            _ ≤ 24*(16*17*4^16) :=
              mul_le_mul_of_nonneg_left hprodPow (by norm_num)
        calc
          _ ≤ 24*(16*17*4^16)*(1/10^44) :=
            mul_le_mul_of_nonneg_right hlogCoeff (by positivity)
          _ ≤ 1/10^30 := by norm_num
      have hcoeff : 3*((r.val:ℝ)+1)*(4:ℝ)^r.val*(1/10^45) ≤ 1/10^30 := by
        have hcoeffBase : ((r.val:ℝ)+1)*(4:ℝ)^r.val ≤ 17*4^16 :=
          mul_le_mul hr1 hpow (by norm_num) (by positivity)
        have hcoeffScale : 3*((r.val:ℝ)+1)*(4:ℝ)^r.val ≤ 3*(17*4^16) := by
          calc
            _ = 3*(((r.val:ℝ)+1)*(4:ℝ)^r.val) := by ring
            _ ≤ 3*(17*4^16) := mul_le_mul_of_nonneg_left hcoeffBase (by norm_num)
        calc
          _ ≤ 3*(17*4^16)*(1/10^45) :=
            mul_le_mul_of_nonneg_right hcoeffScale (by positivity)
          _ ≤ 1/10^30 := by norm_num
      norm_num at he ⊢
      nlinarith [he, hlog, hcoeff]

#print axioms rational_coefficient_high_boxes
#print axioms gamma_rational_reference_eq17
#print axioms real_gamma_polynomial_error17
#print axioms native_gamma_seventeen_boxes

end
end CarryC3Gamma
