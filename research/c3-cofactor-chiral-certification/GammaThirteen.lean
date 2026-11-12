import C3Head48Boxes
import GammaCoefficients

namespace CarryC3Gamma
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024

/-- A tight rational approximation to the existing 256-term logarithm series. -/
def logReferenceTight : ℚ :=
  109861228866810969139524523692252570464749055781632 / 10^50

theorem log_approx_tight_box :
    |logApprox-logReferenceTight| ≤ (1/10^50:ℚ) := by
  decide +kernel

theorem log_three_tight_box :
    |Real.log 3-(logReferenceTight:ℝ)| ≤ (1/10^44:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (by norm_num : |(2/3:ℝ)|<1) 256
  have he : Real.log (1-(2/3:ℝ)) = -Real.log 3 := by
    rw [show 1-(2/3:ℝ)=(3:ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he] at h
  have hh : |(logApprox:ℝ)-Real.log 3| ≤
      (2/3:ℝ)^257/(1-2/3) := by
    simpa [logApprox, sub_eq_add_neg,
      abs_of_pos (by norm_num : (0:ℝ)<2/3)] using h
  have hr : |(logApprox:ℝ)-(logReferenceTight:ℝ)| ≤
      (1/10^50:ℝ) := by
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_one] using rat_abs_cast_le log_approx_tight_box
  have hb := (abs_sub_le (Real.log 3) (logApprox:ℝ)
      (logReferenceTight:ℝ)).trans (add_le_add
        (by simpa only [abs_sub_comm] using hh) hr)
  exact hb.trans (by norm_num)

/-- Exact coefficient centers at substantially higher precision than the
older order-six table. -/
def coefficientReference13 : Fin 13 → ℚ := ![
  120853663607396943731022838528922400091716103225871/10^50,
  1041988527117149563658542747502589075012810665546344/10^50,
  5531141957725872182582310757177413563331909885333214/10^50,
  24474417659369116590766667131717327396390507993234748/10^50,
  101127625869758945864859188976956452320235603650526124/10^50,
  408300151938219416454814888267704504676650596234880560/10^50,
  1637167686303465191160170616352205993566427510559642881/10^50,
  6552493551000305123069468322266214785788003868180322553/10^50,
  26213444349175361348997974840310130503005421497041575141/10^50,
  104856796556561120457265552437300301171202119753539633716/10^50,
  419429736728687573381624866636590143155830704903353900515/10^50,
  1677721058968243938756024513745834834760857538830157538615/10^50,
  6710885962045762668996416882947272311527687417966289114320/10^50]

theorem rational_coefficient_boxes13 (j : Fin 13) :
    |rationalCoefficient 512 j.val-coefficientReference13 j| ≤
      (1/10^45:ℚ) := by
  fin_cases j <;> decide +kernel

theorem coefficient_reference13_bound (j : Fin 13) :
    |coefficientReference13 j| ≤ 70000000 := by
  fin_cases j <;> norm_num [coefficientReference13]

def gammaRealReference13 : Fin 13 → ℚ := ![
  3625609908221908311930685155868/10^30,
  -7663548708578351816482000641792/10^30,
  15893174888761976498431297787137/10^30,
  -31949239178709777115021631561743/10^30,
  63980293192093008229847809417608/10^30,
  -127991891646420739036521496876470/10^30,
  255996753030634441798291770238580/10^30,
  -511998694734762857622717640413011/10^30,
  1023999477055744244704274637635807/10^30,
  -2047999790572611204888884761616166/10^30,
  4095999916179098072851581597226702/10^30,
  -8191999966459989325428916043124026/10^30,
  16383999986581442855906735687070109/10^30]

def gammaRationalPolynomial13 (r : Fin 13) : ℚ :=
  3*∑ j ∈ Finset.range (r.val+1),
    (2*logReferenceTight)^j/(j.factorial:ℚ)*(-1/2:ℚ)^(r.val-j)*
      coefficientReference13 ⟨r.val-j, by omega⟩

theorem gamma_rational_boxes13 (r : Fin 13) :
    |gammaRationalPolynomial13 r-gammaRealReference13 r| ≤
      (1/10^25:ℚ) := by
  fin_cases r <;> decide +kernel

def realGammaPolynomial13 (r : Fin 13) (L : ℝ)
    (a : Fin 13 → ℝ) : ℝ :=
  3*∑ j ∈ Finset.range (r.val+1),
    (2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*a ⟨r.val-j, by omega⟩

theorem real_gamma_polynomial_error13 (r : Fin 13) (L U eL eA : ℝ)
    (heL : 0 ≤ eL) (heA : 0 ≤ eA) (hL : |L| ≤ 2) (hU : |U| ≤ 2)
    (hLU : |L-U| ≤ eL) (a b : Fin 13 → ℝ)
    (ha : ∀ j, |a j| ≤ 70000001)
    (hab : ∀ j, |a j-b j| ≤ eA) :
    |realGammaPolynomial13 r L a-realGammaPolynomial13 r U b| ≤
      10^18*eL+10^10*eA := by
  have hsmall (j : ℕ) (hj : j ≤ 12) :
      |(2*L)^j-(2*U)^j| ≤ 110000000*eL := by
    have hm : max |2*L| |2*U| ≤ 4 := by
      apply max_le
      · simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
          (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ)≤2)).trans_eq
            (show (2:ℝ)*2=4 by norm_num)
      · simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
          (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤2)).trans_eq
            (show (2:ℝ)*2=4 by norm_num)
    have hp : max |2*L| |2*U| ^ (j-1) ≤ (4:ℝ)^11 := by
      apply (pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hm _).trans
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hd : |2*L-2*U| ≤ 2*eL := by
      rw [← mul_sub, abs_mul]
      norm_num
      linarith
    have h := abs_pow_sub_pow_le (a:=2*L) (b:=2*U) (n:=j)
    calc
      _ ≤ (2*eL)*j*4^11 := h.trans (mul_le_mul
        (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg j)) hp
        (pow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _) (by positivity))
      _ ≤ 110000000*eL := by
        have hjr : (j:ℝ) ≤ 12 := by exact_mod_cast hj
        norm_num
        nlinarith
  have ht (j : ℕ) (hj : j ∈ Finset.range (r.val+1)) :
      |(2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*
          a ⟨r.val-j,by omega⟩ -
       (2*U)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*
          b ⟨r.val-j,by omega⟩| ≤
      7701000000000000*eL+17000000*eA := by
    have hj12 : j ≤ 12 := by have := Finset.mem_range.mp hj; omega
    let d : Fin 13 := ⟨r.val-j, by omega⟩
    have hp : |(2*U)^j| ≤ 16777216 := by
      rw [abs_pow]
      calc
        |2*U|^j ≤ (4:ℝ)^j := by
          gcongr
          simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
            (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤2)).trans_eq
              (show (2:ℝ)*2=4 by norm_num)
        _ ≤ 4^12 := pow_le_pow_right₀ (by norm_num) hj12
        _ = 16777216 := by norm_num
    have hc : |(-1/2:ℝ)^(r.val-j)/(j.factorial:ℝ)| ≤ 1 := by
      rw [abs_div, abs_pow]
      norm_num only [abs_of_nonneg (show (0:ℝ)≤j.factorial by positivity),
        abs_neg, abs_div, abs_one, abs_of_pos (show (0:ℝ)<2 by norm_num)]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<j.factorial)).2
      have hf : (1:ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
      exact (pow_le_one₀ (by norm_num) (by norm_num)).trans (by simpa using hf)
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
      _ ≤ (110000000*eL)*70000001+16777216*eA := add_le_add
        (mul_le_mul (hsmall j hj12) (ha d) (abs_nonneg _) (by positivity))
        (mul_le_mul hp (hab d) (abs_nonneg _) (by norm_num))
      _ ≤ 7701000000000000*eL+17000000*eA := by nlinarith
  unfold realGammaPolynomial13
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<3),
    ← Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (by norm_num : (0:ℝ)≤3)).trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ht)
    (by norm_num : (0:ℝ)≤3)).trans
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hr : (r.val+1:ℝ) ≤ 13 := by
    exact_mod_cast (show r.val+1 ≤ 13 by omega)
  norm_num
  nlinarith

theorem gamma_coefficient_real13 (r : Fin 13) :
    gammaCoefficient r.val (Real.log 3) = Complex.I^r.val*
      (realGammaPolynomial13 r (Real.log 3)
        (fun j => (rationalCoefficient 512 j.val:ℝ)):ℂ) := by
  unfold gammaCoefficient realGammaPolynomial13
  push_cast
  ring

theorem native_gamma_thirteen_boxes (r : Fin 13) :
    ‖sourceJet r.val nativeGamma -
      Complex.I^r.val*(gammaRealReference13 r:ℂ)‖ ≤ (1/10^24:ℝ) := by
  let a : Fin 13 → ℝ := fun j => rationalCoefficient 512 j.val
  let b : Fin 13 → ℝ := fun j => coefficientReference13 j
  have hab : ∀ j, |a j-b j| ≤ (1/10^45:ℝ) := by
    intro j
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_one] using rat_abs_cast_le (rational_coefficient_boxes13 j)
  have ha : ∀ j, |a j| ≤ 70000001 := by
    intro j
    have hb : |b j| ≤ (70000000:ℝ) := by
      simpa only [Rat.cast_ofNat] using
        rat_abs_cast_le (coefficient_reference13_bound j)
    have h := (abs_sub_abs_le_abs_sub (a j) (b j)).trans (hab j)
    have he : (1/10^45:ℝ) < 1 := by norm_num
    norm_num at h
    nlinarith
  have hU : |(logReferenceTight:ℝ)| ≤ 2 := by
    norm_num [logReferenceTight]
  have hL : |Real.log 3| ≤ 2 := by
    have h := (abs_sub_abs_le_abs_sub (Real.log 3)
      (logReferenceTight:ℝ)).trans log_three_tight_box
    norm_num [logReferenceTight] at h ⊢
    linarith
  have hp := real_gamma_polynomial_error13 r (Real.log 3) logReferenceTight
    (1/10^44) (1/10^45) (by positivity) (by positivity) hL hU
    log_three_tight_box a b ha hab
  have hr : |realGammaPolynomial13 r logReferenceTight b-
      (gammaRealReference13 r:ℝ)| ≤ (1/10^25:ℝ) := by
    have he : (gammaRationalPolynomial13 r:ℝ) =
        realGammaPolynomial13 r logReferenceTight b := by
      unfold gammaRationalPolynomial13 realGammaPolynomial13
      push_cast
      rfl
    rw [← he]
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_one] using rat_abs_cast_le (gamma_rational_boxes13 r)
  have hb := (abs_sub_le (realGammaPolynomial13 r (Real.log 3) a)
      (realGammaPolynomial13 r logReferenceTight b)
      (gammaRealReference13 r:ℝ)).trans (add_le_add hp hr)
  have hfinite : ‖sourceJet r.val finiteNativeGamma -
      Complex.I^r.val*(gammaRealReference13 r:ℂ)‖ ≤
        10^18*(1/10^44)+10^10*(1/10^45)+(1/10^25:ℝ) := by
    rw [finite_native_gamma_coefficient, gamma_coefficient_real13,
      ← mul_sub, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
    have hc : (gammaRealReference13 r:ℂ) =
        ((gammaRealReference13 r:ℝ):ℂ) := by simp
    rw [hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hb
  have ht := (norm_sub_le_norm_sub_add_norm_sub (sourceJet r.val nativeGamma)
      (sourceJet r.val finiteNativeGamma)
      (Complex.I^r.val*(gammaRealReference13 r:ℂ))).trans
    (add_le_add (native_gamma_jet_error r.val) hfinite)
  have hpow : (4:ℝ)^r.val ≤ 4^12 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ 4^r.val/10^32 +
        (10^18*(1/10^44)+10^10*(1/10^45)+(1/10^25:ℝ)) := ht
    _ ≤ (1/10^24:ℝ) := by
      have he : (4:ℝ)^r.val/10^32 ≤ 4^12/10^32 :=
        div_le_div_of_nonneg_right hpow (by positivity)
      norm_num at he ⊢
      nlinarith

#print axioms rational_coefficient_boxes13
#print axioms log_three_tight_box
#print axioms gamma_rational_boxes13
#print axioms native_gamma_thirteen_boxes

end
end CarryC3Gamma
