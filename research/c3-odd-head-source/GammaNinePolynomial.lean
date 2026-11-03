import LogGammaData
import GammaExtendedRationals

namespace CarryOddHeadSource
open CarryC3Gamma
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def realGammaPolynomial9 (r : Fin 9) (L : ℝ) (a : Fin 9 → ℝ) : ℝ :=
  3*∑ j ∈ Finset.range (r.val+1), (2*L)^j/(j.factorial:ℝ)*
    (-1/2:ℝ)^(r.val-j)*a ⟨r.val-j,by omega⟩

theorem real_gamma_polynomial_error9 (r : Fin 9) (L U eL eA : ℝ)
    (heL : 0 ≤ eL) (heA : 0 ≤ eA) (hL : |L| ≤ 2) (hU : |U| ≤ 2) (hLU : |L-U| ≤ eL)
    (a b : Fin 9 → ℝ) (ha : ∀ j, |a j| ≤ 300000)
    (hab : ∀ j, |a j-b j| ≤ eA) :
    |realGammaPolynomial9 r L a-realGammaPolynomial9 r U b| ≤ 10^13*eL + 10^7*eA := by
  have hsmall (j : ℕ) (hj : j ≤ 8) : |(2*L)^j-(2*U)^j| ≤ 1048576*eL := by
    have hm : max |2*L| |2*U| ≤ 4 := by
      apply max_le
      · simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using
          (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ)≤2)).trans_eq (show (2:ℝ)*2=4 by norm_num)
      · simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using
          (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤2)).trans_eq (show (2:ℝ)*2=4 by norm_num)
    have hp : max |2*L| |2*U| ^ (j-1) ≤ (4:ℝ)^8 := by
      apply (pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hm _).trans
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hd : |2*L-2*U| ≤ 2*eL := by
      rw [← mul_sub,abs_mul]
      norm_num
      linarith
    have h := abs_pow_sub_pow_le (a:=2*L) (b:=2*U) (n:=j)
    calc
      _ ≤ (2*eL)*j*4^8 := h.trans (mul_le_mul
        (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg j)) hp
        (pow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _) (by positivity))
      _ ≤ 1048576*eL := by
        have hjr : (j:ℝ) ≤ 8 := by exact_mod_cast hj
        norm_num
        nlinarith
  have ht (j : ℕ) (hj : j ∈ Finset.range (r.val+1)) :
      |(2*L)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*a ⟨r.val-j,by omega⟩-
       (2*U)^j/(j.factorial:ℝ)*(-1/2:ℝ)^(r.val-j)*b ⟨r.val-j,by omega⟩| ≤
      (315000000000*eL + 65536*eA) := by
    have hj8 : j ≤ 8 := by have := Finset.mem_range.mp hj; omega
    let d : Fin 9 := ⟨r.val-j,by omega⟩
    have hp : |(2*U)^j| ≤ 65536 := by
      rw [abs_pow]
      calc
        |2*U|^j ≤ (4:ℝ)^j := by
          gcongr
          simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using
            (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤2)).trans_eq (show (2:ℝ)*2=4 by norm_num)
        _ ≤ 4^8 := pow_le_pow_right₀ (by norm_num) hj8
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
      _ ≤ (1048576*eL)*300000+65536*eA := add_le_add
        (mul_le_mul (hsmall j hj8) (ha d) (abs_nonneg _) (by positivity))
        (mul_le_mul hp (hab d) (abs_nonneg _) (by norm_num))
      _ ≤ (315000000000*eL + 65536*eA) := by nlinarith
  unfold realGammaPolynomial9
  rw [← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),← Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num : (0:ℝ)≤3)).trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ht) (by norm_num : (0:ℝ)≤3)).trans
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hr : (r.val+1:ℝ) ≤ 9 := by exact_mod_cast (show r.val+1 ≤ 9 by omega)
  norm_num
  nlinarith


end
end CarryOddHeadSource
