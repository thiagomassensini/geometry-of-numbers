import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Algebraic core for central C2 Hankel minors

This module is independent of the zero model.  It defines only the finite ten-scale comparison
sequence and generic consecutive 2×2 determinants; the original C2 jets are introduced later,
through explicit hypotheses about their decomposition.
-/

namespace CarrySigmaCentral

open scoped BigOperators

/-- The consecutive central Hankel minor of an arbitrary real sequence. -/
def hankel2 (H : ℕ → ℝ) (s : ℕ) : ℝ :=
  H s * H (s + 2) - H (s + 1) ^ 2

/-- The finite power sum for any finite family of real scales. -/
def finitePowerMoment {N : ℕ} (a : Fin N → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin N, (a i) ^ (n + 1)

/-- The ten-mode power sum used only as an algebraic comparison sequence. -/
def tenModeMoment (a : Fin 10 → ℝ) (n : ℕ) : ℝ := finitePowerMoment a n

/-- One unordered-pair contribution to the finite moment determinant. -/
def pairTerm (x y : ℝ) (s : ℕ) : ℝ :=
  (x * y) ^ (s + 1) * (x - y) ^ 2

/-- Sum over the ordered index presentation `i < j` of unordered pairs. -/
def pairMoment {N : ℕ} (a : Fin N → ℝ) (s : ℕ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then pairTerm (a i) (a j) s else 0

/-- The algebraic identity holds for every finite number of real scales. -/
theorem pairTerm_expand (x y : ℝ) (s : ℕ) :
    pairTerm x y s = y ^ (s + 1) * x ^ (s + 3) +
      x ^ (s + 1) * y ^ (s + 3) - 2 * y ^ (s + 2) * x ^ (s + 2) := by
  rw [pairTerm, mul_pow]
  have hx : x ^ (s + 3) = x ^ (s + 1) * x ^ 2 := by
    rw [show s + 3 = (s + 1) + 2 by omega, pow_add]
  have hy : y ^ (s + 3) = y ^ (s + 1) * y ^ 2 := by
    rw [show s + 3 = (s + 1) + 2 by omega, pow_add]
  have hx' : x ^ (s + 2) = x ^ (s + 1) * x := by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_add, pow_one]
  have hy' : y ^ (s + 2) = y ^ (s + 1) * y := by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_add, pow_one]
  rw [hx, hy, hx', hy']
  ring

/-- The cross terms introduced by adjoining one scale are exactly its pair contributions with
the existing scales. -/
theorem pairTerm_sum_expand {N : ℕ} (a : Fin N → ℝ) (x : ℝ) (s : ℕ) :
    (∑ i : Fin N, pairTerm x (a i) s) =
      finitePowerMoment a s * x ^ (s + 3) +
        x ^ (s + 1) * finitePowerMoment a (s + 2) -
          2 * finitePowerMoment a (s + 1) * x ^ (s + 2) := by
  calc
    (∑ i : Fin N, pairTerm x (a i) s) =
        ∑ i : Fin N,
          ((a i) ^ (s + 1) * x ^ (s + 3) +
            x ^ (s + 1) * (a i) ^ (s + 3) -
              2 * (a i) ^ (s + 2) * x ^ (s + 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pairTerm_expand x (a i) s
    _ = finitePowerMoment a s * x ^ (s + 3) +
          x ^ (s + 1) * finitePowerMoment a (s + 2) -
            2 * finitePowerMoment a (s + 1) * x ^ (s + 2) := by
      have h1 : (∑ i : Fin N, (a i) ^ (s + 1)) * x ^ (s + 3) =
          finitePowerMoment a s * x ^ (s + 3) := rfl
      have h2 : x ^ (s + 1) * (∑ i : Fin N, (a i) ^ (s + 3)) =
          x ^ (s + 1) * finitePowerMoment a (s + 2) := by
        simp [finitePowerMoment, show s + 3 = (s + 2) + 1 by omega]
      have h3 : 2 * (∑ i : Fin N, (a i) ^ (s + 2)) * x ^ (s + 2) =
          2 * finitePowerMoment a (s + 1) * x ^ (s + 2) := by
        simp [finitePowerMoment, show s + 2 = (s + 1) + 1 by omega]
      have hsum1 : (∑ i : Fin N, (a i) ^ (s + 1) * x ^ (s + 3)) =
          (∑ i : Fin N, (a i) ^ (s + 1)) * x ^ (s + 3) := by
        exact (Finset.sum_mul Finset.univ _ _).symm
      have hsum2 : (∑ i : Fin N, x ^ (s + 1) * (a i) ^ (s + 3)) =
          x ^ (s + 1) * (∑ i : Fin N, (a i) ^ (s + 3)) := by
        exact (Finset.mul_sum Finset.univ _ _).symm
      have hsum3 : (∑ i : Fin N, 2 * (a i) ^ (s + 2) * x ^ (s + 2)) =
          2 * (∑ i : Fin N, (a i) ^ (s + 2)) * x ^ (s + 2) := by
        calc
          _ = (∑ i : Fin N, 2 * (a i) ^ (s + 2)) * x ^ (s + 2) := by
            exact (Finset.sum_mul Finset.univ _ _).symm
          _ = 2 * (∑ i : Fin N, (a i) ^ (s + 2)) * x ^ (s + 2) := by
            rw [← Finset.mul_sum]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hsum1, hsum2, hsum3, h1, h2, h3]

/-- Finite power-sum moments have the Vandermonde-pair determinant identity. -/
theorem finiteMoment_hankel2_eq_pairMoment {N : ℕ} (a : Fin N → ℝ) (s : ℕ) :
    hankel2 (fun n => ∑ i : Fin N, (a i) ^ (n + 1)) s = pairMoment a s := by
  induction N generalizing s with
  | zero => simp [hankel2, pairMoment]
  | succ N ih =>
      let tail : Fin N → ℝ := fun i => a i.succ
      have hmoment (n : ℕ) :
          (∑ i : Fin (N + 1), (a i) ^ (n + 1)) =
            a 0 ^ (n + 1) + ∑ i : Fin N, (tail i) ^ (n + 1) := by
        simp [Fin.sum_univ_succ, tail]
      have hpair : pairMoment a s =
          (∑ i : Fin N, pairTerm (a 0) (tail i) s) + pairMoment tail s := by
        simp [pairMoment, Fin.sum_univ_succ, tail]
      have htail0 : finitePowerMoment tail s =
          ∑ i : Fin N, tail i * tail i ^ s := by
        unfold finitePowerMoment
        simp_rw [show s + 1 = 1 + s by omega, pow_add, pow_one]
      have htail1 : finitePowerMoment tail (s + 1) =
          ∑ i : Fin N, tail i ^ 2 * tail i ^ s := by
        unfold finitePowerMoment
        simp_rw [show (s + 1) + 1 = 2 + s by omega, pow_add]
      have htail2 : finitePowerMoment tail (s + 2) =
          ∑ i : Fin N, tail i ^ 3 * tail i ^ s := by
        unfold finitePowerMoment
        simp_rw [show (s + 2) + 1 = 3 + s by omega, pow_add]
      have hdet :
          hankel2 (fun n => ∑ i : Fin (N + 1), (a i) ^ (n + 1)) s =
            hankel2 (fun n => ∑ i : Fin N, (tail i) ^ (n + 1)) s +
              ∑ i : Fin N, pairTerm (a 0) (tail i) s := by
        simp only [hankel2, hmoment s, hmoment (s + 2), hmoment (s + 1)]
        rw [pairTerm_sum_expand, htail2, htail1, htail0]
        simp_rw [show s + 3 = 3 + s by omega,
          show s + 2 = 2 + s by omega,
          show s + 1 = 1 + s by omega, pow_add, pow_one]
        ring
      calc
        hankel2 (fun n => ∑ i : Fin (N + 1), (a i) ^ (n + 1)) s =
            hankel2 (fun n => ∑ i : Fin N, (tail i) ^ (n + 1)) s +
              ∑ i : Fin N, pairTerm (a 0) (tail i) s := hdet
        _ = pairMoment tail s + ∑ i : Fin N, pairTerm (a 0) (tail i) s := by
          rw [ih tail s]
        _ = pairMoment a s := by rw [hpair]; ring

/-- Expanding a perturbation of both rows of a consecutive 2×2 determinant gives all five
mixed and quadratic terms. -/
theorem hankel2_add_error_expansion (P e : ℕ → ℝ) (s : ℕ) :
    hankel2 (fun n => P n + e n) s - hankel2 P s =
      P s * e (s + 2) + e s * P (s + 2) -
        2 * P (s + 1) * e (s + 1) +
        e s * e (s + 2) - e (s + 1) ^ 2 := by
  simp only [hankel2]
  ring

/-- The five signed summands in the determinant perturbation identity. -/
def determinantErrorTerm (P e : ℕ → ℝ) (s : ℕ) : Fin 5 → ℝ
  | 0 => P s * e (s + 2)
  | 1 => e s * P (s + 2)
  | 2 => -2 * P (s + 1) * e (s + 1)
  | 3 => e s * e (s + 2)
  | 4 => -(e (s + 1) ^ 2)

/-- Positive majorants for the five summands when `P_n ≤ 10 A^(n+1)` and
`|e_n| ≤ 60 η^(n+1)`. -/
def determinantErrorTermBound (A eta : ℝ) (s : ℕ) : Fin 5 → ℝ
  | 0 => 600 * A ^ (s + 1) * eta ^ (s + 3)
  | 1 => 600 * A ^ (s + 3) * eta ^ (s + 1)
  | 2 => 1200 * A ^ (s + 2) * eta ^ (s + 2)
  | 3 => 3600 * eta ^ (s + 1) * eta ^ (s + 3)
  | 4 => 3600 * (eta ^ (s + 2)) ^ 2

/-- The determinant error is bounded by the sum of the five advertised terms. -/
theorem hankel2_error_abs_bound (P e : ℕ → ℝ) (s : ℕ) (A eta : ℝ)
    (hA : 0 ≤ A) (heta : 0 ≤ eta)
    (hPnonneg : ∀ n, 0 ≤ P n)
    (hPbound : ∀ n, P n ≤ 10 * A ^ (n + 1))
    (he : ∀ n, |e n| ≤ 60 * eta ^ (n + 1)) :
    |hankel2 (fun n => P n + e n) s - hankel2 P s| ≤
      600 * (A * eta) ^ (s + 1) * (A + eta) ^ 2 + 7200 * eta ^ (2 * s + 4) := by
  have hterm : ∀ i : Fin 5,
      |determinantErrorTerm P e s i| ≤ determinantErrorTermBound A eta s i := by
    intro i
    fin_cases i
    · simp only [determinantErrorTerm, determinantErrorTermBound]
      rw [abs_mul, abs_of_nonneg (hPnonneg s)]
      calc
        P s * |e (s + 2)| ≤ (10 * A ^ (s + 1)) * (60 * eta ^ (s + 3)) := by
          apply mul_le_mul (hPbound s) (he (s + 2)) (abs_nonneg _) (by positivity)
        _ = 600 * A ^ (s + 1) * eta ^ (s + 3) := by ring
    · simp only [determinantErrorTerm, determinantErrorTermBound]
      rw [abs_mul, abs_of_nonneg (hPnonneg (s + 2)), mul_comm]
      calc
        P (s + 2) * |e s| ≤ (10 * A ^ (s + 3)) * (60 * eta ^ (s + 1)) := by
          apply mul_le_mul (hPbound (s + 2)) (he s) (abs_nonneg _) (by positivity)
        _ = 600 * A ^ (s + 3) * eta ^ (s + 1) := by ring
    · simp only [determinantErrorTerm, determinantErrorTermBound]
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num),
        abs_of_nonneg (hPnonneg (s + 1))]
      calc
        2 * P (s + 1) * |e (s + 1)| =
            2 * (P (s + 1) * |e (s + 1)|) := by ring
        _ ≤ 2 * ((10 * A ^ (s + 2)) * (60 * eta ^ (s + 2))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hPbound (s + 1)) (he (s + 1)) (abs_nonneg _) (by positivity))
            (by norm_num)
        _ = 2 * (10 * A ^ (s + 2)) * (60 * eta ^ (s + 2)) := by ring
        _ = 1200 * A ^ (s + 2) * eta ^ (s + 2) := by ring
    · simp only [determinantErrorTerm, determinantErrorTermBound]
      rw [abs_mul]
      calc
        |e s| * |e (s + 2)| ≤ (60 * eta ^ (s + 1)) * (60 * eta ^ (s + 3)) := by
          exact mul_le_mul (he s) (he (s + 2)) (abs_nonneg _) (by positivity)
        _ = 3600 * eta ^ (s + 1) * eta ^ (s + 3) := by ring
    · simp only [determinantErrorTerm, determinantErrorTermBound]
      rw [abs_neg, abs_sq]
      have he' : |e (s + 1)| ≤ 60 * eta ^ (s + 2) := he (s + 1)
      have hsquare : e (s + 1) ^ 2 ≤ (60 * eta ^ (s + 2)) ^ 2 := by
        simpa only [sq_abs] using
          ((sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 60 * eta ^ (s + 2))).2 he')
      calc
        e (s + 1) ^ 2 ≤ (60 * eta ^ (s + 2)) ^ 2 := hsquare
        _ = 3600 * (eta ^ (s + 2)) ^ 2 := by ring
  have hsum :
      hankel2 (fun n => P n + e n) s - hankel2 P s =
        ∑ i : Fin 5, determinantErrorTerm P e s i := by
    rw [hankel2_add_error_expansion]
    simp [determinantErrorTerm, Fin.sum_univ_succ]
    ring
  calc
    |hankel2 (fun n => P n + e n) s - hankel2 P s| =
        |∑ i : Fin 5, determinantErrorTerm P e s i| := by rw [hsum]
    _ ≤ ∑ i : Fin 5, |determinantErrorTerm P e s i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 5, determinantErrorTermBound A eta s i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i
    _ = 600 * (A * eta) ^ (s + 1) * (A + eta) ^ 2 +
        7200 * eta ^ (2 * s + 4) := by
      simp [determinantErrorTermBound, Fin.sum_univ_succ,
        show s + 3 = (s + 1) + 2 by omega,
        show s + 2 = (s + 1) + 1 by omega,
        show 2 * s + 4 = (s + 1) + (s + 3) by omega,
        pow_add, mul_pow]
      ring

/-- A positive scale has positive finite power-sum moments. -/
theorem tenModeMoment_pos (a : Fin 10 → ℝ) (n : ℕ)
    (ha : ∀ i, 0 < a i) :
    0 < tenModeMoment a n := by
  unfold tenModeMoment finitePowerMoment
  apply Finset.sum_pos
  · intro i hi
    exact pow_pos (ha i) _
  · simp

/-- Uniform upper bound on a ten-mode moment. -/
theorem tenModeMoment_le (a : Fin 10 → ℝ) (n : ℕ) (A : ℝ)
    (haNonneg : ∀ i, 0 ≤ a i) (ha : ∀ i, a i ≤ A) :
    tenModeMoment a n ≤ 10 * A ^ (n + 1) := by
  unfold tenModeMoment finitePowerMoment
  calc
    (∑ i : Fin 10, a i ^ (n + 1)) ≤ ∑ _i : Fin 10, A ^ (n + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (haNonneg i) (ha i) _
    _ = 10 * A ^ (n + 1) := by simp

/-- Coordinatewise ordered nonnegative scales induce ordered finite power sums. -/
theorem tenModeMoment_mono (a b : Fin 10 → ℝ) (n : ℕ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    tenModeMoment a n ≤ tenModeMoment b n := by
  unfold tenModeMoment finitePowerMoment
  apply Finset.sum_le_sum
  intro i hi
  exact pow_le_pow_left₀ (ha i) (hab i) _

/-- Vandermonde-pair formula specialized to ten modes. -/
theorem tenModeMoment_hankel2_eq_pairMoment (a : Fin 10 → ℝ) (s : ℕ) :
    hankel2 (tenModeMoment a) s = pairMoment a s := by
  exact finiteMoment_hankel2_eq_pairMoment a s

/-- All unordered-pair summands are nonnegative for nonnegative scales. -/
theorem pairMoment_nonneg (a : Fin 10 → ℝ) (s : ℕ)
    (ha : ∀ i, 0 ≤ a i) : 0 ≤ pairMoment a s := by
  unfold pairMoment
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs with hij
  · exact mul_nonneg (pow_nonneg (mul_nonneg (ha i) (ha j)) _)
      (sq_nonneg (a i - a j))
  · exact le_rfl

/-- The pair `(0,1)` is included in the unordered-pair sum. -/
theorem pairTerm_01_le_pairMoment (a : Fin 10 → ℝ) (s : ℕ)
    (hterm : ∀ i j, 0 ≤ pairTerm (a i) (a j) s) :
    pairTerm (a 0) (a 1) s ≤ pairMoment a s := by
  unfold pairMoment
  have hinner : pairTerm (a 0) (a 1) s ≤
      ∑ j : Fin 10, if (0 : Fin 10) < j then pairTerm (a 0) (a j) s else 0 := by
    have hf : ∀ j ∈ (Finset.univ : Finset (Fin 10)),
        0 ≤ if (0 : Fin 10) < j then pairTerm (a 0) (a j) s else 0 := by
      intro j hj
      split_ifs with hjlt
      · exact hterm 0 j
      · exact le_rfl
    have hj : (1 : Fin 10) ∈ (Finset.univ : Finset (Fin 10)) := Finset.mem_univ _
    have hlt : (0 : Fin 10) < (1 : Fin 10) := by norm_num
    simpa [hlt] using (Finset.single_le_sum hf hj)
  have houter :
      (∑ j : Fin 10, if (0 : Fin 10) < j then pairTerm (a 0) (a j) s else 0) ≤
        ∑ i : Fin 10, ∑ j : Fin 10,
          if i < j then pairTerm (a i) (a j) s else 0 := by
    have hf : ∀ i ∈ (Finset.univ : Finset (Fin 10)),
        0 ≤ ∑ j : Fin 10, if i < j then pairTerm (a i) (a j) s else 0 := by
      intro i hi
      apply Finset.sum_nonneg
      intro j hj
      split_ifs with hij
      · exact hterm i j
      · exact le_rfl
    have hi : (0 : Fin 10) ∈ (Finset.univ : Finset (Fin 10)) := Finset.mem_univ _
    simpa using (Finset.single_le_sum hf hi)
  exact le_trans hinner houter

end CarrySigmaCentral
