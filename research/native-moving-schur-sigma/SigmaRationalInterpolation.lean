import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.PSeries

/-!
# Exact rational interpolation for the finite C2 coefficient problem

This module establishes the algebraic interpolation identity used by the
129-node route.  It proves that the degree-zero scaled weight sum is exactly
one.  Bounds for the positive-degree weights, a complex analytic bound for the
source, and inclusion in the source coefficient boxes remain open.
-/

namespace CarrySigmaObstruction

open Finset Polynomial

noncomputable section

def c5InterpolationIndices : Finset ℕ := Finset.range 129

def c5InterpolationNode (j : ℕ) : ℚ := (j : ℚ) ^ 2

theorem c5InterpolationNode_injOn :
    Set.InjOn c5InterpolationNode (↑c5InterpolationIndices : Set ℕ) := by
  intro i _ j _ hij
  have hsq : i ^ 2 = j ^ 2 := by
    dsimp [c5InterpolationNode] at hij
    exact_mod_cast hij
  exact (Nat.pow_left_strictMono (by decide : 2 ≠ 0)).injective hsq

def c5LagrangeBasis (j : ℕ) : Polynomial ℚ :=
  Lagrange.basis c5InterpolationIndices c5InterpolationNode j

def c5InterpolationPolynomial (f : ℕ → ℚ) : Polynomial ℚ :=
  Lagrange.interpolate c5InterpolationIndices c5InterpolationNode f

def c5InterpolationWeight (j n : ℕ) : ℚ :=
  (100000 : ℚ) ^ (2 * n) * (c5LagrangeBasis j).coeff n

def c5InterpolationWeightSum (n : ℕ) : ℚ :=
  ∑ j ∈ c5InterpolationIndices, |c5InterpolationWeight j n|

theorem c5BasisDivisor_coeff_zero (x y : ℚ) :
    (Lagrange.basisDivisor x y).coeff 0 = -((x - y)⁻¹ * y) := by
  rw [Lagrange.basisDivisor, Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  simp

theorem c5BasisDivisor_eval_zero (x y : ℚ) :
    (Lagrange.basisDivisor x y).eval 0 = -((x - y)⁻¹ * y) := by
  simp [Lagrange.basisDivisor]

theorem c5BasisDivisor_derivative_eval_zero (x y : ℚ) :
    (Lagrange.basisDivisor x y).derivative.eval 0 = (x - y)⁻¹ := by
  simp [Lagrange.basisDivisor]

theorem c5Coeff_one_eq_derivative_eval_zero (p : Polynomial ℚ) :
    p.coeff 1 = p.derivative.eval 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  simp

theorem c5LagrangeBasis_derivative_eval_zero (j : ℕ) :
    (c5LagrangeBasis j).derivative.eval 0 =
      ∑ k ∈ c5InterpolationIndices.erase j,
        (∏ l ∈ (c5InterpolationIndices.erase j).erase k,
          -((c5InterpolationNode j - c5InterpolationNode l)⁻¹ *
            c5InterpolationNode l)) *
          (c5InterpolationNode j - c5InterpolationNode k)⁻¹ := by
  rw [c5LagrangeBasis, Lagrange.basis, Polynomial.derivative_prod_finset]
  simp [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
    c5BasisDivisor_eval_zero, c5BasisDivisor_derivative_eval_zero]

theorem c5LagrangeBasis_coeff_one (j : ℕ) :
    (c5LagrangeBasis j).coeff 1 =
      (c5LagrangeBasis j).derivative.eval 0 :=
  c5Coeff_one_eq_derivative_eval_zero _

theorem c5LagrangeBasis_coeff_one_zero :
    (c5LagrangeBasis 0).coeff 1 =
      -∑ k ∈ c5InterpolationIndices.erase 0,
        (c5InterpolationNode k)⁻¹ := by
  rw [c5LagrangeBasis_coeff_one, c5LagrangeBasis_derivative_eval_zero]
  have hprod (x : ℕ) :
      ∏ l ∈ (Finset.range 129).erase 0 |>.erase x,
        ((l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2 = 1 := by
    apply Finset.prod_eq_one
    intro l hl
    have hl0 : l ≠ 0 := (Finset.mem_erase.mp ((Finset.mem_erase.mp hl).2)).1
    have hlq : ((l : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hl0)
    field_simp
  simp [c5InterpolationIndices, c5InterpolationNode, hprod]

theorem c5LagrangeBasis_coeff_one_of_ne {j : ℕ} (hj : j ≠ 0) :
    (c5LagrangeBasis j).coeff 1 =
      (∏ l ∈ (c5InterpolationIndices.erase j).erase 0,
        -((c5InterpolationNode j - c5InterpolationNode l)⁻¹ *
          c5InterpolationNode l)) *
        (c5InterpolationNode j - c5InterpolationNode 0)⁻¹ := by
  rw [c5LagrangeBasis_coeff_one, c5LagrangeBasis_derivative_eval_zero]
  apply Finset.sum_eq_single 0
  · intro k hk hk0
    have hzero : 0 ∈ (c5InterpolationIndices.erase j).erase k := by
      refine Finset.mem_erase.mpr ⟨Ne.symm hk0, ?_⟩
      exact Finset.mem_erase.mpr ⟨Ne.symm hj, by simp [c5InterpolationIndices]⟩
    have hfactor :
        ∏ l ∈ (c5InterpolationIndices.erase j).erase k,
          -((c5InterpolationNode j - c5InterpolationNode l)⁻¹ *
            c5InterpolationNode l) = 0 := by
      apply Finset.prod_eq_zero (i := 0) hzero
      simp [c5InterpolationNode]
    rw [hfactor]
    simp [c5InterpolationNode]
  · intro hnot
    have hmem : 0 ∈ c5InterpolationIndices.erase j :=
      Finset.mem_erase.mpr ⟨Ne.symm hj, by simp [c5InterpolationIndices]⟩
    exact False.elim (hnot hmem)

private theorem c5_abs_sub_range_erase (j : ℕ) (hj : j ≤ 128) :
    (∏ k ∈ (Finset.range 129).erase j, |(j : ℚ) - (k : ℚ)|) =
      (j.factorial : ℚ) * ((128 - j).factorial : ℚ) := by
  have hunion : (Finset.range 129).erase j =
      Finset.range j ∪ Finset.Ioc j 128 := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ioc]
    omega
  have hdisjoint : Disjoint (Finset.range j) (Finset.Ioc j 128) := by
    apply Finset.disjoint_left.mpr
    intro k hk₁ hk₂
    simp only [Finset.mem_range] at hk₁
    simp only [Finset.mem_Ioc] at hk₂
    omega
  rw [hunion, Finset.prod_union hdisjoint]
  have hleft :
      (∏ k ∈ Finset.range j, |(j : ℚ) - (k : ℚ)|) = (j.factorial : ℚ) := by
    calc
      (∏ k ∈ Finset.range j, |(j : ℚ) - (k : ℚ)|) =
          ∏ k ∈ Finset.range j, (((j - 1 - k + 1 : ℕ) : ℚ)) := by
            apply Finset.prod_congr rfl
            intro k hk
            have hklt : k < j := Finset.mem_range.mp hk
            rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hklt.le))]
            rw [← Nat.cast_sub hklt.le]
            have hnat : j - k = j - 1 - k + 1 := by omega
            exact_mod_cast hnat
      _ = ∏ k ∈ Finset.range j, ((k + 1 : ℕ) : ℚ) := by
            simpa [Nat.cast_add, Nat.cast_one] using
              (Finset.prod_range_reflect (fun i : ℕ => ((i + 1 : ℕ) : ℚ)) j)
      _ = (j.factorial : ℚ) := by
            exact_mod_cast Finset.prod_range_add_one_eq_factorial j
  have hright :
      (∏ k ∈ Finset.Ioc j 128, |(j : ℚ) - (k : ℚ)|) =
        ((128 - j).factorial : ℚ) := by
    have hioc : Finset.Ioc j 128 = Finset.Ico (j + 1) 129 := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hioc, Finset.prod_Ico_eq_prod_range]
    have hlen : 129 - (j + 1) = 128 - j := by omega
    rw [hlen]
    calc
      (∏ k ∈ Finset.range (128 - j),
          |(j : ℚ) - ((j + 1 + k : ℕ) : ℚ)|) =
          ∏ k ∈ Finset.range (128 - j), ((k + 1 : ℕ) : ℚ) := by
            apply Finset.prod_congr rfl
            intro k hk
            have hcalc : (j : ℚ) - ((j + 1 + k : ℕ) : ℚ) =
                -((k + 1 : ℕ) : ℚ) := by
              push_cast
              ring
            rw [hcalc, abs_neg, abs_of_nonneg (by positivity)]
      _ = ((128 - j).factorial : ℚ) := by
            exact_mod_cast Finset.prod_range_add_one_eq_factorial (128 - j)
  rw [hleft, hright]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem c5_nat_shifted_product (j : ℕ) (hj : 1 ≤ j) :
    Nat.factorial (j - 1) *
      Finset.prod (Finset.range 129) (fun k : ℕ => j + k) =
      Nat.factorial (j + 128) := by
  have hlength : j + 128 = (j - 1) + 129 := by omega
  have hfac := Nat.factorial_eq_prod_range_add_one (j + 128)
  rw [hlength, Finset.prod_range_add] at hfac
  have hfirst :
      Finset.prod (Finset.range (j - 1)) (fun k : ℕ => k + 1) =
        Nat.factorial (j - 1) := by
    exact Finset.prod_range_add_one_eq_factorial (j - 1)
  have hfun : (fun k : ℕ => (j - 1) + k + 1) = fun k => j + k := by
    funext k
    omega
  rw [hfirst, hfun] at hfac
  rw [← hlength] at hfac
  exact hfac.symm

private theorem c5_factorial_center_product_le (j : ℕ) (hj : j ≤ 128) :
    Nat.factorial 128 * Nat.factorial 128 ≤
      Nat.factorial (128 - j) * Nat.factorial (128 + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjlt : j < 128 := by omega
      have hleft : Nat.factorial (128 - j) =
          (128 - j) * Nat.factorial (127 - j) := by
        have harg : 128 - j = (127 - j) + 1 := by omega
        rw [harg, Nat.factorial_succ]
      have hright : Nat.factorial (129 + j) =
          (129 + j) * Nat.factorial (128 + j) := by
        have harg : 129 + j = (128 + j) + 1 := by omega
        simpa only [harg] using (Nat.factorial_succ (128 + j))
      have hstep : Nat.factorial (128 - j) * Nat.factorial (128 + j) ≤
          Nat.factorial (127 - j) * Nat.factorial (129 + j) := by
        rw [hleft, hright]
        have hcoef : 128 - j ≤ 129 + j := by omega
        calc
          ((128 - j) * Nat.factorial (127 - j)) * Nat.factorial (128 + j) =
              (Nat.factorial (127 - j) * Nat.factorial (128 + j)) * (128 - j) := by ring
          _ ≤ (Nat.factorial (127 - j) * Nat.factorial (128 + j)) * (129 + j) :=
            Nat.mul_le_mul_left _ hcoef
          _ = Nat.factorial (127 - j) * ((129 + j) * Nat.factorial (128 + j)) := by ring
      rw [show 128 - (j + 1) = 127 - j by omega,
        show 128 + (j + 1) = 129 + j by omega]
      exact (ih (by omega)).trans hstep

private theorem c5_inv_sq_sum_range_le (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n, ((k + 1 : ℚ) ^ 2)⁻¹) ≤
      2 := by
  have hsum :
      (∑ k ∈ Finset.range n, ((k + 1 : ℚ) ^ 2)⁻¹) =
        1 + ∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℚ) ^ 2)⁻¹ := by
    have hIco :
        (∑ k ∈ Finset.range n, ((k + 1 : ℚ) ^ 2)⁻¹) =
          ∑ i ∈ Finset.Ico 1 (n + 1), ((i : ℚ) ^ 2)⁻¹ := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm]
    have hset : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ioo 1 (n + 1)) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Ioo]
      omega
    rw [hIco, hset, Finset.sum_insert]
    · norm_num
    · simp
  rw [hsum]
  have htail := sum_Ioo_inv_sq_le (α := ℚ) 1 (n + 1)
  have htail' :
      (∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℚ) ^ 2)⁻¹) ≤ 1 := by
    norm_num at htail
    simpa using htail
  calc
    1 + ∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℚ) ^ 2)⁻¹ =
        (∑ i ∈ Finset.Ioo 1 (n + 1), ((i : ℚ) ^ 2)⁻¹) + 1 := by ring
    _ ≤ 1 + 1 := add_le_add_left htail' (1 : ℚ)
    _ = 2 := by norm_num

private theorem c5_rat_shifted_product (j : ℕ) (hj : 1 ≤ j) :
    (Nat.factorial (j - 1) : ℚ) *
        Finset.prod (Finset.range 129) (fun k : ℕ => (j : ℚ) + (k : ℚ)) =
      (Nat.factorial (j + 128) : ℚ) := by
  have hNat := c5_nat_shifted_product j hj
  have hCast := congrArg (fun n : ℕ => (n : ℚ)) hNat
  simpa only [Nat.cast_mul, Nat.cast_prod, Nat.cast_add] using hCast

set_option maxRecDepth 10000 in
private theorem c5_shifted_product_erase (j : ℕ) (hj : 1 ≤ j)
    (hj128 : j ≤ 128) :
    (Nat.factorial (j - 1) : ℚ) *
        (Finset.prod ((Finset.range 129).erase j)
          (fun k : ℕ => (j : ℚ) + (k : ℚ)) *
          (2 * (j : ℚ))) =
      (Nat.factorial (j + 128) : ℚ) := by
  have hfull : (Nat.factorial (j - 1) : ℚ) *
      Finset.prod (Finset.range 129) (fun k : ℕ => (j : ℚ) + (k : ℚ)) =
        (Nat.factorial (j + 128) : ℚ) := by
    exact c5_rat_shifted_product j hj
  have hjmem : j ∈ Finset.range 129 := Finset.mem_range.mpr (by omega)
  have herase := Finset.prod_erase_mul (Finset.range 129)
    (fun k : ℕ => ((j + k : ℕ) : ℚ)) hjmem
  have herase' :
      Finset.prod ((Finset.range 129).erase j)
          (fun k : ℕ => (j : ℚ) + (k : ℚ)) * (2 * (j : ℚ)) =
        Finset.prod (Finset.range 129)
          (fun k : ℕ => (j : ℚ) + (k : ℚ)) := by
    simpa only [Nat.cast_add, two_mul] using herase
  rw [herase']
  exact hfull

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem c5_abs_square_difference_product (j : ℕ) (hj : 1 ≤ j)
    (hj128 : j ≤ 128) :
    (∏ k ∈ (Finset.range 129).erase j,
      |(j : ℚ) ^ 2 - (k : ℚ) ^ 2|) * 2 =
        (Nat.factorial (128 - j) : ℚ) *
          (Nat.factorial (128 + j) : ℚ) := by
  have hsplit :
      Finset.prod ((Finset.range 129).erase j)
          (fun k : ℕ => |(j : ℚ) ^ 2 - (k : ℚ) ^ 2|) =
      Finset.prod ((Finset.range 129).erase j)
          (fun k : ℕ => |(j : ℚ) - (k : ℚ)|) *
        Finset.prod ((Finset.range 129).erase j)
          (fun k : ℕ => (j : ℚ) + (k : ℚ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    have hdiff : (j : ℚ) ^ 2 - (k : ℚ) ^ 2 =
        ((j : ℚ) - (k : ℚ)) * ((j : ℚ) + (k : ℚ)) := by ring
    have hjq : (0 : ℚ) ≤ (j : ℚ) := by positivity
    have hkq : (0 : ℚ) ≤ (k : ℚ) := by positivity
    rw [hdiff, abs_mul]
    rw [abs_of_nonneg (add_nonneg hjq hkq)]
  rw [hsplit, c5_abs_sub_range_erase j hj128]
  have hfactj : (Nat.factorial j : ℚ) =
      (j : ℚ) * (Nat.factorial (j - 1) : ℚ) := by
    have harg : (j - 1) + 1 = j := by omega
    have h := Nat.factorial_succ (j - 1)
    rw [harg] at h
    exact_mod_cast h
  have hshift := c5_shifted_product_erase j hj hj128
  calc
    ((Nat.factorial j : ℚ) * (Nat.factorial (128 - j) : ℚ) *
        Finset.prod ((Finset.range 129).erase j)
          (fun k : ℕ => (j : ℚ) + (k : ℚ))) * 2 =
      (Nat.factorial (128 - j) : ℚ) *
        ((Nat.factorial (j - 1) : ℚ) *
          (Finset.prod ((Finset.range 129).erase j)
            (fun k : ℕ => (j : ℚ) + (k : ℚ)) *
            (2 * (j : ℚ)))) := by rw [hfactj]; ring
    _ = (Nat.factorial (128 - j) : ℚ) *
        (Nat.factorial (j + 128) : ℚ) := by rw [hshift]
    _ = (Nat.factorial (128 - j) : ℚ) *
        (Nat.factorial (128 + j) : ℚ) := by congr 1 <;> omega

private theorem c5_nonzero_square_product (j : ℕ) (hj : 1 ≤ j)
    (hj128 : j ≤ 128) :
    (∏ l ∈ ((Finset.range 129).erase j).erase 0, (l : ℚ) ^ 2) *
        (j : ℚ) ^ 2 = (Nat.factorial 128 : ℚ) ^ 2 := by
  have hset : (Finset.range 129).erase 0 = Finset.Ico 1 129 := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  have hbase :
      (∏ l ∈ (Finset.range 129).erase 0, (l : ℚ) ^ 2) =
        (Nat.factorial 128 : ℚ) ^ 2 := by
    rw [hset, Finset.prod_Ico_eq_prod_range]
    simp only [Nat.reduceSub]
    rw [Finset.prod_pow]
    have hprod :
        (∏ k ∈ Finset.range 128, ((1 + k : ℕ) : ℚ)) =
          (Nat.factorial 128 : ℚ) := by
      calc
        (∏ k ∈ Finset.range 128, ((1 + k : ℕ) : ℚ)) =
            ∏ k ∈ Finset.range 128, ((k + 1 : ℕ) : ℚ) := by
              apply Finset.prod_congr rfl
              intro k hk
              congr 1
              omega
        _ = (Nat.factorial 128 : ℚ) := by
              exact_mod_cast Finset.prod_range_add_one_eq_factorial 128
    rw [hprod]
  have hsets : ((Finset.range 129).erase j).erase 0 =
      ((Finset.range 129).erase 0).erase j := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  have hjmem : j ∈ (Finset.range 129).erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  calc
    (∏ l ∈ ((Finset.range 129).erase j).erase 0, (l : ℚ) ^ 2) *
        (j : ℚ) ^ 2 =
      (∏ l ∈ ((Finset.range 129).erase 0).erase j, (l : ℚ) ^ 2) *
        (j : ℚ) ^ 2 := by rw [hsets]
    _ = ∏ l ∈ (Finset.range 129).erase 0, (l : ℚ) ^ 2 := by
      exact Finset.prod_erase_mul ((Finset.range 129).erase 0)
        (fun l : ℕ => (l : ℚ) ^ 2) hjmem
    _ = (Nat.factorial 128 : ℚ) ^ 2 := hbase

theorem c5LagrangeBasisProductCoeffOne_bound :
    ∀ j : Fin 129, j.val ≠ 0 →
      |(∏ l ∈ (c5InterpolationIndices.erase j.val).erase 0,
          -((c5InterpolationNode j.val - c5InterpolationNode l)⁻¹ *
            c5InterpolationNode l)) *
        (c5InterpolationNode j.val - c5InterpolationNode 0)⁻¹| ≤
        (2 : ℚ) / (j.val : ℚ) ^ 2 := by
  intro j hj0
  let n : ℕ := j.val
  let q : ℚ := (n : ℚ) ^ 2
  let T : Finset ℕ := (Finset.range 129).erase n
  let S : Finset ℕ := T.erase 0
  let num : ℚ := ∏ l ∈ S, (l : ℚ) ^ 2
  let denSmall : ℚ := ∏ k ∈ S, |q - (k : ℚ) ^ 2|
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hj0
  have hn128 : n ≤ 128 := by dsimp [n]; omega
  have hqpos : 0 < q := by dsimp [q]; positivity
  have h0mem : 0 ∈ T := by
    apply Finset.mem_erase.mpr
    constructor
    · exact Ne.symm (Nat.ne_of_gt hn)
    · exact Finset.mem_range.mpr (by dsimp [n]; omega)
  have hdenErase :
      (∏ k ∈ T, |q - (k : ℚ) ^ 2|) = denSmall * q := by
    have herase := Finset.prod_erase_mul T
      (fun k : ℕ => |q - (k : ℚ) ^ 2|) h0mem
    simpa [S, denSmall, abs_of_pos hqpos] using herase.symm
  have hnum : num * q = (Nat.factorial 128 : ℚ) ^ 2 := by
    simpa [num, S, T, q] using c5_nonzero_square_product n hn hn128
  have hden :
      (∏ k ∈ T, |q - (k : ℚ) ^ 2|) * 2 =
        (Nat.factorial (128 - n) : ℚ) *
          (Nat.factorial (128 + n) : ℚ) := by
    simpa [T, q] using c5_abs_square_difference_product n hn hn128
  have hcenterNat := c5_factorial_center_product_le n hn128
  have hcenterMul :
      (Nat.factorial 128 : ℚ) * (Nat.factorial 128 : ℚ) ≤
        (Nat.factorial (128 - n) : ℚ) *
          (Nat.factorial (128 + n) : ℚ) := by
    exact_mod_cast hcenterNat
  have hcenter : (Nat.factorial 128 : ℚ) ^ 2 ≤
      (Nat.factorial (128 - n) : ℚ) *
        (Nat.factorial (128 + n) : ℚ) := by
    simpa only [pow_two] using hcenterMul
  have hfacScaled : num * q ≤ 2 * denSmall * q := by
    calc
      num * q = (Nat.factorial 128 : ℚ) ^ 2 := hnum
      _ ≤ (Nat.factorial (128 - n) : ℚ) *
          (Nat.factorial (128 + n) : ℚ) := hcenter
      _ = (∏ k ∈ T, |q - (k : ℚ) ^ 2|) * 2 := hden.symm
      _ = 2 * denSmall * q := by rw [hdenErase]; ring
  have hnumLe : num ≤ 2 * denSmall := by
    exact (mul_le_mul_right hqpos).mp hfacScaled
  have hdenFullPos : 0 < ∏ k ∈ T, |q - (k : ℚ) ^ 2| := by
    have hfacPos :
        0 < (Nat.factorial (128 - n) : ℚ) *
          (Nat.factorial (128 + n) : ℚ) := by positivity
    have hprodPos :
        0 < (∏ k ∈ T, |q - (k : ℚ) ^ 2|) * 2 := by
      rw [hden]
      exact hfacPos
    norm_num at hprodPos ⊢
    nlinarith
  have hdenSmallPos : 0 < denSmall := by
    rw [hdenErase] at hdenFullPos
    by_contra hnot
    have hle : denSmall ≤ 0 := le_of_not_gt hnot
    have hnonpos : denSmall * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hqpos.le
    linarith
  have hcoefTerm (l : ℕ) (hl : l ∈ S) :
      | -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)| *
          |q - (l : ℚ) ^ 2| = (l : ℚ) ^ 2 := by
    have hln : l ≠ n := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    have hdiff : q - (l : ℚ) ^ 2 ≠ 0 := by
      intro heq
      have hsqQ : (n : ℚ) ^ 2 = (l : ℚ) ^ 2 := by
        dsimp [q] at heq
        linarith
      have hsqN : n ^ 2 = l ^ 2 := by exact_mod_cast hsqQ
      have hEq : n = l :=
        (Nat.pow_left_strictMono (by decide : 2 ≠ 0)).injective hsqN
      exact hln hEq.symm
    have habs : |q - (l : ℚ) ^ 2| ≠ 0 := abs_ne_zero.mpr hdiff
    rw [abs_neg, abs_mul, abs_inv,
      abs_of_nonneg (sq_nonneg (l : ℚ))]
    calc
      (|q - (l : ℚ) ^ 2|⁻¹ * (l : ℚ) ^ 2) *
          |q - (l : ℚ) ^ 2| =
        (|q - (l : ℚ) ^ 2|⁻¹ * |q - (l : ℚ) ^ 2|) *
          (l : ℚ) ^ 2 := by ring
      _ = (l : ℚ) ^ 2 := by rw [inv_mul_cancel₀ habs, one_mul]
  have hprodTerm :
      (∏ l ∈ S, | -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)|) * denSmall = num := by
    calc
      (∏ l ∈ S, | -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)|) *
          (∏ l ∈ S, |q - (l : ℚ) ^ 2|) =
        ∏ l ∈ S,
          (| -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)| *
            |q - (l : ℚ) ^ 2|) := by rw [← Finset.prod_mul_distrib]
      _ = num := by
        calc
          (∏ l ∈ S,
              (| -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)| *
                |q - (l : ℚ) ^ 2|)) =
              ∏ l ∈ S, (l : ℚ) ^ 2 := by
                apply Finset.prod_congr rfl
                intro l hl
                exact hcoefTerm l hl
          _ = num := by rfl
  have hcoeffIdentity :
      |(∏ l ∈ S,
          -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)) * q⁻¹| * q * denSmall = num := by
    rw [abs_mul, Finset.abs_prod, abs_of_pos (inv_pos.mpr hqpos)]
    calc
      (∏ l ∈ S, | -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)|) * q⁻¹ *
          q * denSmall =
        ((∏ l ∈ S, | -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)|) * denSmall) *
          (q⁻¹ * q) := by ring
      _ = num := by rw [hprodTerm, inv_mul_cancel₀ (ne_of_gt hqpos), mul_one]
  have hscaled :
      |(∏ l ∈ S,
          -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)) * q⁻¹| * q * denSmall ≤
        2 * denSmall := by rw [hcoeffIdentity]; exact hnumLe
  have habsq :
      |(∏ l ∈ S,
          -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)) * q⁻¹| * q ≤ 2 := by
    exact (mul_le_mul_right hdenSmallPos).mp hscaled
  have hbound := (le_div_iff₀ hqpos).2 habsq
  simpa [S, T, q, n, c5InterpolationIndices, c5InterpolationNode] using hbound

theorem c5LagrangeBasis_coeff_one_zero_abs_le :
    |(c5LagrangeBasis 0).coeff 1| ≤ 2 := by
  rw [c5LagrangeBasis_coeff_one_zero]
  have hset : (Finset.range 129).erase 0 = Finset.Ico 1 129 := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  have hsum :
      (∑ k ∈ (Finset.range 129).erase 0, ((k : ℚ) ^ 2)⁻¹) =
        ∑ k ∈ Finset.range 128, ((k + 1 : ℚ) ^ 2)⁻¹ := by
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.reduceSub, Nat.cast_add, Nat.cast_one, add_comm]
  rw [hsum, abs_neg]
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range 128, ((k + 1 : ℚ) ^ 2)⁻¹ := by
    apply Finset.sum_nonneg
    intro k hk
    exact inv_nonneg.mpr (sq_nonneg _)
  rw [abs_of_nonneg hnonneg]
  have htel := c5_inv_sq_sum_range_le 128 (by omega)
  linarith

theorem c5LagrangeBasis_coeff_one_abs_le (j : ℕ) (hj : j < 129) :
    |(c5LagrangeBasis j).coeff 1| ≤
      if j = 0 then 2 else (2 : ℚ) / (j : ℚ) ^ 2 := by
  by_cases hj0 : j = 0
  · subst j
    simpa using c5LagrangeBasis_coeff_one_zero_abs_le
  · rw [if_neg hj0, c5LagrangeBasis_coeff_one_of_ne hj0]
    have h := c5LagrangeBasisProductCoeffOne_bound ⟨j, hj⟩ hj0
    simpa [c5InterpolationIndices, c5InterpolationNode] using h

theorem c5InterpolationCoeffOneAbsSum_le_six :
    (∑ j ∈ c5InterpolationIndices,
      |(c5LagrangeBasis j).coeff 1|) ≤ 6 := by
  calc
    (∑ j ∈ c5InterpolationIndices,
        |(c5LagrangeBasis j).coeff 1|) ≤
      ∑ j ∈ c5InterpolationIndices,
        (if j = 0 then (2 : ℚ) else 2 / (j : ℚ) ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          exact c5LagrangeBasis_coeff_one_abs_le j (Finset.mem_range.mp hj)
    _ ≤ 6 := by
      let f : ℕ → ℚ := fun j =>
        if j = 0 then 2 else 2 / (j : ℚ) ^ 2
      change (∑ j ∈ Finset.range 129,
        if j = 0 then 2 else 2 / (j : ℚ) ^ 2) ≤ 6
      have h0 : 0 ∈ Finset.range 129 := Finset.mem_range.mpr (by omega)
      rw [← Finset.sum_erase_add (Finset.range 129) f h0]
      have hset : (Finset.range 129).erase 0 = Finset.Ico 1 129 := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
        omega
      have hsum :
          (∑ j ∈ (Finset.range 129).erase 0, f j) ≤ 4 := by
        rw [hset, Finset.sum_Ico_eq_sum_range]
        simp [Nat.reduceSub, f, Nat.cast_add, Nat.cast_one]
        have htel := c5_inv_sq_sum_range_le 128 (by omega)
        have hsumEq :
            (∑ k ∈ Finset.range 128, 2 / ((k + 1 : ℚ) ^ 2)) =
              2 * ∑ k ∈ Finset.range 128, ((k + 1 : ℚ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        rw [hsumEq]
        linarith
      rw [← Finset.sum_erase_add (Finset.range 129) f h0]
      have hf0 : f 0 = 2 := by simp [f]
      rw [hf0]
      linarith

theorem c5InterpolationWeightSum_one_lt_ten_eleven :
    c5InterpolationWeightSum 1 < 10 ^ 11 := by
  unfold c5InterpolationWeightSum
  simp only [c5InterpolationWeight, Nat.mul_one]
  rw [show (100000 : ℚ) ^ 2 = 10 ^ 10 by norm_num]
  simp_rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (10 ^ 10 : ℚ))]
  rw [← Finset.mul_sum]
  calc
    (10 ^ 10 : ℚ) *
        (∑ j ∈ c5InterpolationIndices,
          |(c5LagrangeBasis j).coeff 1|) ≤ 10 ^ 10 * 6 := by
            exact mul_le_mul_of_nonneg_left c5InterpolationCoeffOneAbsSum_le_six
              (by norm_num)
    _ < 10 ^ 11 := by norm_num

theorem c5LagrangeBasis_coeff_zero (j : ℕ) :
    (c5LagrangeBasis j).coeff 0 =
      ∏ k ∈ c5InterpolationIndices.erase j,
        -((c5InterpolationNode j - c5InterpolationNode k)⁻¹ *
          c5InterpolationNode k) := by
  simp [c5LagrangeBasis, Lagrange.basis, c5InterpolationIndices,
    Polynomial.coeff_zero_prod, c5BasisDivisor_coeff_zero]

theorem c5LagrangeBasis_coeff_zero_of_ne {j : ℕ} (hj : j ≠ 0) :
    (c5LagrangeBasis j).coeff 0 = 0 := by
  rw [c5LagrangeBasis_coeff_zero]
  refine Finset.prod_eq_zero (i := 0) ?_ ?_
  · exact Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_range.mpr (by norm_num)⟩
  · simp [c5InterpolationNode]

theorem c5LagrangeBasis_zero_coeff_zero :
    (c5LagrangeBasis 0).coeff 0 = 1 := by
  rw [c5LagrangeBasis_coeff_zero]
  apply Finset.prod_eq_one
  intro k hk
  have hkne : k ≠ 0 := (Finset.mem_erase.mp hk).1
  have hksq : ((k : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hkne)
  simp only [c5InterpolationNode, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0)]
  field_simp [hksq]
  ring

theorem c5InterpolationWeightSum_zero_eq_one :
    c5InterpolationWeightSum 0 = 1 := by
  rw [c5InterpolationWeightSum, ← Finset.sum_erase_add _ _
    (show 0 ∈ c5InterpolationIndices by simp [c5InterpolationIndices])]
  have hzero : c5InterpolationWeight 0 0 = 1 := by
    simp [c5InterpolationWeight, c5LagrangeBasis_zero_coeff_zero]
  have hrest : (∑ j ∈ c5InterpolationIndices.erase 0,
      |c5InterpolationWeight j 0|) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjne : j ≠ 0 := (Finset.mem_erase.mp hj).1
    simp [c5InterpolationWeight, c5LagrangeBasis_coeff_zero_of_ne hjne]
  rw [hrest, zero_add, hzero, abs_one]

theorem c5InterpolationPolynomial_coeff (f : ℕ → ℚ) (n : ℕ) :
    (c5InterpolationPolynomial f).coeff n =
      ∑ j ∈ c5InterpolationIndices,
        f j * (c5LagrangeBasis j).coeff n := by
  simp [c5InterpolationPolynomial, c5LagrangeBasis, Lagrange.interpolate_apply,
    Polynomial.coeff_C_mul]

theorem c5_interpolate_polynomial (p : Polynomial ℚ) (hp : p.degree < 129) :
    c5InterpolationPolynomial (fun j => p.eval (c5InterpolationNode j)) = p := by
  unfold c5InterpolationPolynomial
  symm
  apply Lagrange.eq_interpolate c5InterpolationNode_injOn
  simpa [c5InterpolationIndices] using hp

theorem c5InterpolationPolynomial_coeff_of_degree_lt
    (p : Polynomial ℚ) (hp : p.degree < 129) (n : ℕ) :
    p.coeff n =
      ∑ j ∈ c5InterpolationIndices,
        p.eval (c5InterpolationNode j) * (c5LagrangeBasis j).coeff n := by
  calc
    p.coeff n = (c5InterpolationPolynomial (fun j => p.eval (c5InterpolationNode j))).coeff n := by
      rw [c5_interpolate_polynomial p hp]
    _ = ∑ j ∈ c5InterpolationIndices,
          p.eval (c5InterpolationNode j) * (c5LagrangeBasis j).coeff n :=
      c5InterpolationPolynomial_coeff _ _

end
end CarrySigmaObstruction
