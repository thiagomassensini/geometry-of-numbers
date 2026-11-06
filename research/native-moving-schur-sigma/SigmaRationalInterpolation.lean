import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.PSeries

/-!
# Exact rational interpolation for the finite C2 coefficient problem

This module establishes the algebraic interpolation identity used by the
129-node route. It proves exact interpolation and a uniform symbolic bound on
the scaled weight sums through degree fourteen. A complex analytic source
bound and inclusion in the source coefficient boxes remain open.
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
        (Nat.factorial (128 + j) : ℚ) := by
          have hargs : j + 128 = 128 + j := by omega
          rw [hargs]

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

/-- The degree-one coefficient of a nonzero-node Lagrange basis is bounded by
twice the reciprocal square of its node index. -/
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
    · exact Finset.mem_range.mpr (by omega)
  have hdenErase :
      (∏ k ∈ T, |q - (k : ℚ) ^ 2|) = denSmall * q := by
    have herase := Finset.prod_erase_mul T
      (fun k : ℕ => |q - (k : ℚ) ^ 2|) h0mem
    simpa [S, denSmall, abs_of_pos hqpos] using herase.symm
  have hnum : num * q = (Nat.factorial 128 : ℚ) ^ 2 := by
    change (∏ l ∈ ((Finset.range 129).erase n).erase 0,
      (l : ℚ) ^ 2) * (n : ℚ) ^ 2 = (Nat.factorial 128 : ℚ) ^ 2
    exact c5_nonzero_square_product n hn hn128
  have hden :
      (∏ k ∈ T, |q - (k : ℚ) ^ 2|) * 2 =
        (Nat.factorial (128 - n) : ℚ) *
          (Nat.factorial (128 + n) : ℚ) := by
    change (∏ k ∈ (Finset.range 129).erase n,
      |(n : ℚ) ^ 2 - (k : ℚ) ^ 2|) * 2 =
        (Nat.factorial (128 - n) : ℚ) * (Nat.factorial (128 + n) : ℚ)
    exact c5_abs_square_difference_product n hn hn128
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
    exact le_of_mul_le_mul_right hfacScaled hqpos
  have hdenFullPos : 0 < ∏ k ∈ T, |q - (k : ℚ) ^ 2| := by
    have hfacPos :
        0 < (Nat.factorial (128 - n) : ℚ) *
          (Nat.factorial (128 + n) : ℚ) := by positivity
    have hprodPos :
        0 < (∏ k ∈ T, |q - (k : ℚ) ^ 2|) * 2 := by
      rw [hden]
      exact hfacPos
    exact (mul_pos_iff_of_pos_right (by norm_num : 0 < (2 : ℚ))).mp hprodPos
  have hdenSmallPos : 0 < denSmall := by
    rw [hdenErase] at hdenFullPos
    by_contra hnot
    have hle : denSmall ≤ 0 := le_of_not_gt hnot
    have hnonpos : denSmall * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hqpos.le
    linarith
  have hcoefTerm (l : ℕ) (hl : l ∈ S) :
      |-((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)| *
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
      (∏ l ∈ S, |-((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)|) * denSmall = num := by
    calc
      (∏ l ∈ S, |-((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)|) *
          (∏ l ∈ S, |q - (l : ℚ) ^ 2|) =
        ∏ l ∈ S,
          (|-((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)| *
            |q - (l : ℚ) ^ 2|) := by rw [← Finset.prod_mul_distrib]
      _ = num := by
        calc
          (∏ l ∈ S,
              (|-((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)| *
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
      (∏ l ∈ S, |-((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)|) * q⁻¹ *
          q * denSmall =
        ((∏ l ∈ S, |-((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)|) * denSmall) *
          (q⁻¹ * q) := by ring
      _ = num := by rw [hprodTerm, inv_mul_cancel₀ (ne_of_gt hqpos), mul_one]
  have hscaled :
      |(∏ l ∈ S,
          -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)) * q⁻¹| * q * denSmall ≤
        2 * denSmall := by rw [hcoeffIdentity]; exact hnumLe
  have habsq :
      |(∏ l ∈ S,
          -((q - (l : ℚ) ^ 2)⁻¹ * (l : ℚ) ^ 2)) * q⁻¹| * q ≤ 2 := by
    exact le_of_mul_le_mul_right hscaled hdenSmallPos
  have hbound := (le_div_iff₀ hqpos).2 habsq
  simpa [S, T, q, n, c5InterpolationIndices, c5InterpolationNode] using hbound

theorem c5LagrangeBasis_coeff_one_zero_abs_le :
    |(c5LagrangeBasis 0).coeff 1| ≤ 2 := by
  rw [c5LagrangeBasis_coeff_one_zero]
  simp only [c5InterpolationIndices, c5InterpolationNode]
  have hset : (Finset.range 129).erase 0 = Finset.Ico 1 129 := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  have hsum :
      (∑ k ∈ (Finset.range 129).erase 0, ((k : ℚ) ^ 2)⁻¹) =
        ∑ k ∈ Finset.range 128, ((k + 1 : ℚ) ^ 2)⁻¹ := by
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.cast_add, Nat.cast_one, add_comm]
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

/-- The unscaled absolute degree-one coefficients of all interpolation bases
sum to at most six. -/
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
        simp [f, Nat.cast_add, Nat.cast_one]
        have htel := c5_inv_sq_sum_range_le 128 (by omega)
        have hsumEq :
            (∑ k ∈ Finset.range 128, 2 / (1 + (k : ℚ)) ^ 2) =
              2 * ∑ k ∈ Finset.range 128, ((k + 1 : ℚ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hadd : (1 : ℚ) + (k : ℚ) = (k : ℚ) + 1 := by ring
          rw [hadd, div_eq_mul_inv]
        rw [hsumEq]
        linarith
      have hf0 : f 0 = 2 := by simp [f]
      rw [hf0]
      linarith

/-- The sum of absolute scaled interpolation weights for degree one is below
ten to the eleventh. -/
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

private def c5PositiveLinearFactor (a : ℚ) : Polynomial ℚ :=
  1 - Polynomial.C a * Polynomial.X

private theorem c5_coeff_mul_positiveLinearFactor_zero
    (p : Polynomial ℚ) (a : ℚ) :
    (p * c5PositiveLinearFactor a).coeff 0 = p.coeff 0 := by
  simp [c5PositiveLinearFactor]

private theorem c5_coeff_mul_positiveLinearFactor_succ
    (p : Polynomial ℚ) (a : ℚ) (n : ℕ) :
    (p * c5PositiveLinearFactor a).coeff (n + 1) =
      p.coeff (n + 1) - a * p.coeff n := by
  rw [c5PositiveLinearFactor,
    show p * (1 - Polynomial.C a * Polynomial.X) =
      p - Polynomial.C a * (p * Polynomial.X) by ring]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_X]

/-- Coefficients of a finite product of normalized positive linear factors are
bounded by the corresponding power of the sum of their slopes. -/
private theorem c5_positiveLinearFactor_product_coeff_abs_le_pow_sum
    {α : Type} [DecidableEq α] (s : Finset α) (a : α → ℚ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (n : ℕ) :
    |(∏ i ∈ s, c5PositiveLinearFactor (a i)).coeff n| ≤
      (∑ i ∈ s, a i) ^ n := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
      cases n with
      | zero => simp
      | succ n => simp [c5PositiveLinearFactor, Polynomial.coeff_one]
  | @insert i s hi ih =>
      have hai : 0 ≤ a i := ha i (Finset.mem_insert_self i s)
      have has : ∀ j ∈ s, 0 ≤ a j := fun j hj =>
        ha j (Finset.mem_insert_of_mem hj)
      let P : Polynomial ℚ := ∏ j ∈ s, c5PositiveLinearFactor (a j)
      have hPzero : |P.coeff 0| ≤ (∑ j ∈ s, a j) ^ 0 := by
        have hzero : P.coeff 0 = 1 := by
          simp [P, c5PositiveLinearFactor, Polynomial.coeff_zero_prod]
        rw [hzero]
        simp
      cases n with
      | zero =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi]
          change |(c5PositiveLinearFactor (a i) * P).coeff 0| ≤
            (a i + ∑ j ∈ s, a j) ^ 0
          rw [mul_comm]
          rw [c5_coeff_mul_positiveLinearFactor_zero]
          simpa using hPzero
      | succ n =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi]
          change |(c5PositiveLinearFactor (a i) * P).coeff (n + 1)| ≤
            (a i + ∑ j ∈ s, a j) ^ (n + 1)
          rw [mul_comm]
          rw [c5_coeff_mul_positiveLinearFactor_succ]
          have hSnonneg : 0 ≤ ∑ j ∈ s, a j :=
            Finset.sum_nonneg fun j hj => has j hj
          have hcoeff :
              |P.coeff (n + 1) - a i * P.coeff n| ≤
                (∑ j ∈ s, a j) ^ (n + 1) +
                  a i * (∑ j ∈ s, a j) ^ n := by
            calc
              |P.coeff (n + 1) - a i * P.coeff n| ≤
                  |P.coeff (n + 1)| + |a i * P.coeff n| := abs_sub _ _
              _ ≤ (∑ j ∈ s, a j) ^ (n + 1) +
                    a i * (∑ j ∈ s, a j) ^ n := by
                apply add_le_add
                · simpa [P] using ih has (n + 1)
                · rw [abs_mul, abs_of_nonneg hai]
                  exact mul_le_mul_of_nonneg_left
                    (by simpa [P] using ih has n) hai
          have hpow :
              (∑ j ∈ s, a j) ^ n ≤
                (∑ j ∈ s, a j + a i) ^ n := by
            gcongr
            linarith
          have hscaled :
              (∑ j ∈ s, a j) ^ n *
                  (∑ j ∈ s, a j + a i) ≤
                (∑ j ∈ s, a j + a i) ^ n *
                  (∑ j ∈ s, a j + a i) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
          calc
            |P.coeff (n + 1) - a i * P.coeff n| ≤
                (∑ j ∈ s, a j) ^ (n + 1) +
                  a i * (∑ j ∈ s, a j) ^ n := hcoeff
            _ = (∑ j ∈ s, a j) ^ n *
                  (∑ j ∈ s, a j + a i) := by
                rw [pow_succ]
                ring
            _ ≤ (∑ j ∈ s, a j + a i) ^ n *
                  (∑ j ∈ s, a j + a i) := hscaled
            _ = (∑ j ∈ s, a j + a i) ^ (n + 1) := by rw [pow_succ]
            _ = (a i + ∑ j ∈ s, a j) ^ (n + 1) := by congr 1; ring

private theorem c5_positive_inverse_square_sum_le_two
    (s : Finset ℕ) (hs : s ⊆ (Finset.range 129).erase 0) :
    (∑ k ∈ s, ((k : ℚ) ^ 2)⁻¹) ≤ 2 := by
  have hsumSubset :
      (∑ k ∈ s, ((k : ℚ) ^ 2)⁻¹) ≤
        ∑ k ∈ (Finset.range 129).erase 0, ((k : ℚ) ^ 2)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hs
    intro k hk _
    exact inv_nonneg.mpr (sq_nonneg (k : ℚ))
  have hset : (Finset.range 129).erase 0 = Finset.Ico 1 129 := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  have hsum :
      (∑ k ∈ (Finset.range 129).erase 0, ((k : ℚ) ^ 2)⁻¹) =
        ∑ k ∈ Finset.range 128, ((k + 1 : ℚ) ^ 2)⁻¹ := by
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.cast_add, Nat.cast_one, add_comm]
  rw [hsum] at hsumSubset
  exact hsumSubset.trans (c5_inv_sq_sum_range_le 128 (by omega))

private def c5PositiveInterpolationIndices : Finset ℕ :=
  c5InterpolationIndices.erase 0

private def c5LagrangePositiveTailFactors (j : ℕ) : Finset ℕ :=
  c5PositiveInterpolationIndices.erase j

private theorem c5_basisDivisor_zero_eq_positiveLinearFactor
    (k : ℕ) (hk : k ≠ 0) :
    Lagrange.basisDivisor 0 ((k : ℚ) ^ 2) =
      c5PositiveLinearFactor (((k : ℚ) ^ 2)⁻¹) := by
  have hy : ((k : ℚ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr hk)
  rw [Lagrange.basisDivisor, c5PositiveLinearFactor, zero_sub, inv_neg,
    Polynomial.C_neg]
  have hmul :
      Polynomial.C (((k : ℚ) ^ 2)⁻¹) *
        Polynomial.C ((k : ℚ) ^ 2) = 1 := by
    rw [← Polynomial.C_mul]
    field_simp [hy]
    simp
  rw [mul_sub]
  rw [show -Polynomial.C (((k : ℚ) ^ 2)⁻¹) *
      Polynomial.C ((k : ℚ) ^ 2) = -1 by rw [neg_mul, hmul]]
  ring

private theorem c5_basisDivisor_eq_scalar_mul_positiveLinearFactor
    (j k : ℕ) (hk : k ≠ 0) (hjk : j ≠ k) :
    Lagrange.basisDivisor ((j : ℚ) ^ 2) ((k : ℚ) ^ 2) =
      Polynomial.C (-(((j : ℚ) ^ 2 - (k : ℚ) ^ 2)⁻¹ *
        (k : ℚ) ^ 2)) *
        c5PositiveLinearFactor (((k : ℚ) ^ 2)⁻¹) := by
  have hy : ((k : ℚ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr hk)
  have hxy : (j : ℚ) ^ 2 ≠ (k : ℚ) ^ 2 := by
    intro h
    have hnat : j ^ 2 = k ^ 2 := by exact_mod_cast h
    exact hjk ((Nat.pow_left_strictMono (by decide : 2 ≠ 0)).injective hnat)
  have hdiff : (j : ℚ) ^ 2 - (k : ℚ) ^ 2 ≠ 0 := sub_ne_zero.mpr hxy
  let y : ℚ := (k : ℚ) ^ 2
  let δ : ℚ := (j : ℚ) ^ 2 - (k : ℚ) ^ 2
  have hy' : y ≠ 0 := by simpa [y] using hy
  have hδ : δ ≠ 0 := by simpa [δ] using hdiff
  have hconst :
      Polynomial.C (δ⁻¹) * Polynomial.C y =
        -Polynomial.C (-(δ⁻¹ * y)) := by
    rw [← Polynomial.C_mul, ← Polynomial.C_neg]
    congr 1
    ring
  have hlinear :
      Polynomial.C (-(δ⁻¹ * y)) * Polynomial.C (y⁻¹) =
        -Polynomial.C (δ⁻¹) := by
    rw [← Polynomial.C_mul, ← Polynomial.C_neg]
    congr 1
    field_simp [hy', hδ]
  rw [Lagrange.basisDivisor, c5PositiveLinearFactor]
  change Polynomial.C (δ⁻¹) * (Polynomial.X - Polynomial.C y) =
    Polynomial.C (-(δ⁻¹ * y)) *
      (1 - Polynomial.C (y⁻¹) * Polynomial.X)
  rw [mul_sub, hconst, mul_sub, mul_one, ← mul_assoc, hlinear]
  ring

private theorem c5LagrangeBasis_factorization_zero :
    c5LagrangeBasis 0 =
      ∏ k ∈ c5PositiveInterpolationIndices,
        c5PositiveLinearFactor (((k : ℚ) ^ 2)⁻¹) := by
  rw [c5LagrangeBasis, Lagrange.basis]
  apply Finset.prod_congr rfl
  intro k hk
  exact c5_basisDivisor_zero_eq_positiveLinearFactor k
    (Finset.mem_erase.mp hk).1

private theorem c5LagrangeBasis_factorization_of_ne
    (j : ℕ) (hj0 : j ≠ 0) :
    c5LagrangeBasis j =
      Polynomial.C ((c5LagrangeBasis j).coeff 1) * Polynomial.X *
        ∏ k ∈ c5LagrangePositiveTailFactors j,
          c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := by
  let S : Finset ℕ := c5LagrangePositiveTailFactors j
  let b : ℕ → ℚ := fun k =>
    -((c5InterpolationNode j - c5InterpolationNode k)⁻¹ *
      c5InterpolationNode k)
  let B : ℚ := ∏ k ∈ S, b k
  let A : ℚ := B * (c5InterpolationNode j)⁻¹
  have hsets :
      (c5InterpolationIndices.erase j).erase 0 = S := by
    change ((Finset.range 129).erase j).erase 0 =
      ((Finset.range 129).erase 0).erase j
    ext k
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  have hzero : 0 ∈ c5InterpolationIndices.erase j := by
    apply Finset.mem_erase.mpr
    exact ⟨Ne.symm hj0, Finset.mem_range.mpr (by norm_num)⟩
  have hcoeff : (c5LagrangeBasis j).coeff 1 = A := by
    rw [c5LagrangeBasis_coeff_one_of_ne hj0]
    dsimp [A, B, b]
    rw [hsets]
    simp [c5InterpolationNode]
  have hdecomp :
      c5LagrangeBasis j =
        (∏ k ∈ S,
          Lagrange.basisDivisor (c5InterpolationNode j)
            (c5InterpolationNode k)) *
          Lagrange.basisDivisor (c5InterpolationNode j) 0 := by
    rw [c5LagrangeBasis, Lagrange.basis]
    calc
      (∏ k ∈ c5InterpolationIndices.erase j,
          Lagrange.basisDivisor (c5InterpolationNode j)
            (c5InterpolationNode k)) =
        (∏ k ∈ (c5InterpolationIndices.erase j).erase 0,
          Lagrange.basisDivisor (c5InterpolationNode j)
            (c5InterpolationNode k)) *
          Lagrange.basisDivisor (c5InterpolationNode j) 0 :=
            (Finset.prod_erase_mul (c5InterpolationIndices.erase j)
              (fun k => Lagrange.basisDivisor (c5InterpolationNode j)
                (c5InterpolationNode k)) hzero).symm
      _ = (∏ k ∈ S,
            Lagrange.basisDivisor (c5InterpolationNode j)
              (c5InterpolationNode k)) *
          Lagrange.basisDivisor (c5InterpolationNode j) 0 := by rw [hsets]
  have htail :
      (∏ k ∈ S,
        Lagrange.basisDivisor (c5InterpolationNode j)
          (c5InterpolationNode k)) =
        Polynomial.C B *
          ∏ k ∈ S,
            c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := by
    calc
      (∏ k ∈ S,
        Lagrange.basisDivisor (c5InterpolationNode j)
          (c5InterpolationNode k)) =
        ∏ k ∈ S,
          (Polynomial.C (b k) *
            c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹)) := by
          apply Finset.prod_congr rfl
          intro k hk
          have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
          have hkpos : k ∈ c5PositiveInterpolationIndices :=
            (Finset.mem_erase.mp hk).2
          have hk0 : k ≠ 0 := (Finset.mem_erase.mp hkpos).1
          simpa [c5InterpolationNode, b] using
            c5_basisDivisor_eq_scalar_mul_positiveLinearFactor
              j k hk0 (Ne.symm hkj)
      _ = (∏ k ∈ S, Polynomial.C (b k)) *
          ∏ k ∈ S,
            c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) :=
          Finset.prod_mul_distrib
      _ = Polynomial.C B *
          ∏ k ∈ S,
            c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := by
          rw [← map_prod Polynomial.C b S]
  have hzeroFactor :
      Lagrange.basisDivisor (c5InterpolationNode j) 0 =
        Polynomial.C ((c5InterpolationNode j)⁻¹) * Polynomial.X := by
    simp [Lagrange.basisDivisor, c5InterpolationNode]
  have hraw :
      c5LagrangeBasis j =
        Polynomial.C A * Polynomial.X *
          ∏ k ∈ S,
            c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := by
    calc
      c5LagrangeBasis j =
          (∏ k ∈ S,
            Lagrange.basisDivisor (c5InterpolationNode j)
              (c5InterpolationNode k)) *
            Lagrange.basisDivisor (c5InterpolationNode j) 0 := hdecomp
      _ = (Polynomial.C B *
            ∏ k ∈ S,
              c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹)) *
            (Polynomial.C ((c5InterpolationNode j)⁻¹) *
              Polynomial.X) := by rw [htail, hzeroFactor]
      _ = Polynomial.C A * Polynomial.X *
          ∏ k ∈ S,
            c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := by
          calc
            _ = (Polynomial.C B *
                Polynomial.C ((c5InterpolationNode j)⁻¹)) *
                Polynomial.X *
                ∏ k ∈ S,
                  c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := by ac_rfl
            _ = Polynomial.C
                (B * (c5InterpolationNode j)⁻¹) *
                Polynomial.X *
                ∏ k ∈ S,
                  c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := by
                rw [← Polynomial.C_mul]
            _ = Polynomial.C A * Polynomial.X *
                ∏ k ∈ S,
                  c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := by
                simp [A]
  calc
    c5LagrangeBasis j =
        Polynomial.C A * Polynomial.X *
          ∏ k ∈ S, c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := hraw
    _ = Polynomial.C ((c5LagrangeBasis j).coeff 1) * Polynomial.X *
          ∏ k ∈ S, c5PositiveLinearFactor ((c5InterpolationNode k)⁻¹) := by
        rw [← hcoeff]

private theorem c5LagrangeBasis_zeroIndex_coeff_abs_le_two_pow
    (n : ℕ) :
    |(c5LagrangeBasis 0).coeff n| ≤ 2 ^ n := by
  rw [c5LagrangeBasis_factorization_zero]
  let a : ℕ → ℚ := fun k => ((k : ℚ) ^ 2)⁻¹
  have hprod := c5_positiveLinearFactor_product_coeff_abs_le_pow_sum
    c5PositiveInterpolationIndices a
    (fun k hk => inv_nonneg.mpr (sq_nonneg (k : ℚ))) n
  have hsum :
      (∑ k ∈ c5PositiveInterpolationIndices, a k) ≤ 2 := by
    apply c5_positive_inverse_square_sum_le_two
    exact Finset.Subset.rfl
  have hpow :
      (∑ k ∈ c5PositiveInterpolationIndices, a k) ^ n ≤ 2 ^ n := by
    gcongr
    exact Finset.sum_nonneg fun k hk =>
      inv_nonneg.mpr (sq_nonneg (k : ℚ))
  exact hprod.trans hpow

private theorem c5LagrangeBasis_nonzeroIndex_coeff_abs_le_weight
    (j n : ℕ) (hj : j ≠ 0) (hn : 1 ≤ n) :
    |(c5LagrangeBasis j).coeff n| ≤
      2 ^ (n - 1) * |(c5LagrangeBasis j).coeff 1| := by
  conv_lhs => rw [c5LagrangeBasis_factorization_of_ne j hj]
  let S : Finset ℕ := c5LagrangePositiveTailFactors j
  let a : ℕ → ℚ := fun k => (c5InterpolationNode k)⁻¹
  have hnEq : n = (n - 1) + 1 := by omega
  have hcoeff :
      (Polynomial.C ((c5LagrangeBasis j).coeff 1) * Polynomial.X *
        ∏ k ∈ S, c5PositiveLinearFactor (a k)).coeff n =
      (c5LagrangeBasis j).coeff 1 *
        (∏ k ∈ S, c5PositiveLinearFactor (a k)).coeff (n - 1) := by
    rw [hnEq]
    rw [show Polynomial.C ((c5LagrangeBasis j).coeff 1) * Polynomial.X *
        (∏ k ∈ S, c5PositiveLinearFactor (a k)) =
      Polynomial.C ((c5LagrangeBasis j).coeff 1) *
        (Polynomial.X * ∏ k ∈ S, c5PositiveLinearFactor (a k)) by ring]
    simp
  rw [hcoeff, abs_mul]
  have hprod := c5_positiveLinearFactor_product_coeff_abs_le_pow_sum
    S a (fun k hk => inv_nonneg.mpr (sq_nonneg (k : ℚ))) (n - 1)
  have hsumRaw : (∑ k ∈ S, ((k : ℚ) ^ 2)⁻¹) ≤ 2 := by
    apply c5_positive_inverse_square_sum_le_two
    exact Finset.erase_subset _ _
  have hsum : (∑ k ∈ S, a k) ≤ 2 := by
    simpa [a, c5InterpolationNode] using hsumRaw
  have hpow : (∑ k ∈ S, a k) ^ (n - 1) ≤ 2 ^ (n - 1) := by
    gcongr
    exact Finset.sum_nonneg fun k hk => by
      change 0 ≤ (c5InterpolationNode k)⁻¹
      apply inv_nonneg.mpr
      simp [c5InterpolationNode]
  calc
    |(c5LagrangeBasis j).coeff 1| *
        |(∏ k ∈ S, c5PositiveLinearFactor (a k)).coeff (n - 1)| ≤
      |(c5LagrangeBasis j).coeff 1| * (∑ k ∈ S, a k) ^ (n - 1) :=
        mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ ≤ |(c5LagrangeBasis j).coeff 1| * 2 ^ (n - 1) :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    _ = 2 ^ (n - 1) * |(c5LagrangeBasis j).coeff 1| := by ring

/-- For every positive degree, the sum of the absolute Lagrange coefficients
is bounded by `4 * 2^n`; this controls all scaled interpolation weights through
degree fourteen with a uniform rational margin. -/
theorem c5InterpolationCoeffAbsSum_le_four_mul_two_pow
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ j ∈ c5InterpolationIndices,
      |(c5LagrangeBasis j).coeff n|) ≤ 4 * 2 ^ n := by
  rw [← Finset.sum_erase_add c5InterpolationIndices
    (fun j => |(c5LagrangeBasis j).coeff n|)
    (show 0 ∈ c5InterpolationIndices by simp [c5InterpolationIndices])]
  have hzero := c5LagrangeBasis_zeroIndex_coeff_abs_le_two_pow n
  have htail :
      (∑ j ∈ c5PositiveInterpolationIndices,
        |(c5LagrangeBasis j).coeff n|) ≤ 6 * 2 ^ (n - 1) := by
    calc
      (∑ j ∈ c5PositiveInterpolationIndices,
          |(c5LagrangeBasis j).coeff n|) ≤
        ∑ j ∈ c5PositiveInterpolationIndices,
          2 ^ (n - 1) * |(c5LagrangeBasis j).coeff 1| := by
            apply Finset.sum_le_sum
            intro j hj
            exact c5LagrangeBasis_nonzeroIndex_coeff_abs_le_weight j n
              (Finset.mem_erase.mp hj).1 hn
      _ = 2 ^ (n - 1) *
          ∑ j ∈ c5PositiveInterpolationIndices,
            |(c5LagrangeBasis j).coeff 1| := by rw [Finset.mul_sum]
      _ ≤ 2 ^ (n - 1) * 6 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            (∑ j ∈ c5PositiveInterpolationIndices,
                |(c5LagrangeBasis j).coeff 1|) ≤
              ∑ j ∈ c5InterpolationIndices,
                |(c5LagrangeBasis j).coeff 1| := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                    (Finset.erase_subset _ _)
                  intro j hj hjnot
                  exact abs_nonneg _
            _ ≤ 6 := c5InterpolationCoeffOneAbsSum_le_six
      _ = 6 * 2 ^ (n - 1) := by ring
  have hnEq : n = (n - 1) + 1 := by omega
  calc
    (∑ j ∈ c5PositiveInterpolationIndices,
        |(c5LagrangeBasis j).coeff n|) +
        |(c5LagrangeBasis 0).coeff n| ≤
      6 * 2 ^ (n - 1) + 2 ^ n := add_le_add htail hzero
    _ = 4 * 2 ^ n := by
      have hnExp : n = (n - 1) + 1 := by omega
      have hpow : (2 : ℚ) ^ n = 2 ^ (n - 1) * 2 := by
        calc
          (2 : ℚ) ^ n = (2 : ℚ) ^ ((n - 1) + 1) :=
            congrArg (fun e : ℕ => (2 : ℚ) ^ e) hnExp
          _ = (2 : ℚ) ^ (n - 1) * 2 := by rw [pow_succ]
      calc
        (6 : ℚ) * (2 : ℚ) ^ (n - 1) + (2 : ℚ) ^ n =
            6 * (2 : ℚ) ^ (n - 1) + (2 : ℚ) ^ (n - 1) * 2 := by rw [hpow]
        _ = 4 * ((2 : ℚ) ^ (n - 1) * 2) := by ring
        _ = 4 * (2 : ℚ) ^ n := by rw [hpow]

/-- The degree-two through degree-fourteen scaled interpolation weights fit
inside the uniform `10^145` budget used by the analytic source estimate. -/
theorem c5InterpolationWeightSum_lt_ten_145
    (n : ℕ) (hn : 2 ≤ n) (hn14 : n ≤ 14) :
    c5InterpolationWeightSum n < 10 ^ 145 := by
  let scale : ℚ := (100000 : ℚ) ^ (2 * n)
  have hscale : scale ≤ 10 ^ 140 := by
    dsimp [scale]
    rw [show (100000 : ℚ) = 10 ^ 5 by norm_num, ← pow_mul]
    apply pow_le_pow_right₀
    · norm_num
    · omega
  have hcoeff := c5InterpolationCoeffAbsSum_le_four_mul_two_pow n (by omega)
  have hsmall : 4 * (2 : ℚ) ^ n < 10 ^ 5 := by
    calc
      4 * (2 : ℚ) ^ n ≤ 4 * 2 ^ 14 := by gcongr; norm_num
      _ < 10 ^ 5 := by norm_num
  have hweight :
      c5InterpolationWeightSum n =
        scale * ∑ j ∈ c5InterpolationIndices,
          |(c5LagrangeBasis j).coeff n| := by
    unfold c5InterpolationWeightSum c5InterpolationWeight
    dsimp [scale]
    calc
      (∑ j ∈ c5InterpolationIndices,
          |(100000 : ℚ) ^ (2 * n) * (c5LagrangeBasis j).coeff n|) =
        ∑ j ∈ c5InterpolationIndices,
          (100000 : ℚ) ^ (2 * n) * |(c5LagrangeBasis j).coeff n| := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [abs_mul, abs_of_nonneg]
            positivity
      _ = (100000 : ℚ) ^ (2 * n) *
          ∑ j ∈ c5InterpolationIndices,
            |(c5LagrangeBasis j).coeff n| := by rw [Finset.mul_sum]
  calc
    c5InterpolationWeightSum n =
        scale * ∑ j ∈ c5InterpolationIndices,
          |(c5LagrangeBasis j).coeff n| := hweight
    _ ≤ scale * (4 * (2 : ℚ) ^ n) :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ < 10 ^ 140 * 10 ^ 5 := by
      calc
        scale * (4 * (2 : ℚ) ^ n) ≤ 10 ^ 140 * (4 * (2 : ℚ) ^ n) :=
          mul_le_mul_of_nonneg_right hscale (by positivity)
        _ < 10 ^ 140 * 10 ^ 5 :=
          mul_lt_mul_of_pos_left hsmall (by positivity)
    _ = 10 ^ 145 := by rw [← pow_add]

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
