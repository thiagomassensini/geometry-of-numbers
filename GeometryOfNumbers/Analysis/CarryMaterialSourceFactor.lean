import GeometryOfNumbers.Analysis.CarryMaterialMixedSchur
import Mathlib.LinearAlgebra.Matrix.Block

/-! Triangular extraction of observations AFTER complete material synthesis.
The recurrence is defined without positivity. Its signed prefix retains the
entire remainder; a real Cholesky identity requires separately proved signs.
No source, metric or Hilbert carrier is defined by a target Hankel matrix. -/
namespace GeometryOfNumbers.Analysis
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Algebraic elimination of actual ordered pairings. At a zero pivot this
total definition subtracts zero; it does not assert annihilation of that row. -/
def carryPairingRemainder (K : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => K
  | n+1 => fun i j => carryPairingRemainder K n i j -
      carryPairingRemainder K n i n * carryPairingRemainder K n n j /
        carryPairingRemainder K n n n

def carryPairingPivot (K : ℕ → ℕ → ℝ) (r : ℕ) : ℝ :=
  carryPairingRemainder K r r r

def carryPairingColumn (K : ℕ → ℕ → ℝ) (r i : ℕ) : ℝ :=
  carryPairingRemainder K r i r / carryPairingPivot K r

theorem carryPairingPivot_zero (K : ℕ → ℕ → ℝ) : carryPairingPivot K 0 = K 0 0 := rfl

theorem carryPairingPivot_one (K : ℕ → ℕ → ℝ) :
    carryPairingPivot K 1 = K 1 1-K 1 0*K 0 1/K 0 0 := rfl

theorem carryPairingPivot_two (K : ℕ → ℕ → ℝ) :
    carryPairingPivot K 2 = K 2 2-K 2 0*K 0 2/K 0 0-
      (K 2 1-K 2 0*K 0 1/K 0 0)*(K 1 2-K 1 0*K 0 2/K 0 0)/
        (K 1 1-K 1 0*K 0 1/K 0 0) := rfl

theorem carryPairingRemainder_symm {K : ℕ → ℕ → ℝ}
    (hK : ∀ i j, K i j = K j i) (n i j : ℕ) :
    carryPairingRemainder K n i j = carryPairingRemainder K n j i := by
  induction n generalizing i j with
  | zero => exact hK i j
  | succ n ih =>
    simp only [carryPairingRemainder]
    rw [ih i j,ih i n,ih n j]
    ring

/-- Complete signed polarized prefix, valid even at zero pivots. In
particular the remainder is not discarded to obtain a positive expression. -/
theorem carryPairing_signed_prefix {K : ℕ → ℕ → ℝ}
    (hK : ∀ i j, K i j = K j i) (n i j : ℕ) :
    K i j = (∑ r ∈ Finset.range n, carryPairingPivot K r *
      carryPairingColumn K r i * carryPairingColumn K r j) +
        carryPairingRemainder K n i j := by
  induction n with
  | zero => simp [carryPairingRemainder]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [carryPairingRemainder,carryPairingColumn,carryPairingPivot]
    rw [carryPairingRemainder_symm hK n n j]
    by_cases hp : carryPairingRemainder K n n n = 0
    · simp [hp]
    · field_simp
      ring

/-- A row disappears only after its own nonzero pivot has been verified.
This is the precise nondegeneracy requirement for a finite LDL factor. -/
theorem carryPairingRemainder_row_zero (K : ℕ → ℕ → ℝ) (n : ℕ)
    (hp : ∀ r < n, carryPairingPivot K r ≠ 0) (i : ℕ) (hi : i < n) (j : ℕ) :
    carryPairingRemainder K n i j = 0 := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      have hn := hp n (by omega)
      change carryPairingRemainder K n n j -
        carryPairingPivot K n * carryPairingRemainder K n n j / carryPairingPivot K n = 0
      field_simp
      ring
    · have hl : i < n := by omega
      have hh : ∀ r < n, carryPairingPivot K r ≠ 0 := fun r hr => hp r (by omega)
      simp only [carryPairingRemainder,ih hh i hl j,ih hh i hl n,zero_mul,zero_div,sub_self]

theorem carryPairingColumn_diagonal (K : ℕ → ℕ → ℝ) (r : ℕ)
    (hp : carryPairingPivot K r ≠ 0) : carryPairingColumn K r r = 1 := by
  exact div_self hp

theorem carryPairingColumn_above (K : ℕ → ℕ → ℝ) (r i : ℕ)
    (hp : ∀ k < r, carryPairingPivot K k ≠ 0) (hi : i < r) :
    carryPairingColumn K r i = 0 := by
  rw [carryPairingColumn,carryPairingRemainder_row_zero K r hp i hi r,zero_div]

/-- Finite signed factor identity. Nonzero pivots, rather than `PosDef`,
justify elimination; their signs have not been inferred from the algebra. -/
theorem carryPairing_signed_factor {K : ℕ → ℕ → ℝ}
    (hK : ∀ i j, K i j = K j i) (n : ℕ)
    (hp : ∀ r < n, carryPairingPivot K r ≠ 0) (i j : Fin n) :
    K i j = ∑ r : Fin n, carryPairingPivot K r *
      carryPairingColumn K r i * carryPairingColumn K r j := by
  have he := carryPairing_signed_prefix hK n i j
  rw [carryPairingRemainder_row_zero K n hp i i.isLt j,add_zero] at he
  rw [Fin.sum_univ_eq_sum_range (fun r => carryPairingPivot K r *
    carryPairingColumn K r i * carryPairingColumn K r j) n]
  exact he

/-- The candidate real square-root factor is computed from the same ordered
pairings. Its definition does not certify the signs under the square roots. -/
def carryPairingCholesky (K : ℕ → ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i r => carryPairingColumn K r i * Real.sqrt (carryPairingPivot K r)

/-- Exact defect of the real square-root candidate, at every finite order,
without a sign or invertibility assumption. Negative pivots and the entire
uneliminated remainder remain visible. -/
theorem carryPairingCholesky_defect {K : ℕ → ℕ → ℝ}
    (hK : ∀ i j, K i j = K j i) (n : ℕ) (i j : Fin n) :
    K i j = (carryPairingCholesky K n*(carryPairingCholesky K n)ᵀ) i j+
      carryPairingRemainder K n i j-
        ∑ r : Fin n, max (-carryPairingPivot K r) 0 *
          carryPairingColumn K r i * carryPairingColumn K r j := by
  have he := carryPairing_signed_prefix hK n i j
  rw [← Fin.sum_univ_eq_sum_range (fun r => carryPairingPivot K r *
    carryPairingColumn K r i * carryPairingColumn K r j) n] at he
  rw [he]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,carryPairingCholesky]
  have ht : (∑ r : Fin n, carryPairingPivot K r*carryPairingColumn K r i*carryPairingColumn K r j) =
      (∑ r : Fin n, carryPairingColumn K r i*Real.sqrt (carryPairingPivot K r)*
        (carryPairingColumn K r j*Real.sqrt (carryPairingPivot K r)))-
      ∑ r : Fin n, max (-carryPairingPivot K r) 0*carryPairingColumn K r i*carryPairingColumn K r j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    have hs : (Real.sqrt (carryPairingPivot K r))^2-max (-carryPairingPivot K r) 0 =
        carryPairingPivot K r := by
      by_cases hp : 0 ≤ carryPairingPivot K r
      · rw [Real.sq_sqrt hp,max_eq_right (neg_nonpos.mpr hp),sub_zero]
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hp),
          max_eq_left (neg_nonneg.mpr (le_of_not_ge hp))]
        ring
    calc
      _ = ((Real.sqrt (carryPairingPivot K r))^2-max (-carryPairingPivot K r) 0)*
        carryPairingColumn K r i*carryPairingColumn K r j := by rw [hs]
      _ = _ := by ring
  rw [ht]
  ring

theorem carryPairingCholesky_identity {K : ℕ → ℕ → ℝ}
    (hK : ∀ i j, K i j = K j i) (n : ℕ)
    (hp : ∀ r < n, 0 < carryPairingPivot K r) :
    carryPairingCholesky K n * (carryPairingCholesky K n)ᵀ =
      (fun i j : Fin n => K i j) := by
  ext i j
  rw [carryPairing_signed_factor hK n (fun r hr => (hp r hr).ne') i j]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,carryPairingCholesky]
  apply Finset.sum_congr rfl
  intro r _
  have hs := Real.sq_sqrt (hp r r.isLt).le
  calc
    _ = (Real.sqrt (carryPairingPivot K r))^2 *
      carryPairingColumn K r i * carryPairingColumn K r j := by ring
    _ = _ := by rw [hs]

theorem carryPairingCholesky_above (K : ℕ → ℕ → ℝ) (n : ℕ)
    (hp : ∀ r < n, carryPairingPivot K r ≠ 0) (i r : Fin n) (hi : i < r) :
    carryPairingCholesky K n i r = 0 := by
  rw [carryPairingCholesky,carryPairingColumn_above K r i
    (fun k hk => hp k (lt_trans hk r.isLt)) hi,zero_mul]

theorem carryPairingCholesky_diagonal (K : ℕ → ℕ → ℝ) (n : ℕ)
    (hp : ∀ r < n, carryPairingPivot K r ≠ 0) (i : Fin n) :
    carryPairingCholesky K n i i = Real.sqrt (carryPairingPivot K i) := by
  rw [carryPairingCholesky,carryPairingColumn_diagonal K i (hp i i.isLt),one_mul]

theorem carryPairingCholesky_det_pos (K : ℕ → ℕ → ℝ) (n : ℕ)
    (hp : ∀ r < n, 0 < carryPairingPivot K r) :
    0 < (carryPairingCholesky K n).det := by
  have ht : (carryPairingCholesky K n).BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact carryPairingCholesky_above K n (fun r hr => (hp r hr).ne') i j hij
  rw [Matrix.det_of_lowerTriangular _ ht]
  apply Finset.prod_pos
  intro i _
  rw [carryPairingCholesky_diagonal K n (fun r hr => (hp r hr).ne')]
  exact Real.sqrt_pos.mpr (hp i i.isLt)

/-- Positivity is a consequence of this constructed factor and its proved
diagonal signs, rather than an input to its definition. -/
theorem carryPairingCholesky_posDef {K : ℕ → ℕ → ℝ}
    (hK : ∀ i j, K i j = K j i) (n : ℕ)
    (hp : ∀ r < n, 0 < carryPairingPivot K r) :
    Matrix.PosDef (fun i j : Fin n => K i j) := by
  let C := carryPairingCholesky K n
  have hd : IsUnit C.det := isUnit_iff_ne_zero.mpr (carryPairingCholesky_det_pos K n hp).ne'
  letI := Matrix.invertibleOfIsUnitDet C hd
  have hc := (Matrix.PosDef.one (n := Fin n) (R := ℝ)).mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_invertible C)
  rw [Matrix.mul_one,Matrix.conjTranspose_eq_transpose_of_trivial] at hc
  change (carryPairingCholesky K n*(carryPairingCholesky K n)ᵀ).PosDef at hc
  rwa [carryPairingCholesky_identity hK n hp] at hc

/-- Every ordered crossing is retained before taking a diagonal energy. -/
def carryPairingBilinear (K : ℕ → ℕ → ℝ) (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, K i j*x i*y j

theorem carryPairingBilinear_eq_dotProduct (K : ℕ → ℕ → ℝ) (n : ℕ) (x y : Fin n → ℝ) :
    carryPairingBilinear K n x y = x ⬝ᵥ ((fun i j : Fin n => K i j) *ᵥ y) := by
  simp only [carryPairingBilinear,Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem carryPairingBilinear_factor {K : ℕ → ℕ → ℝ}
    (hK : ∀ i j, K i j = K j i) (n : ℕ)
    (hp : ∀ r < n, carryPairingPivot K r ≠ 0) (x y : Fin n → ℝ) :
    carryPairingBilinear K n x y =
      ∑ r : Fin n, carryPairingPivot K r *
        (∑ i : Fin n, carryPairingColumn K r i*x i) *
        (∑ j : Fin n, carryPairingColumn K r j*y j) := by
  simp only [carryPairingBilinear,carryPairing_signed_factor hK n hp,
    Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Restore the already extracted central channel without changing any
coupling. This is matrix bookkeeping after synthesis, not a new state. -/
def carryPairingBorderFactor {n : ℕ} (a : ℝ) (v : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => Fin.cases (Fin.cases (Real.sqrt a) (fun _ => 0) j)
    (fun k => Fin.cases (v k/Real.sqrt a) (fun r => C k r) j) i

theorem carryPairingBorderFactor_origin {n : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (v : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    (carryPairingBorderFactor a v C*(carryPairingBorderFactor a v C)ᵀ) 0 0 = a := by
  simp [Matrix.mul_apply,Fin.sum_univ_succ,carryPairingBorderFactor,← pow_two,
    Real.sq_sqrt ha]

theorem carryPairingBorderFactor_origin_succ {n : ℕ} (a : ℝ) (ha : 0 < a)
    (v : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (carryPairingBorderFactor a v C*(carryPairingBorderFactor a v C)ᵀ) 0 i.succ = v i := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
    carryPairingBorderFactor,Fin.cases_zero,Fin.cases_succ,zero_mul,Finset.sum_const_zero,add_zero]
  field_simp [Real.sqrt_pos.mpr ha |>.ne']

theorem carryPairingBorderFactor_succ_origin {n : ℕ} (a : ℝ) (ha : 0 < a)
    (v : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (carryPairingBorderFactor a v C*(carryPairingBorderFactor a v C)ᵀ) i.succ 0 = v i := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
    carryPairingBorderFactor,Fin.cases_zero,Fin.cases_succ,mul_zero,Finset.sum_const_zero,add_zero]
  field_simp [Real.sqrt_pos.mpr ha |>.ne']

theorem carryPairingBorderFactor_succ_succ {n : ℕ} (a : ℝ) (ha : 0 < a)
    (v : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (carryPairingBorderFactor a v C*(carryPairingBorderFactor a v C)ᵀ) i.succ j.succ =
      v i*v j/a+(C*Cᵀ) i j := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
    carryPairingBorderFactor,Fin.cases_succ,Fin.cases_zero]
  congr 1
  have hs := Real.sq_sqrt ha.le
  have hn := (Real.sqrt_pos.mpr ha).ne'
  field_simp
  rw [hs]
  ring

theorem carryPairingBorderFactor_det_pos {n : ℕ} (a : ℝ) (ha : 0 < a)
    (v : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, i < j → C i j = 0) (hd : ∀ i, 0 < C i i) :
    0 < (carryPairingBorderFactor a v C).det := by
  have ht : (carryPairingBorderFactor a v C).BlockTriangular OrderDual.toDual := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro j
      refine Fin.cases ?_ (fun r => ?_) j
      · intro hij
        exact (lt_irrefl _ hij).elim
      · intro _
        rfl
    · intro j
      refine Fin.cases ?_ (fun r => ?_) j
      · intro hij
        change k.succ < (0 : Fin (n+1)) at hij
        exact (not_lt_of_ge (Fin.zero_le _ ) hij).elim
      · intro hij
        change k.succ < r.succ at hij
        exact hC k r (Fin.succ_lt_succ_iff.mp hij)
  rw [Matrix.det_of_lowerTriangular _ ht]
  apply Finset.prod_pos
  intro i _
  refine Fin.cases ?_ (fun k => ?_) i
  · exact Real.sqrt_pos.mpr ha
  · exact hd k

/-- The inputs here are already synthesized physical residual observations;
they are not moments introduced as the definition of a new physical state. -/
def carryMaterialEvenPairing (i j : ℕ) : ℝ :=
  carryMaterialResidualJet (2*(i+1)) (2*(j+1))

def carryMaterialOddPairing (i j : ℕ) : ℝ :=
  carryMaterialResidualJet (2*i+1) (2*j+1)

def carryMaterialEvenCholesky (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  carryPairingCholesky carryMaterialEvenPairing n

end
end GeometryOfNumbers.Analysis
