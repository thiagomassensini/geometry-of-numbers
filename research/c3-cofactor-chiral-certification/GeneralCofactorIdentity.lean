import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Fin

namespace C3GeneralCofactor

noncomputable section
set_option autoImplicit false

variable {R : Type*}

/-- The symmetric one-row/one-column border of a square matrix. -/
def border {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (d : R) :
    Matrix (Fin n.succ) (Fin n.succ) R := fun i j =>
  Fin.lastCases
    (Fin.lastCases d b j)
    (fun i => Fin.lastCases (b i) (fun j => A i j) j)
    i

@[simp] theorem border_castSucc_castSucc {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (d : R)
    (i j : Fin n) : border A b d i.castSucc j.castSucc = A i j := by
  simp [border]

@[simp] theorem border_castSucc_last {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (d : R)
    (i : Fin n) : border A b d i.castSucc (Fin.last n) = b i := by
  simp [border]

@[simp] theorem border_last_castSucc {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (d : R)
    (i : Fin n) : border A b d (Fin.last n) i.castSucc = b i := by
  simp [border]

@[simp] theorem border_last_last {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (d : R) :
    border A b d (Fin.last n) (Fin.last n) = d := by
  simp [border]

@[simp] theorem border_minor_permute {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R)
    (b : Fin n.succ → R) (d : R) (j : Fin n.succ) :
    (border A b d).submatrix Fin.castSucc (fun k => j.castSucc.succAbove k) =
      (A.updateCol j b).submatrix id (Fin.cycleIcc j (Fin.last n)) := by
  haveI : NeZero n.succ := ⟨Nat.succ_ne_zero n⟩
  ext i k
  change border A b d i.castSucc (j.castSucc.succAbove k) =
    A.updateCol j b i (Fin.cycleIcc j (Fin.last n) k)
  by_cases hkj : k < j
  · have h : k.castSucc < j.castSucc := Fin.castSucc_lt_castSucc_iff.mpr hkj
    rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have hne : k ≠ j := ne_of_lt hkj
    simp [Fin.cycleIcc_of_lt hkj, Matrix.updateCol, hne]
  · have hjk : j ≤ k := le_of_not_gt hkj
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hjk)]
    by_cases hkl : k = Fin.last n
    · subst k
      simp [Fin.cycleIcc_of_last (i := j) (j := Fin.last n) (Fin.le_last _),
        Matrix.updateCol]
    · have hklt : k < Fin.last n := Fin.lt_last_iff_ne_last.mpr hkl
      have hkltval : k.val < n := by
        simpa [Fin.lt_def, Fin.val_last] using hklt
      have hval : (k + 1).val = k.val + 1 :=
        Fin.val_add_one_of_lt' (by omega)
      have hidx : k.succ = (k + 1).castSucc := by
        apply Fin.ext
        simp [Fin.val_succ, Fin.val_castSucc, hval]
      rw [hidx]
      have hjleval : j.val ≤ k.val := Fin.le_iff_val_le_val.mp hjk
      have hne : k + 1 ≠ j := by
        intro he
        have hv := congrArg Fin.val he
        rw [hval] at hv
        omega
      simp [Fin.cycleIcc_of_ge_of_lt hjk hklt, Matrix.updateCol, hne]

theorem border_upperLeft {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R)
    (b : Fin n.succ → R) (d : R) :
    (border A b d).submatrix Fin.castSucc Fin.castSucc = A := by
  ext i j
  simp

private theorem border_cofactor_sign {n : ℕ} [CommRing R] (j : Fin n.succ) :
    (-1 : R) ^ (n + 1 + j.val) * (-1 : R) ^ (n - j.val) = -1 := by
  have hexp : n + 1 + j.val + (n - j.val) = 2 * n + 1 := by omega
  rw [← pow_add, hexp, pow_succ, pow_mul]
  norm_num

theorem border_det_succ {n : ℕ} [CommRing R]
    (A : Matrix (Fin n.succ) (Fin n.succ) R) (b : Fin n.succ → R) (d : R) :
    (border A b d).det = A.det * d - ∑ i : Fin n.succ, b i * (A.adjugate.mulVec b) i := by
  rw [Matrix.det_succ_row (border A b d) (Fin.last n.succ), Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.val_castSucc, border_last_castSucc, border_last_last,
    Fin.succAbove_last]
  rw [border_upperLeft]
  simp_rw [border_minor_permute]
  simp_rw [Matrix.det_permute', Fin.sign_cycleIcc_of_le (Fin.le_last _)]
  simp_rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  -- The Laplace signs and the column-cycle signs multiply to `-1`.
  have hsign (m : ℕ) : (↑↑((-1 : ℤˣ) ^ m) : R) = (-1 : R) ^ m := by norm_cast
  simp_rw [hsign]
  simp_rw [Fin.val_last]
  have hterm (i : Fin n.succ) :
      (-1 : R) ^ (n + 1 + i.val) * b i *
          ((-1 : R) ^ (n - i.val) * (A.adjugate.mulVec b) i) =
        -(b i * (A.adjugate.mulVec b) i) := by
    calc
      _ = ((-1 : R) ^ (n + 1 + i.val) * (-1 : R) ^ (n - i.val)) *
          (b i * (A.adjugate.mulVec b) i) := by ring
      _ = -1 * (b i * (A.adjugate.mulVec b) i) := by rw [border_cofactor_sign]
      _ = _ := by ring
  have hlastsign : (-1 : R) ^ (n + 1 + (n + 1)) = 1 := by
    rw [show n + 1 + (n + 1) = 2 * (n + 1) by omega, pow_mul]
    norm_num
  simp_rw [hterm, hlastsign, Finset.sum_neg_distrib]
  ring

theorem border_det {n : ℕ} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (d : R) :
    (border A b d).det = A.det * d - ∑ i : Fin n, b i * (A.adjugate.mulVec b) i := by
  cases n with
  | zero =>
      rw [Matrix.det_fin_one]
      simp only [border, ← Fin.last_zero, Fin.lastCases_last]
      simp
  | succ n => exact border_det_succ A b d

def cofactorVector {n : ℕ} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) : Fin n.succ → R :=
  Fin.lastCases A.det (fun i => -(A.adjugate.mulVec b) i)

def lastScalarVector {n : ℕ} [Zero R] (x : R) : Fin n.succ → R :=
  Fin.lastCases x (fun _ => 0)

private theorem adjugate_mulVec_left {n : ℕ} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) :
    A.mulVec (A.adjugate.mulVec b) = A.det • b := by
  rw [Matrix.mulVec_mulVec b A A.adjugate, Matrix.mul_adjugate]
  simp [Matrix.smul_mulVec]

theorem border_mulVec_cofactor {n : ℕ} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (d : R) :
    (border A b d).mulVec (cofactorVector A b) =
      lastScalarVector ((border A b d).det) := by
  have hA := adjugate_mulVec_left A b
  have hAi (i : Fin n) :
      (A.mulVec (A.adjugate.mulVec b)) i = A.det * b i := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hA i
  have hsumA (i : Fin n) :
      (∑ j : Fin n, A i j * -(A.adjugate.mulVec b) j) =
        -(A.mulVec (A.adjugate.mulVec b)) i := by
    rw [Matrix.mulVec_apply, dotProduct]
    calc
      (∑ j : Fin n, A i j * -(A.adjugate.mulVec b) j) =
          ∑ j : Fin n, -(A i j * (A.adjugate.mulVec b) j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = -∑ j : Fin n, A i j * (A.adjugate.mulVec b) j := by
            rw [Finset.sum_neg_distrib]
  have hsumB :
      (∑ j : Fin n, b j * -(A.adjugate.mulVec b) j) =
        -∑ j : Fin n, b j * (A.adjugate.mulVec b) j := by
    calc
      (∑ j : Fin n, b j * -(A.adjugate.mulVec b) j) =
          ∑ j : Fin n, -(b j * (A.adjugate.mulVec b) j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = -∑ j : Fin n, b j * (A.adjugate.mulVec b) j := by
            rw [Finset.sum_neg_distrib]
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_castSucc]
    simp only [Matrix.row_apply, border_last_castSucc, border_last_last,
      cofactorVector, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [hsumB]
    rw [border_det]
    simp only [lastScalarVector, Fin.lastCases_last]
    ring
  · rw [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_castSucc]
    simp only [Matrix.row_apply, border_castSucc_castSucc, border_castSucc_last,
      cofactorVector, Fin.lastCases_castSucc, Fin.lastCases_last,
      lastScalarVector]
    rw [hsumA i, hAi i]
    ring

theorem cofactorVector_quadratic {n : ℕ} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (d : R) :
    (cofactorVector A b) ⬝ᵥ ((border A b d).mulVec (cofactorVector A b)) =
      A.det * (border A b d).det := by
  rw [border_mulVec_cofactor]
  simp [dotProduct, cofactorVector, lastScalarVector, Fin.sum_univ_castSucc,
    Fin.lastCases_castSucc, Fin.lastCases_last]

theorem border_det_three_by_three [CommRing R] (a b d e f g : R) :
    (border (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) R)
      (![e, f] : Fin 2 → R) g).det =
        (a * d - b ^ 2) * g - d * e ^ 2 + 2 * b * e * f - a * f ^ 2 := by
  rw [border_det]
  simp [Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

theorem cofactorVector_three_by_three [CommRing R] (a b d e f : R) :
    cofactorVector (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) R)
        (![e, f] : Fin 2 → R) =
      (![b * f - d * e, b * e - a * f, a * d - b ^ 2] : Fin 3 → R) := by
  ext i
  fin_cases i
  · change cofactorVector (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) R)
        (![e, f] : Fin 2 → R) ((0 : Fin 2).castSucc) =
      (![b * f - d * e, b * e - a * f, a * d - b ^ 2] : Fin 3 → R)
        ((0 : Fin 2).castSucc)
    rw [cofactorVector, Fin.lastCases_castSucc]
    simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · change cofactorVector (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) R)
        (![e, f] : Fin 2 → R) ((1 : Fin 2).castSucc) =
      (![b * f - d * e, b * e - a * f, a * d - b ^ 2] : Fin 3 → R)
        ((1 : Fin 2).castSucc)
    rw [cofactorVector, Fin.lastCases_castSucc]
    simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · change cofactorVector (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) R)
        (![e, f] : Fin 2 → R) (Fin.last 2) =
      (![b * f - d * e, b * e - a * f, a * d - b ^ 2] : Fin 3 → R) (Fin.last 2)
    rw [cofactorVector, Fin.lastCases_last]
    simp
    ring

#print axioms border_minor_permute
#print axioms border_det_succ
#print axioms border_upperLeft
#print axioms border_det
#print axioms border_mulVec_cofactor
#print axioms cofactorVector_quadratic
#print axioms border_det_three_by_three
#print axioms cofactorVector_three_by_three

end
end C3GeneralCofactor
