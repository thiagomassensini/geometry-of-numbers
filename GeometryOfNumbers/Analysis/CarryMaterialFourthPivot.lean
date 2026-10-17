import GeometryOfNumbers.Analysis.CarryMaterialSourceFactor

/-! The next pivot of the unchanged ordered material elimination. This
module exposes the full polarized remainder; it does not assert its sign. -/
namespace GeometryOfNumbers.Analysis
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

def carryMaterialFourthPivot : ℝ := carryPairingPivot carryMaterialEvenPairing 3

/-- Pairing with the first, second and third already extracted columns.
Both original argument orders survive before any symmetry is applied. -/
def carryMaterialFourthOldCoupling : ℝ :=
  carryMaterialEvenPairing 3 0*carryMaterialEvenPairing 0 3/
      carryPairingPivot carryMaterialEvenPairing 0+
    carryPairingRemainder carryMaterialEvenPairing 1 3 1*
      carryPairingRemainder carryMaterialEvenPairing 1 1 3/
        carryPairingPivot carryMaterialEvenPairing 1+
    carryPairingRemainder carryMaterialEvenPairing 2 3 2*
      carryPairingRemainder carryMaterialEvenPairing 2 2 3/
        carryPairingPivot carryMaterialEvenPairing 2

theorem carryMaterialFourthPivot_split :
    carryMaterialFourthPivot = carryMaterialResidualJet 8 8-carryMaterialFourthOldCoupling := by
  unfold carryMaterialFourthPivot carryMaterialFourthOldCoupling carryPairingPivot
  simp only [carryPairingRemainder]
  change _ = carryMaterialEvenPairing 3 3-_
  ring

/-- The raw source equation will replace only the new diagonal. Every
ordered old-new product remains in the already constructed threshold. -/
def carryMaterialFourthSourceThreshold : ℝ :=
  (carryMaterialTaylorShift 9 0).re^2/carryMaterialResponseScale+carryMaterialFourthOldCoupling

/-- Source signs are separate obligations. This conditional bilinear step
uses only the three OLD nonzero pivots and retains the NEW pivot signed. -/
theorem carryMaterialFourthBilinear_sewing
    (hK : ∀ i j, carryMaterialEvenPairing i j = carryMaterialEvenPairing j i)
    (hp : ∀ r < 3, carryPairingPivot carryMaterialEvenPairing r ≠ 0)
    (x y : Fin 4 → ℝ) :
    carryPairingBilinear carryMaterialEvenPairing 4 x y =
      (∑ r : Fin 3, carryPairingPivot carryMaterialEvenPairing r *
        (∑ i : Fin 4, carryPairingColumn carryMaterialEvenPairing r i*x i) *
        (∑ j : Fin 4, carryPairingColumn carryMaterialEvenPairing r j*y j))+
          carryMaterialFourthPivot*x 3*y 3 := by
  have he (i j : Fin 4) : carryMaterialEvenPairing i j =
      (∑ r : Fin 3, carryPairingPivot carryMaterialEvenPairing r *
        carryPairingColumn carryMaterialEvenPairing r i *
        carryPairingColumn carryMaterialEvenPairing r j)+
      if i = 3 ∧ j = 3 then carryMaterialFourthPivot else 0 := by
    have hr := carryPairing_signed_prefix hK 3 i j
    rw [← Fin.sum_univ_eq_sum_range (fun r => carryPairingPivot carryMaterialEvenPairing r *
      carryPairingColumn carryMaterialEvenPairing r i *
      carryPairingColumn carryMaterialEvenPairing r j) 3] at hr
    rw [hr]
    congr 1
    by_cases hi : i = 3
    · subst i
      by_cases hj : j = 3
      · subst j
        rfl
      · rw [if_neg (by simp [hj]),carryPairingRemainder_symm hK 3]
        exact carryPairingRemainder_row_zero _ 3 hp j (by have := j.isLt; omega) 3
    · rw [if_neg (by simp [hi])]
      exact carryPairingRemainder_row_zero _ 3 hp i (by have := i.isLt; omega) j
  simp only [carryPairingBilinear,he,add_mul,Finset.sum_add_distrib]
  have hsum : (∑ i : Fin 4, ∑ j : Fin 4,
      (∑ r : Fin 3, carryPairingPivot carryMaterialEvenPairing r *
        carryPairingColumn carryMaterialEvenPairing r i *
        carryPairingColumn carryMaterialEvenPairing r j)*x i*y j) =
      ∑ r : Fin 3, carryPairingPivot carryMaterialEvenPairing r *
        (∑ i : Fin 4, carryPairingColumn carryMaterialEvenPairing r i*x i) *
        (∑ j : Fin 4, carryPairingColumn carryMaterialEvenPairing r j*y j) := by
    simp only [Finset.sum_mul]
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
  rw [hsum]
  congr 1
  simp [Fin.sum_univ_succ,Fin.isValue]

/-- Back substitution in the actual three source columns. This is a
coefficient combination of observations, not a new physical source. -/
def carryMaterialFourthCritical : Fin 4 → ℝ :=
  let x2 := -carryPairingColumn carryMaterialEvenPairing 2 3
  let x1 := -carryPairingColumn carryMaterialEvenPairing 1 2*x2-
    carryPairingColumn carryMaterialEvenPairing 1 3
  ![-carryPairingColumn carryMaterialEvenPairing 0 1*x1-
      carryPairingColumn carryMaterialEvenPairing 0 2*x2-
      carryPairingColumn carryMaterialEvenPairing 0 3,x1,x2,1]

theorem carryMaterialFourthCritical_last : carryMaterialFourthCritical 3 = 1 := rfl

theorem carryMaterialFourthCritical_ne_zero : carryMaterialFourthCritical ≠ 0 := by
  intro he
  have hh := congrFun he 3
  norm_num only [carryMaterialFourthCritical_last,Pi.zero_apply] at hh

theorem carryMaterialFourthCritical_annihilates
    (hp : ∀ r < 3, carryPairingPivot carryMaterialEvenPairing r ≠ 0) (r : Fin 3) :
    (∑ i : Fin 4, carryPairingColumn carryMaterialEvenPairing r i*
      carryMaterialFourthCritical i) = 0 := by
  have hd (k : ℕ) (hk : k < 3) := carryPairingColumn_diagonal carryMaterialEvenPairing k (hp k hk)
  have hz (k i : ℕ) (hk : k < 3) (hi : i < k) := carryPairingColumn_above carryMaterialEvenPairing k i
    (fun j hj => hp j (lt_trans hj hk)) hi
  fin_cases r
  · simp only [Fin.val_zero,Fin.sum_univ_succ,Fin.val_succ,carryMaterialFourthCritical,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,hd 0 (by decide)]
    ring
  · simp only [Fin.val_succ,Fin.val_zero,Fin.sum_univ_succ,carryMaterialFourthCritical,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
      hz 1 0 (by decide) (by decide),hd 1 (by decide)]
    ring
  · simp only [Fin.val_succ,Fin.val_zero,Fin.sum_univ_succ,carryMaterialFourthCritical,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
      hz 2 0 (by decide) (by decide),hz 2 1 (by decide) (by decide),hd 2 (by decide)]
    ring

theorem carryMaterialFourthCritical_pairing
    (hK : ∀ i j, carryMaterialEvenPairing i j = carryMaterialEvenPairing j i)
    (hp : ∀ r < 3, carryPairingPivot carryMaterialEvenPairing r ≠ 0) (y : Fin 4 → ℝ) :
    carryPairingBilinear carryMaterialEvenPairing 4 carryMaterialFourthCritical y =
      carryMaterialFourthPivot*y 3 := by
  rw [carryMaterialFourthBilinear_sewing hK hp]
  simp only [carryMaterialFourthCritical_annihilates hp,mul_zero,zero_mul,
    Finset.sum_const_zero,carryMaterialFourthCritical_last,zero_add,mul_one]

end
end GeometryOfNumbers.Analysis
