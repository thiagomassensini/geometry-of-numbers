import MovingSchur

namespace CarryCriticalEuler
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

def pair (m : ℕ → ℝ) (s : ℕ) {N : ℕ} (x y : Fin N → ℝ) : ℝ :=
  x ⬝ᵥ (sourceMomentMatrix m s N *ᵥ y)

def jetEuler {N : ℕ} (v : Fin N → ℝ) : Fin N → ℝ := fun i => (i.val:ℝ)*v i

def weightedForm (m : ℕ → ℝ) (s : ℕ) {N : ℕ} (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, v i*v j *
    (((i.val+j.val+s:ℕ):ℝ)+1)*(2*((i.val+j.val+s:ℕ):ℝ)+3)*m (i.val+j.val+s+1)

theorem pair_symm (m : ℕ → ℝ) (s : ℕ) {N : ℕ} (x y : Fin N → ℝ) :
    pair m s x y = pair m s y x := by
  have ht : (sourceMomentMatrix m s N)ᵀ = sourceMomentMatrix m s N := by
    ext i j
    simp [sourceMomentMatrix,Nat.add_comm]
  unfold pair
  rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,ht,dotProduct_comm]

theorem pair_self (m : ℕ → ℝ) (s : ℕ) {N : ℕ} (v : Fin N → ℝ) :
    pair m s v v = sourceMomentQuadratic m s N v := by
  simp [pair,sourceMomentQuadratic]

/-- Jet-order Euler operation only; it is not identified with the material clock. -/
theorem weighted_euler_identity (m : ℕ → ℝ) (s : ℕ) {N : ℕ} (v : Fin N → ℝ) :
    weightedForm m s v =
      ((2:ℝ)*(s:ℝ)^2+5*(s:ℝ)+3)*pair m (s+1) v v +
      (8*(s:ℝ)+10)*pair m (s+1) v (jetEuler v) +
      4*pair m (s+1) v (jetEuler (jetEuler v)) +
      4*pair m (s+1) (jetEuler v) (jetEuler v) := by
  -- Keep the two mixed Euler contributions until their symmetric pairing is used.
  have hexpand : weightedForm m s v =
      ((2:ℝ)*(s:ℝ)^2+5*(s:ℝ)+3)*pair m (s+1) v v +
      (4*(s:ℝ)+5)*(pair m (s+1) v (jetEuler v)+pair m (s+1) (jetEuler v) v) +
      2*(pair m (s+1) v (jetEuler (jetEuler v))+
         pair m (s+1) (jetEuler (jetEuler v)) v) +
      4*pair m (s+1) (jetEuler v) (jetEuler v) := by
    simp only [weightedForm,pair,jetEuler,sourceMomentMatrix,Matrix.mulVec,dotProduct,
      Finset.mul_sum,mul_add,Nat.add_assoc]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring
  rw [hexpand,pair_symm m (s+1) (jetEuler v) v,
    pair_symm m (s+1) (jetEuler (jetEuler v)) v]
  ring

/-- Shifted pair against a lower-degree vector is determined by its top
coefficient and the original Schur relation, with no positivity premise. -/
theorem stationary_shift_pair (m : ℕ → ℝ) (s n : ℕ) (v : Fin (n+2) → ℝ)
    (p : ℝ) (hrel : sourceMomentMatrix m s (n+2) *ᵥ v = Fin.snoc 0 p)
    (r : Fin (n+1) → ℝ) :
    pair m (s+1) v (Fin.snoc r 0) = p*r (Fin.last n) := by
  have hrow (j : Fin (n+1)) :
      (v ᵥ* sourceMomentMatrix m (s+1) (n+2)) j.castSucc =
        (sourceMomentMatrix m s (n+2) *ᵥ v) j.succ := by
    simp only [Matrix.vecMul,Matrix.mulVec,dotProduct,sourceMomentMatrix]
    apply Finset.sum_congr rfl
    intro i hi
    have he : i.val+j.castSucc.val+(s+1) = j.succ.val+i.val+s := by simp; omega
    rw [he]
    ring
  unfold pair
  rw [Matrix.dotProduct_mulVec,dotProduct,Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,mul_zero,add_zero,hrow,hrel]
  rw [Fin.sum_univ_castSucc]
  simp [← Fin.castSucc_succ,Fin.snoc_castSucc,Fin.snoc_last]

end
end CarryCriticalEuler
