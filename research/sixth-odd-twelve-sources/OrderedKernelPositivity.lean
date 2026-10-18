import VariationalSchur

/-! Ordered elimination of an already specified real symmetric pairing.
No source sign is assumed except the explicitly supplied finite PosDef. -/
namespace CarryOrderedKernel
open GeometryOfNumbers.Analysis
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def firstSchurKernel (K : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  K (i+1) (j+1)-K (i+1) 0*K 0 (j+1)/K 0 0

theorem firstSchurKernel_symm (K : ℕ → ℕ → ℝ)
    (hK : ∀ i j, K i j=K j i) (i j : ℕ) :
    firstSchurKernel K i j = firstSchurKernel K j i := by
  unfold firstSchurKernel
  rw [hK (i+1) (j+1),hK (i+1) 0,hK (j+1) 0]
  ring

theorem remainder_firstSchur (K : ℕ → ℕ → ℝ) (r i j : ℕ) :
    carryPairingRemainder (firstSchurKernel K) r i j =
      carryPairingRemainder K (r+1) (i+1) (j+1) := by
  induction r generalizing i j with
  | zero => rfl
  | succ r ih => simp only [carryPairingRemainder,ih]

theorem firstSchurKernel_posDef (K : ℕ → ℕ → ℝ)
    (hK : ∀ i j, K i j=K j i) (n : ℕ)
    (hM : Matrix.PosDef (fun i j : Fin (n+1) => K i.val j.val)) :
    Matrix.PosDef (fun i j : Fin n => firstSchurKernel K i.val j.val) := by
  let a := K 0 0
  let v : Fin n → ℝ := fun j => K 0 (j.val+1)
  let D : Matrix (Fin n) (Fin n) ℝ := fun i j => K (i.val+1) (j.val+1)
  have ha : 0 < a := hM.diag_pos (i := 0)
  have cons_energy (x : Fin n → ℝ) (t : ℝ) :
      (Fin.cons t x) ⬝ᵥ ((fun i j : Fin (n+1) => K i.val j.val) *ᵥ Fin.cons t x) =
        a*t^2+2*t*(v ⬝ᵥ x)+x ⬝ᵥ (D *ᵥ x) := by
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.cons_zero,
      Fin.cons_succ,Fin.val_zero,Fin.val_succ,mul_add,Finset.sum_add_distrib]
    have he : (∑ i : Fin n, x i*(K (i.val+1) 0*t)) = t*(v ⬝ᵥ x) := by
      simp only [v,dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hK (i.val+1) 0]
      ring
    rw [he]
    dsimp [a,v,D,Matrix.mulVec,dotProduct]
    ring
  have schur_energy (x : Fin n → ℝ) :
      x ⬝ᵥ ((fun i j : Fin n => firstSchurKernel K i.val j.val) *ᵥ x) =
        x ⬝ᵥ (D *ᵥ x)-(v ⬝ᵥ x)^2/a := by
    have he : (∑ i : Fin n, x i*(∑ j : Fin n,
        (K (i.val+1) 0*K 0 (j.val+1)/a)*x j)) = (v ⬝ᵥ x)^2/a := by
      simp only [v,dotProduct,pow_two,Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hK (i.val+1) 0]
      ring
    simp only [firstSchurKernel,Matrix.mulVec,dotProduct,sub_mul,
      Finset.sum_sub_distrib,mul_sub]
    change _ = _
    rw [he]
    rfl
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact firstSchurKernel_symm K hK j.val i.val
  · intro x hx
    let t := -(v ⬝ᵥ x)/a
    have hz : (Fin.cons t x : Fin (n+1) → ℝ) ≠ 0 := by
      intro hz
      apply hx
      funext i
      simpa only [Fin.cons_succ,Pi.zero_apply] using congrFun hz i.succ
    have hp := hM.dotProduct_mulVec_pos hz
    simp only [star_trivial] at hp ⊢
    rw [cons_energy] at hp
    rw [schur_energy]
    have he : a*t^2+2*t*(v ⬝ᵥ x)+x ⬝ᵥ (D *ᵥ x) =
        x ⬝ᵥ (D *ᵥ x)-(v ⬝ᵥ x)^2/a := by
      dsimp [t]
      field_simp [ha.ne']
      ring
    rwa [he] at hp

/-- Converse sign extraction for the ORIGINAL ordered pivot. This does not
identify its quantitative interval with a preconditioned pivot interval. -/
theorem ordered_pivot_pos_of_posDef (K : ℕ → ℕ → ℝ)
    (hK : ∀ i j, K i j=K j i) (n : ℕ)
    (hM : Matrix.PosDef (fun i j : Fin (n+1) => K i.val j.val)) :
    0 < carryPairingPivot K n := by
  induction n generalizing K with
  | zero => exact hM.diag_pos (i := 0)
  | succ n ih =>
      have hp := ih (firstSchurKernel K) (firstSchurKernel_symm K hK)
        (firstSchurKernel_posDef K hK (n+1) hM)
      simpa only [carryPairingPivot,remainder_firstSchur] using hp

end
end CarryOrderedKernel
