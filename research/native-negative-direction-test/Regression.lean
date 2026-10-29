import NegativeTransport

/-! Existing PR41 control data are regressions, NEVER canonical moments. -/
open CarryNegativeDirection CarrySelfAdjointOperator
open scoped BigOperators Matrix
noncomputable section

-- Same future-crossing control as PR41: a null prefix with a future nonzero cross.
example : let m : ℕ → ℝ := fun n => if n=0 ∨ n=3 then 1 else 0
    sourceMomentQuadratic m 0 2 ![0,1]=0 ∧
    sourceMomentCoupling m 0 2 ⬝ᵥ ![0,1]=1 ∧
    sourceMomentQuadratic m 0 3 (nullCouplingWitness m 0 2 ![0,1])=-1 := by
  dsimp only
  have hz : sourceMomentQuadratic (fun n => if n=0 ∨ n=3 then (1:ℝ) else 0) 0 2 ![0,1]=0 := by
    norm_num [sourceMomentQuadratic,sourceMomentMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  have hb : sourceMomentCoupling (fun n => if n=0 ∨ n=3 then (1:ℝ) else 0) 0 2 ⬝ᵥ ![0,1]=1 := by
    norm_num [sourceMomentCoupling,dotProduct,Fin.sum_univ_two]
  refine ⟨hz,hb,?_⟩
  rw [null_coupling_witness_energy _ _ _ _ hz (by rw [hb]; norm_num)]
  norm_num

-- The previous block really is PSD and singular, so PosDef cannot be silently assumed.
example : let m : ℕ → ℝ := fun n => if n=0 ∨ n=3 then 1 else 0
    (sourceMomentMatrix m 0 2).PosSemidef ∧ ¬ (sourceMomentMatrix m 0 2).PosDef := by
  dsimp only
  have he : sourceMomentMatrix (fun n => if n=0 ∨ n=3 then (1:ℝ) else 0) 0 2=
      Matrix.diagonal ![1,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sourceMomentMatrix,Matrix.diagonal]
  rw [he]
  constructor
  · exact Matrix.posSemidef_diagonal_iff.mpr (by intro i; fin_cases i <;> norm_num)
  · intro hp
    have h := hp.diag_pos (i:=(1:Fin 2))
    norm_num at h

-- A different singular prefix is compatible with b=Ay, yet its residual is negative.
-- Auxiliary rational data only: not a claim about the canonical sequence.
example : let m : ℕ → ℝ := fun n => if n < 4 then 1 else 1/2
    sourceMomentMatrix m 0 2 *ᵥ ![1,-1] = 0 ∧
    sourceMomentMatrix m 0 2 *ᵥ ![1,0] = sourceMomentCoupling m 0 2 ∧
    sourceMomentQuadratic m 0 3 (Fin.snoc (-![1,0]) 1) = -1/2 := by
  dsimp only
  have hy : sourceMomentMatrix (fun n => if n < 4 then (1:ℝ) else 1/2) 0 2 *ᵥ ![1,0] =
      sourceMomentCoupling (fun n => if n < 4 then (1:ℝ) else 1/2) 0 2 := by
    ext i
    fin_cases i <;> norm_num [sourceMomentMatrix,sourceMomentCoupling,Matrix.mulVec,
      dotProduct,Fin.sum_univ_two]
  refine ⟨?_,hy,?_⟩
  · ext i
    fin_cases i <;> norm_num [sourceMomentMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · rw [solution_witness_energy _ _ _ _ hy]
    norm_num [sourceMomentCoupling,dotProduct,Fin.sum_univ_two]
