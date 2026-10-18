import OddTrialData

namespace CarrySixthOdd
open CarryIntegralCertificate CarrySelfAdjointOperator CarryCriticalSource
open GeometryOfNumbers.Analysis
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem mem_rawTrialPairingBox (i j : ℕ) :
    (rawTrialPairingBox i j).Mem (trialPairing i j) := by
  exact mem_sum _ _ 6 (fun a _ => mem_sum _ _ 6 (fun b _ =>
    mem_mul (mem_mul (mem_ofRat _) (mem_compactMomentBox (a+b+1))) (mem_ofRat _)))

theorem mem_trialPairingBox (i j : ℕ) : (trialPairingBox i j).Mem (trialPairing i j) := by
  by_cases hi : i < 6
  · by_cases hj : j < 6
    · exact mem_of_contained (mem_rawTrialPairingBox i j) (trial_pairing_checks ⟨i,hi⟩ ⟨j,hj⟩)
    · simp only [trialPairingBox,dif_pos hi,dif_neg hj,Box.Mem]
  · simp only [trialPairingBox,dif_neg hi,Box.Mem]

theorem trialPairing_symm (i j : ℕ) : trialPairing i j = trialPairing j i := by
  unfold trialPairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show b+a+1=a+b+1 by omega]
  ring

/-- An exact coordinate identity for the SAME Hankel form. -/
theorem trialMatrix_identity :
    (fun i j : Fin 6 => trialPairing i.val j.val) =
      trialMatrixᵀ * sourceMomentMatrix h 1 6 * trialMatrix := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,trialMatrix,sourceMomentMatrix,
    Finset.sum_mul,trialPairing]
  rw [Finset.sum_comm]
  rw [Fin.sum_univ_eq_sum_range (fun b => ∑ a : Fin 6,
    (trialCoefficient a.val i.val:ℝ)*h (a.val+b+1)*(trialCoefficient b j.val:ℝ)) 6]
  apply Finset.sum_congr rfl
  intro b _
  exact (Fin.sum_univ_eq_sum_range (fun a =>
    (trialCoefficient a i.val:ℝ)*h (a+b+1)*(trialCoefficient b j.val:ℝ)) 6).symm

theorem trialMatrix_det_pos : 0 < trialMatrix.det := by
  have ht : trialMatrix.BlockTriangular id := by
    intro i j hij
    change (trialCoefficient i.val j.val:ℝ) = 0
    rw [trial_upper_check i j hij]
    norm_num
  rw [Matrix.det_of_upperTriangular ht]
  apply Finset.prod_pos
  intro i _
  change (0:ℝ) < (trialCoefficient i.val i.val:ℝ)
  exact_mod_cast trial_diagonal_check i

def trialRemainderBox : ℕ → ℕ → ℕ → Box
  | 0,i,j => trialPairingBox i j
  | r+1,i,j => (trialRemainderBox r i j).add
      (((trialRemainderBox r i r).mul (trialRemainderBox r r j)).div
        (trialRemainderBox r r r)).neg

theorem mem_trialRemainderBox (r i j : ℕ) :
    (trialRemainderBox r i j).Mem (carryPairingRemainder trialPairing r i j) := by
  induction r generalizing i j with
  | zero => exact mem_trialPairingBox i j
  | succ r ih =>
      exact mem_add (ih i j)
        (mem_neg (mem_div (mem_mul (ih i r) (ih r j)) (ih r r)))

theorem trial_six_rectangle_check :
    ∀ r : Fin 6, (trialRemainderBox r.val r.val r.val).positive = true := by
  decide +kernel

theorem trial_sixth_lower_check :
    ((trialRemainderBox 5 5 5).add (Box.point 1).neg).positive = true := by
  decide +kernel

theorem trial_sixth_upper_check :
    ((Box.rat 22 10).add (trialRemainderBox 5 5 5).neg).positive = true := by
  decide +kernel

/-- Quantitative bounds ONLY for the coordinate-transformed ordered pivot. -/
theorem trial_sixth_pivot_bounds :
    1 < carryPairingPivot trialPairing 5 ∧ carryPairingPivot trialPairing 5 < (22/10:ℝ) := by
  have hm := mem_trialRemainderBox 5 5 5
  have hl := pos_of_mem (mem_add hm (mem_neg (mem_point 1))) trial_sixth_lower_check
  have hu := pos_of_mem (mem_add (mem_rat 22 10) (mem_neg hm)) trial_sixth_upper_check
  norm_num only [Int.cast_one,Int.cast_ofNat] at hl hu
  change 1 < carryPairingRemainder trialPairing 5 5 5 ∧
    carryPairingRemainder trialPairing 5 5 5 < (22/10:ℝ)
  constructor <;> linarith only [hl,hu]

theorem trial_six_pivots_pos (r : ℕ) (hr : r < 6) :
    0 < carryPairingPivot trialPairing r :=
  pos_of_mem (mem_trialRemainderBox r r r) (trial_six_rectangle_check ⟨r,hr⟩)

theorem trial_six_posDef : Matrix.PosDef (fun i j : Fin 6 => trialPairing i.val j.val) :=
  carryPairingCholesky_posDef trialPairing_symm 6 trial_six_pivots_pos

/-- Positivity is transported back through a proved invertible coordinate
map. No positive factorization is postulated for the native physical source. -/
theorem odd_source_six_posDef : (sourceMomentMatrix h 1 6).PosDef := by
  have hg := trial_six_posDef
  rw [trialMatrix_identity] at hg
  have hd : IsUnit trialMatrix.det := isUnit_iff_ne_zero.mpr trialMatrix_det_pos.ne'
  letI := Matrix.invertibleOfIsUnitDet trialMatrix hd
  have hc := hg.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_invertible (trialMatrix⁻¹))
  have he : (trialMatrix⁻¹)ᵀ *
      (trialMatrixᵀ * sourceMomentMatrix h 1 6 * trialMatrix) * trialMatrix⁻¹ =
        sourceMomentMatrix h 1 6 := by
    calc
      _ = (trialMatrix*trialMatrix⁻¹)ᵀ * sourceMomentMatrix h 1 6 *
          (trialMatrix*trialMatrix⁻¹) := by
            simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_inv_of_invertible]; simp
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,he] at hc
  exact hc

theorem sixth_odd_pivot_pos : 0 < sourceMomentSchur h 1 5 :=
  (sourceMomentMatrix_succ_posDef_iff h 1 5 CarryThetaPattern.odd_source_five_posDef).mp
    odd_source_six_posDef

theorem sixth_odd_criticalMargin : HasCriticalMargin 1 5 :=
  (criticalMargin_iff_pivot 1 5 CarryThetaPattern.odd_source_five_posDef).mpr sixth_odd_pivot_pos

theorem sixth_odd_sourceThetaGap_pos : 0 < CarryThetaPattern.sourceThetaGap 1 5 :=
  (CarryThetaPattern.criticalMargin_iff_thetaGap 1 5 CarryThetaPattern.odd_source_five_posDef).mp
    sixth_odd_criticalMargin

theorem sixth_odd_theta_integral_certificate :
    CarryThetaPattern.sourceThetaIntegral 11 <
      4*(Nat.factorial 24:ℝ)*CarryThetaPattern.sourceCeiling 1 5 :=
  (CarryThetaPattern.oddMargin_iff_upper_theta 5 CarryThetaPattern.odd_source_five_posDef).mp
    sixth_odd_criticalMargin

end
end CarrySixthOdd
