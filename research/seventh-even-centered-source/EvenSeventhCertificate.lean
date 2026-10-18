import EvenTrialData

namespace CarrySeventhEven
open CarryIntegralCertificate CarrySelfAdjointOperator CarryCriticalSource
open GeometryOfNumbers.Analysis
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem mem_rawTrialPairingBox (i j : ℕ) :
    (rawTrialPairingBox i j).Mem (trialPairing i j) := by
  exact mem_sum _ _ 7 (fun a _ => mem_sum _ _ 7 (fun b _ =>
    mem_mul (mem_mul (mem_ofRat _) (mem_compactMomentBox (a+b))) (mem_ofRat _)))

theorem mem_trialPairingBox (i j : ℕ) : (trialPairingBox i j).Mem (trialPairing i j) := by
  by_cases hi : i < 7
  · by_cases hj : j < 7
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
  rw [show b+a=a+b by omega]
  ring

/-- An exact coordinate identity for the SAME Hankel form. -/
theorem trialMatrix_identity :
    (fun i j : Fin 7 => trialPairing i.val j.val) =
      trialMatrixᵀ * sourceMomentMatrix h 0 7 * trialMatrix := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,trialMatrix,sourceMomentMatrix,
    Finset.sum_mul,trialPairing,Nat.add_zero]
  rw [Finset.sum_comm]
  rw [Fin.sum_univ_eq_sum_range (fun b => ∑ a : Fin 7,
    (trialCoefficient a.val i.val:ℝ)*h (a.val+b)*(trialCoefficient b j.val:ℝ)) 7]
  apply Finset.sum_congr rfl
  intro b _
  exact (Fin.sum_univ_eq_sum_range (fun a =>
    (trialCoefficient a i.val:ℝ)*h (a+b)*(trialCoefficient b j.val:ℝ)) 7).symm

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

theorem trial_seven_rectangle_check :
    ∀ r : Fin 7, (trialRemainderBox r.val r.val r.val).positive = true := by
  decide +kernel

theorem trial_seventh_lower_check :
    ((trialRemainderBox 6 6 6).add (Box.point 5).neg).positive = true := by
  decide +kernel

theorem trial_seventh_upper_check :
    ((Box.rat 53 10).add (trialRemainderBox 6 6 6).neg).positive = true := by
  decide +kernel

/-- Quantitative bounds ONLY for the coordinate-transformed ordered pivot. -/
theorem trial_seventh_pivot_bounds :
    5 < carryPairingPivot trialPairing 6 ∧ carryPairingPivot trialPairing 6 < (53/10:ℝ) := by
  have hm := mem_trialRemainderBox 6 6 6
  have hl := pos_of_mem (mem_add hm (mem_neg (mem_point 5))) trial_seventh_lower_check
  have hu := pos_of_mem (mem_add (mem_rat 53 10) (mem_neg hm)) trial_seventh_upper_check
  norm_num only [Int.cast_ofNat] at hl hu
  change 5 < carryPairingRemainder trialPairing 6 6 6 ∧
    carryPairingRemainder trialPairing 6 6 6 < (53/10:ℝ)
  constructor <;> linarith only [hl,hu]

theorem trial_seven_pivots_pos (r : ℕ) (hr : r < 7) :
    0 < carryPairingPivot trialPairing r :=
  pos_of_mem (mem_trialRemainderBox r r r) (trial_seven_rectangle_check ⟨r,hr⟩)

theorem trial_seven_posDef : Matrix.PosDef (fun i j : Fin 7 => trialPairing i.val j.val) :=
  carryPairingCholesky_posDef trialPairing_symm 7 trial_seven_pivots_pos

/-- Positivity is transported back through a proved invertible coordinate
map. No positive factorization is postulated for the native physical source. -/
theorem even_source_seven_posDef : (sourceMomentMatrix h 0 7).PosDef := by
  have hg := trial_seven_posDef
  rw [trialMatrix_identity] at hg
  have hd : IsUnit trialMatrix.det := isUnit_iff_ne_zero.mpr trialMatrix_det_pos.ne'
  letI := Matrix.invertibleOfIsUnitDet trialMatrix hd
  have hc := hg.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_invertible (trialMatrix⁻¹))
  have he : (trialMatrix⁻¹)ᵀ *
      (trialMatrixᵀ * sourceMomentMatrix h 0 7 * trialMatrix) * trialMatrix⁻¹ =
        sourceMomentMatrix h 0 7 := by
    calc
      _ = (trialMatrix*trialMatrix⁻¹)ᵀ * sourceMomentMatrix h 0 7 *
          (trialMatrix*trialMatrix⁻¹) := by
            simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_inv_of_invertible]; simp
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,he] at hc
  exact hc

theorem seventh_even_pivot_pos : 0 < sourceMomentSchur h 0 6 :=
  (sourceMomentMatrix_succ_posDef_iff h 0 6 CarrySixthEven.even_source_six_posDef).mp
    even_source_seven_posDef

theorem seventh_even_criticalMargin : HasCriticalMargin 0 6 :=
  (criticalMargin_iff_pivot 0 6 CarrySixthEven.even_source_six_posDef).mpr seventh_even_pivot_pos

theorem seventh_even_sourceThetaGap_pos : 0 < CarryThetaPattern.sourceThetaGap 0 6 :=
  (CarryThetaPattern.criticalMargin_iff_thetaGap 0 6 CarrySixthEven.even_source_six_posDef).mp
    seventh_even_criticalMargin

theorem seventh_even_theta_integral_certificate :
    -4*(Nat.factorial 26:ℝ)*CarryThetaPattern.sourceCeiling 0 6 < CarryThetaPattern.sourceThetaIntegral 12 :=
  (CarryThetaPattern.evenMargin_iff_lower_theta 6 CarrySixthEven.even_source_six_posDef).mp
    seventh_even_criticalMargin

end
end CarrySeventhEven
