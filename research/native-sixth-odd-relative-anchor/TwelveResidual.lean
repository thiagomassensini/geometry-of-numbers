import TwelveCoordinates

namespace CarrySixthRelative
open CarrySelfAdjointOperator CarryDirectAnchor CarryIntegralCertificate CarryVariationalSchur
open CarryCriticalSource CarrySixthOdd
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

/-- General congruence leaves the inverse-residual correction unchanged. -/
theorem congruence_inverse_residual {n : ℕ} (P A : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (hP : IsUnit P) (hA : IsUnit A) :
    r ⬝ᵥ (A⁻¹ *ᵥ r) = (Pᵀ *ᵥ r) ⬝ᵥ ((Pᵀ * A * P)⁻¹ *ᵥ (Pᵀ *ᵥ r)) := by
  let w := A⁻¹ *ᵥ r
  let u := P⁻¹ *ᵥ w
  letI := hA.invertible
  letI := hP.invertible
  have hw : A *ᵥ w = r := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hpu : P *ᵥ u = w := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hbu : (Pᵀ * A * P) *ᵥ u = Pᵀ *ᵥ r := by
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hpu,hw]
  have hB : IsUnit (Pᵀ * A * P) := (((Matrix.isUnit_transpose P).mpr hP).mul hA).mul hP
  letI := hB.invertible
  have he := congrArg (fun v => (Pᵀ * A * P)⁻¹ *ᵥ v) hbu
  rw [Matrix.mulVec_mulVec,Matrix.inv_mul_of_invertible,Matrix.one_mulVec] at he
  change r ⬝ᵥ w = (Pᵀ *ᵥ r) ⬝ᵥ _
  rw [← he,dotProduct_comm (Pᵀ *ᵥ r) u]
  calc
    r ⬝ᵥ w = w ⬝ᵥ r := dotProduct_comm r w
    _ = (P *ᵥ u) ⬝ᵥ r := by rw [hpu]
    _ = u ⬝ᵥ (Pᵀ *ᵥ r) := by rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]

theorem twelve_residual_component (a : Fin 5) :
    sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve a =
      h (a.val+6) + ∑ b ∈ Finset.range 5, h (a.val+b+1)*twelveCoeff b := by
  unfold sourceTrialResidual sourceMomentCoupling sourceMomentMatrix twelveSolve
  simp only [Pi.sub_apply,Matrix.mulVec,dotProduct,mul_neg,Finset.sum_neg_distrib,sub_neg_eq_add]
  rw [Fin.sum_univ_eq_sum_range (fun b => h (a.val+b+1)*twelveCoeff b) 5]

theorem twelve_trial_cross_expand (i : Fin 5) :
    trialPairing i.val 5 = ∑ a ∈ Finset.range 5,
      (CarrySixthOdd.trialCoefficient a i.val:ℝ) *
      ((10:ℝ)^18 * h (a+6) + ∑ b ∈ Finset.range 5,
        h (a+b+1) * (CarrySixthOdd.trialCoefficient b 5:ℝ)) := by
  unfold trialPairing
  rw [Finset.sum_range_succ]
  simp only [old_trial_last_row_zero i,Rat.cast_zero,zero_mul,Finset.sum_const_zero,add_zero]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_range_succ]
  have hlast : (CarrySixthOdd.trialCoefficient 5 5:ℝ) = (10:ℝ)^18 := by
    norm_num [CarrySixthOdd.trialCoefficient,trialCoefficientData]
  rw [hlast]
  rw [mul_add,Finset.mul_sum]
  have hsum : (∑ b ∈ Finset.range 5,
      (CarrySixthOdd.trialCoefficient a i.val:ℝ)*h (a+b+1)*
        (CarrySixthOdd.trialCoefficient b 5:ℝ)) =
      ∑ b ∈ Finset.range 5, (CarrySixthOdd.trialCoefficient a i.val:ℝ)*
        (h (a+b+1)*(CarrySixthOdd.trialCoefficient b 5:ℝ)) := by
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hsum]
  have hh : a+5+1=a+6 := by omega
  rw [hh]
  ring

/-- Every crossed residual in the old coordinate frame is one of the checked
original trial pairings; the trial vector itself is unchanged. -/
theorem transformed_residual_entry (i : Fin 5) :
    (oldCoordinateᵀ *ᵥ sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve) i =
      trialPairing i.val 5/(10:ℝ)^18 := by
  rw [twelve_trial_cross_expand,Finset.sum_div,← Fin.sum_univ_eq_sum_range]
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,oldCoordinate]
  apply Finset.sum_congr rfl
  intro a ha
  rw [twelve_residual_component]
  have hsum : (∑ b ∈ Finset.range 5, h (a.val+b+1)*twelveCoeff b) =
      (∑ b ∈ Finset.range 5, h (a.val+b+1) *
        (CarrySixthOdd.trialCoefficient b 5:ℝ))/(10:ℝ)^18 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b hb
    unfold twelveCoeff
    ring
  rw [hsum]
  field_simp

theorem trial_cross_bounded (i : Fin 5) : |trialPairing i.val 5| ≤ (1/50:ℝ) := by
  have h := mem_of_contained (mem_trialPairingBox i.val 5)
    (show (trialPairingBox i.val 5).contained (.finite (-(2*10^58)) (2*10^58))=true by
      fin_cases i <;> decide +kernel)
  norm_num [Box.Mem,intervalScale] at h
  apply abs_le.mpr
  constructor <;> nlinarith [h.1,h.2]

end
end CarrySixthRelative
