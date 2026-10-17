import KnownMargins

/-! Exact next source obligation. The certified even fifth direction does
not remove the odd fifth direction. Its new coefficient uses theta order 20,
beyond the integral box certificate currently ending at order 18. -/
namespace CarryCriticalSource
open CarrySelfAdjointOperator MeasureTheory
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

def fifthOddCeiling : ℝ :=
  -((∑ k ∈ Finset.range 9, h k*completedNativeRealEvenCharacteristicCoefficient (9-k)) +
    completedNativeRealEvenCharacteristicCoefficient 0 *
      (sourceMomentCoupling h 1 4 ⬝ᵥ
        ((sourceMomentMatrix h 1 4)⁻¹ *ᵥ sourceMomentCoupling h 1 4)))/10

theorem fifthOdd_sourceRemainder :
    nativeSourceSchurRemainder 1 4 =
      10*(fifthOddCeiling-completedNativeRealEvenCharacteristicCoefficient 10) := by
  unfold nativeSourceSchurRemainder fifthOddCeiling
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat]
  ring

theorem fifthOdd_margin_iff_coefficient :
    HasCriticalMargin 1 4 ↔ completedNativeRealEvenCharacteristicCoefficient 10 < fifthOddCeiling := by
  rw [criticalMargin_iff_sourceRemainder 1 4
    (sourceMatrices_through_four_posDef 1 4 (by omega))]
  change (0 < nativeSourceSchurRemainder 1 4) ↔ _
  rw [fifthOdd_sourceRemainder]
  constructor <;> intro hp <;> linarith

theorem source_c10_theta :
    completedNativeRealEvenCharacteristicCoefficient 10 =
      (1520*completedNativeThetaTailMoment 18-completedNativeThetaTailMoment 20)/
        (4*(Nat.factorial 20 : ℝ)) := by
  rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
  have he := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 9
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat] at he
  norm_num only [Nat.reduceMul, show (-1 : ℝ)^10 = 1 by norm_num]
  rw [show completedNativeXiCosineMoment 10 =
      380*completedNativeThetaTailMoment 18-(1/4:ℝ)*completedNativeThetaTailMoment 20 by exact he]
  norm_num [Nat.factorial]
  ring

theorem fifthOdd_margin_iff_thetaMoments :
    HasCriticalMargin 1 4 ↔
      1520*completedNativeThetaTailMoment 18-completedNativeThetaTailMoment 20 <
        4*(Nat.factorial 20 : ℝ)*fifthOddCeiling := by
  rw [fifthOdd_margin_iff_coefficient, source_c10_theta,
    div_lt_iff₀ (by positivity : (0:ℝ) < 4*(Nat.factorial 20 : ℝ))]
  rw [mul_comm fifthOddCeiling]

/-- The whole half-line is retained, including the signed tail. -/
theorem source_theta20_integral :
    (∫ u in Set.Ioi (0:ℝ), (1520*u^18-u^20)*XiThetaCosine.thetaTail u) =
      1520*completedNativeThetaTailMoment 18-completedNativeThetaTailMoment 20 := by
  have h18 := (integrableOn_pow_mul_thetaTail 18).const_mul (1520:ℝ)
  have h20 := integrableOn_pow_mul_thetaTail 20
  have he : (fun u : ℝ => (1520*u^18-u^20)*XiThetaCosine.thetaTail u) =
      fun u => 1520*(u^18*XiThetaCosine.thetaTail u)-u^20*XiThetaCosine.thetaTail u := by
    funext u
    ring
  rw [he, integral_sub h18 h20, integral_const_mul]
  rfl

theorem fifthOdd_margin_iff_thetaIntegral :
    HasCriticalMargin 1 4 ↔
      (∫ u in Set.Ioi (0:ℝ), (1520*u^18-u^20)*XiThetaCosine.thetaTail u) <
        4*(Nat.factorial 20 : ℝ)*fifthOddCeiling := by
  rw [fifthOdd_margin_iff_thetaMoments, source_theta20_integral]

end
end CarryCriticalSource
