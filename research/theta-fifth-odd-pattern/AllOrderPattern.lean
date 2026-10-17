import NextSourceGate

/-! All-order source pattern. These are exact identities and a sign
criterion, not an unconditional positive estimate at arbitrary order. -/
namespace CarryThetaPattern
open CarrySelfAdjointOperator CarryCriticalSource MeasureTheory
open scoped BigOperators Matrix Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

def sourceCeiling (s : Fin 2) (n : ℕ) : ℝ :=
  -((∑ k ∈ Finset.range (2*n+s.val), h k*
      completedNativeRealEvenCharacteristicCoefficient (2*n+s.val-k)) +
    completedNativeRealEvenCharacteristicCoefficient 0 *
      (sourceMomentCoupling h s.val n ⬝ᵥ
        ((sourceMomentMatrix h s.val n)⁻¹ *ᵥ sourceMomentCoupling h s.val n)))/
      ((2*n+s.val+1:ℕ):ℝ)

theorem sourceRemainder_ceiling (s : Fin 2) (n : ℕ) :
    nativeSourceSchurRemainder s.val n = ((2*n+s.val+1:ℕ):ℝ)*
      (sourceCeiling s n-completedNativeRealEvenCharacteristicCoefficient (2*n+s.val+1)) := by
  have hn : (((2*n+s.val+1:ℕ):ℝ)) ≠ 0 := by positivity
  unfold sourceCeiling nativeSourceSchurRemainder
  field_simp [hn]
  ring

theorem criticalMargin_iff_sourceCoefficient (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) :
    HasCriticalMargin s n ↔
      completedNativeRealEvenCharacteristicCoefficient (2*n+s.val+1) < sourceCeiling s n := by
  rw [criticalMargin_iff_sourceRemainder s n hA,sourceRemainder_ceiling]
  rw [mul_pos_iff_of_pos_left (by positivity : (0:ℝ) < ((2*n+s.val+1:ℕ):ℝ)),sub_pos]

/-- The weight is derived from the source coefficient; it changes sign
on the original infinite integration interval. -/
def sourceThetaIntegral (d : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0:ℝ),
    (4*((2*d+2:ℕ):ℝ)*((2*d+1:ℕ):ℝ)*u^(2*d)-u^(2*d+2))*XiThetaCosine.thetaTail u

theorem sourceThetaIntegral_moments (d : ℕ) :
    sourceThetaIntegral d =
      4*((2*d+2:ℕ):ℝ)*((2*d+1:ℕ):ℝ)*completedNativeThetaTailMoment (2*d)-
        completedNativeThetaTailMoment (2*d+2) := by
  have h0 := (integrableOn_pow_mul_thetaTail (2*d)).const_mul
    (4*((2*d+2:ℕ):ℝ)*((2*d+1:ℕ):ℝ))
  have h1 := integrableOn_pow_mul_thetaTail (2*d+2)
  have he : (fun u : ℝ =>
      (4*((2*d+2:ℕ):ℝ)*((2*d+1:ℕ):ℝ)*u^(2*d)-u^(2*d+2))*XiThetaCosine.thetaTail u) =
    fun u => (4*((2*d+2:ℕ):ℝ)*((2*d+1:ℕ):ℝ))*(u^(2*d)*XiThetaCosine.thetaTail u)-
      u^(2*d+2)*XiThetaCosine.thetaTail u := by funext u; ring
  unfold sourceThetaIntegral
  rw [he,integral_sub h0 h1,integral_const_mul]
  rfl


/-- Recover the existing positive Xi-kernel moment; no new positive
kernel is chosen to fit the logarithmic moments. -/
theorem sourceThetaIntegral_eq_xiMoment (d : ℕ) :
    sourceThetaIntegral d = 4*completedNativeXiCosineMoment (d+1) := by
  rw [sourceThetaIntegral_moments,completedNativeXiCosineMoment_succ_eq_thetaTailMoments]
  ring

theorem sourceThetaIntegral_pos (d : ℕ) : 0 < sourceThetaIntegral d := by
  rw [sourceThetaIntegral_eq_xiMoment]
  exact mul_pos (by norm_num) (completedNativeXiCosineMoment_pos (d+1))

theorem sourceCoefficient_theta (d : ℕ) :
    completedNativeRealEvenCharacteristicCoefficient (d+1) =
      (-1:ℝ)^(d+1)*sourceThetaIntegral d/(4*(Nat.factorial (2*d+2):ℝ)) := by
  rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder,
    completedNativeXiCosineMoment_succ_eq_thetaTailMoments,sourceThetaIntegral_moments,
    show 2*(d+1)=2*d+2 by omega]
  ring

theorem sourceCoefficient_parity (s : Fin 2) (n : ℕ) :
    completedNativeRealEvenCharacteristicCoefficient (2*n+s.val+1) =
      (-1:ℝ)^(s.val+1)*sourceThetaIntegral (2*n+s.val)/
        (4*(Nat.factorial (2*(2*n+s.val)+2):ℝ)) := by
  rw [sourceCoefficient_theta]
  have he : (-1:ℝ)^(2*n+s.val+1) = (-1:ℝ)^(s.val+1) := by
    rw [show 2*n+s.val+1=2*n+(s.val+1) by omega,pow_add,
      Even.neg_one_pow (show Even (2*n) from ⟨n,by omega⟩),one_mul]
  rw [he]

theorem criticalMargin_iff_sourceTheta (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) :
    HasCriticalMargin s n ↔
      (-1:ℝ)^(s.val+1)*sourceThetaIntegral (2*n+s.val) <
        4*(Nat.factorial (2*(2*n+s.val)+2):ℝ)*sourceCeiling s n := by
  rw [criticalMargin_iff_sourceCoefficient s n hA,sourceCoefficient_parity,
    div_lt_iff₀ (by positivity : (0:ℝ) < 4*(Nat.factorial (2*(2*n+s.val)+2):ℝ))]
  rw [mul_comm (sourceCeiling s n)]


/-- The literal signed gap, with the full old-source feedback retained. -/
def sourceThetaGap (s : Fin 2) (n : ℕ) : ℝ :=
  4*(Nat.factorial (2*(2*n+s.val)+2):ℝ)*sourceCeiling s n-
    (-1:ℝ)^(s.val+1)*sourceThetaIntegral (2*n+s.val)

theorem sourceSchur_thetaGap (s : Fin 2) (n : ℕ) :
    completedNativeRealEvenCharacteristicCoefficient 0 *
      (4*(Nat.factorial (2*(2*n+s.val)+2):ℝ))*sourceMomentSchur h s.val n =
        ((2*n+s.val+1:ℕ):ℝ)*sourceThetaGap s n := by
  have hd : (4*(Nat.factorial (2*(2*n+s.val)+2):ℝ)) ≠ 0 := by positivity
  calc
    _ = (4*(Nat.factorial (2*(2*n+s.val)+2):ℝ))*nativeSourceSchurRemainder s.val n := by
      rw [nativeSourceSchurRemainder_eq]
      ring
    _ = _ := by
      rw [sourceRemainder_ceiling,sourceCoefficient_parity]
      unfold sourceThetaGap
      field_simp [hd]

/-- A division-free physical limit for the all-order theta gap. -/
theorem physicalThetaGap_tendsto (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) :
    Filter.Tendsto (fun k => completedNativeRealEvenCharacteristicCoefficient 0 *
      (4*(Nat.factorial (2*(2*n+s.val)+2):ℝ))*criticalBalance s n k)
      Filter.atTop (nhds (2*((2*n+s.val+1:ℕ):ℝ)*sourceThetaGap s n)) := by
  have ht := (criticalBalance_tendsto s n hA).const_mul
    (completedNativeRealEvenCharacteristicCoefficient 0 *
      (4*(Nat.factorial (2*(2*n+s.val)+2):ℝ)))
  have he : (completedNativeRealEvenCharacteristicCoefficient 0 *
      (4*(Nat.factorial (2*(2*n+s.val)+2):ℝ)))*(2*sourceMomentSchur h s.val n) =
        2*((2*n+s.val+1:ℕ):ℝ)*sourceThetaGap s n := by
    calc
      _ = 2*(completedNativeRealEvenCharacteristicCoefficient 0 *
        (4*(Nat.factorial (2*(2*n+s.val)+2):ℝ))*sourceMomentSchur h s.val n) := by ring
      _ = _ := by rw [sourceSchur_thetaGap]; ring
  rw [he] at ht
  exact ht

theorem criticalMargin_iff_thetaGap (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) :
    HasCriticalMargin s n ↔ 0 < sourceThetaGap s n := by
  rw [criticalMargin_iff_sourceTheta s n hA]
  exact sub_pos.symm

/-- Even steps require a lower bound on the signed theta integral. -/
theorem evenMargin_iff_lower_theta (n : ℕ)
    (hA : (sourceMomentMatrix h 0 n).PosDef) :
    HasCriticalMargin 0 n ↔ -4*(Nat.factorial (4*n+2):ℝ)*sourceCeiling 0 n <
      sourceThetaIntegral (2*n) := by
  have hh := criticalMargin_iff_sourceTheta 0 n hA
  norm_num at hh
  rw [show 2*(2*n)+2=4*n+2 by omega] at hh
  rw [hh]
  constructor <;> intro ht <;> linarith

/-- Odd steps require an upper bound; the orientation does not stay fixed. -/
theorem oddMargin_iff_upper_theta (n : ℕ)
    (hA : (sourceMomentMatrix h 1 n).PosDef) :
    HasCriticalMargin 1 n ↔ sourceThetaIntegral (2*n+1) <
      4*(Nat.factorial (4*n+4):ℝ)*sourceCeiling 1 n := by
  have hh := criticalMargin_iff_sourceTheta 1 n hA
  norm_num at hh
  simpa only [show 2*(2*n+1)+2=4*n+4 by omega] using hh

def AllSourceThetaGates : Prop :=
  ∀ (s : Fin 2) (n : ℕ), (sourceMomentMatrix h s.val n).PosDef →
    (-1:ℝ)^(s.val+1)*sourceThetaIntegral (2*n+s.val) <
      4*(Nat.factorial (2*(2*n+s.val)+2):ℝ)*sourceCeiling s n

theorem allSourceThetaGates_iff_margins : AllSourceThetaGates ↔ AllCriticalMargins := by
  constructor
  · intro hg s n hA
    exact (criticalMargin_iff_sourceTheta s n hA).mpr (hg s n hA)
  · intro hm s n hA
    exact (criticalMargin_iff_sourceTheta s n hA).mp (hm s n hA)

theorem allSourceThetaGates_returnBounds (hg : AllSourceThetaGates) :
    CarryReturnCompatibility.AllFiniteReturnBounds :=
  allCriticalMargins_returnBounds (allSourceThetaGates_iff_margins.mp hg)

theorem sourceCeiling_fifthOdd : sourceCeiling 1 4 = fifthOddCeiling := by
  norm_num [sourceCeiling,fifthOddCeiling]

end
end CarryThetaPattern
