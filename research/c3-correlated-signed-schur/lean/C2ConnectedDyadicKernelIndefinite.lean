import C2ConnectedDyadicTowerSign

/-!
For ALL dyadic cutoffs T=60*2^k, the NATURAL but naive
connected-defect matrix K_T(p,q)=a_T(p)a_T(q)-a_T(pq)
on prime-camera labels (3,5) is indefinite, with an exact negative
determinant -1/(64*4^k).

This is an all-cutoff dyadic no-go for identifying scalar connected
C2 cumulants with a positive Gram; it does not exclude other
constructions, and does NOT imply negative NATIVE moment pivots.
-/

namespace CarryWheelNativeSignedGate
open CPFormal.Carry.C2
open CPFormal.Analytic.Cp

theorem mass60_dyadic_9 (k : ℕ) :
    oddCoreTruncatedMass (60*2^k) 9 =
      1-(1/2:ℚ)*(1/2:ℚ)^k := by
  apply dyadic_mass60_closed 9 (by norm_num) (by norm_num) (1/2) ?_ k
  rw [mass60_9]
  norm_num

theorem mass120_25 : oddCoreTruncatedMass 120 25 = (1/2:ℚ) := by
  norm_num [oddCoreTruncatedMass, oddCoreMinusDepth, oddCorePlusDepth,
    oddCoreBranchMass, dyadicBranchWeight, Finset.sum_Icc_succ_top]

theorem dyadic_mass120_step
    (m k : ℕ) (hm : 0 < m) (hm30 : m ≤ 30) :
    oddCoreTruncatedMass (120*2^(k+1)) m =
      (1/2:ℚ) + (1/2:ℚ)*oddCoreTruncatedMass (120*2^k) m := by
  have hp : 0 < 2^k := by positivity
  have hmM : m ≤ 30*2^k := by omega
  have h := oddCoreTruncatedMass_eight_mul_eq
    (M:=30*2^k) (m:=m) hm hmM
  have hleft : 8*(30*2^k) = 120*2^(k+1) := by
    rw [pow_succ]; ring
  have hright : 4*(30*2^k) = 120*2^k := by ring
  simpa only [hleft,hright] using h

theorem mass120_dyadic_25 (k : ℕ) :
    oddCoreTruncatedMass (120*2^k) 25 =
      1-(1/2:ℚ)*(1/2:ℚ)^k := by
  induction k with
  | zero =>
    simp only [pow_zero, mul_one]
    rw [mass120_25]
    norm_num
  | succ k ih =>
    rw [dyadic_mass120_step 25 k (by norm_num) (by norm_num),
        ih, pow_succ]
    ring

theorem mass60_dyadic_25 (k : ℕ) :
    oddCoreTruncatedMass (60*2^k) 25 =
      1-(1/2:ℚ)^k := by
  cases k with
  | zero =>
    simpa using mass60_25
  | succ k =>
    have h := mass120_dyadic_25 k
    have hh : 60*2^(k+1) = 120*2^k := by
      rw [pow_succ]
      ring
    rw [hh, h, pow_succ]
    ring

def dyadicConnectedPositiveDefect (k p q : ℕ) : ℚ :=
  oddCoreTruncatedMass (60*2^k) p *
    oddCoreTruncatedMass (60*2^k) q -
  oddCoreTruncatedMass (60*2^k) (p*q)

theorem dyadic_defect_3_3 (k : ℕ) :
    dyadicConnectedPositiveDefect k 3 3 =
      (1/4:ℚ)*(1/2:ℚ)^k +
      (1/64:ℚ)*(1/4:ℚ)^k := by
  unfold dyadicConnectedPositiveDefect
  rw [mass60_dyadic_3, mass60_dyadic_9]
  have h : (1/4:ℚ)^k = (1/2:ℚ)^k*(1/2:ℚ)^k := by
    rw [show (1/4:ℚ)=(1/2)*(1/2) by norm_num, mul_pow]
  rw [h]
  ring

theorem dyadic_defect_5_5 (k : ℕ) :
    dyadicConnectedPositiveDefect k 5 5 =
      (1/2:ℚ)*(1/2:ℚ)^k +
      (1/16:ℚ)*(1/4:ℚ)^k := by
  unfold dyadicConnectedPositiveDefect
  rw [mass60_dyadic_5, mass60_dyadic_25]
  have h : (1/4:ℚ)^k = (1/2:ℚ)^k*(1/2:ℚ)^k := by
    rw [show (1/4:ℚ)=(1/2)*(1/2) by norm_num, mul_pow]
  rw [h]
  ring

theorem dyadic_defect_3_5 (k : ℕ) :
    dyadicConnectedPositiveDefect k 3 5 =
      (3/8:ℚ)*(1/2:ℚ)^k +
      (1/32:ℚ)*(1/4:ℚ)^k := by
  unfold dyadicConnectedPositiveDefect
  rw [mass60_dyadic_3, mass60_dyadic_5, mass60_dyadic_15]
  have h : (1/4:ℚ)^k = (1/2:ℚ)^k*(1/2:ℚ)^k := by
    rw [show (1/4:ℚ)=(1/2)*(1/2) by norm_num, mul_pow]
  rw [h]
  ring

/-- This is an INDEFINITE Gram candidate at every dyadic depth,
even though every entry stays positive. -/
theorem dyadic_naive_defect_matrix_det_negative_exact (k : ℕ) :
    dyadicConnectedPositiveDefect k 3 3 *
      dyadicConnectedPositiveDefect k 5 5 -
      (dyadicConnectedPositiveDefect k 3 5)^2 =
        -(1/64:ℚ)*(1/4:ℚ)^k := by
  rw [dyadic_defect_3_3, dyadic_defect_5_5, dyadic_defect_3_5]
  have h : (1/4:ℚ)^k = (1/2:ℚ)^k*(1/2:ℚ)^k := by
    rw [show (1/4:ℚ)=(1/2)*(1/2) by norm_num, mul_pow]
  rw [h]
  ring

theorem dyadic_naive_defect_matrix_det_strictly_neg (k : ℕ) :
    dyadicConnectedPositiveDefect k 3 3 *
      dyadicConnectedPositiveDefect k 5 5 -
      (dyadicConnectedPositiveDefect k 3 5)^2 < 0 := by
  rw [dyadic_naive_defect_matrix_det_negative_exact]
  have hp : 0 < (1/4:ℚ)^k := by positivity
  linarith

end CarryWheelNativeSignedGate
