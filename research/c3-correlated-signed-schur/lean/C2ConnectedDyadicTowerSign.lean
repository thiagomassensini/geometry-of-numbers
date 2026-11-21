import C2ConnectedDefectSchurObstruction

/-!
Explicit DYADIC ALL-DEPTH SIGN of the original finite C2 connected
semiprime cumulant at vertices (3,5), using the unchanged 4M/8M exact
mass identity. This is stronger than any fixed cutoff numerical witness.

The connected coefficient stays strictly NEGATIVE, yet tends to 0
on 60*2^k. Hence a raw fixed-vertex b_T(15) must not be identified
with a fixed positive completed-native Schur pivot.
-/

namespace CarryWheelNativeSignedGate
open CPFormal.Carry.C2
open CPFormal.Analytic.Cp

theorem dyadic_mass60_step
    (m k : ℕ) (hm : 0 < m) (hm15 : m ≤ 15) :
    oddCoreTruncatedMass (60*2^(k+1)) m =
      (1/2:ℚ) + (1/2:ℚ)*oddCoreTruncatedMass (60*2^k) m := by
  have hp : 0 < 2^k := by positivity
  have hmM : m ≤ 15*2^k := by omega
  have h := oddCoreTruncatedMass_eight_mul_eq
    (M:=15*2^k) (m:=m) hm hmM
  have hleft : 8*(15*2^k) = 60*2^(k+1) := by
    rw [pow_succ]
    ring
  have hright : 4*(15*2^k) = 60*2^k := by ring
  simpa only [hleft,hright] using h

theorem dyadic_mass60_closed
    (m : ℕ) (hm : 0 < m) (hm15 : m ≤ 15) (delta : ℚ)
    (hbase : oddCoreTruncatedMass 60 m = 1-delta) :
    ∀ k : ℕ, oddCoreTruncatedMass (60*2^k) m =
      1-delta*(1/2:ℚ)^k := by
  intro k
  induction k with
  | zero =>
    simpa using hbase
  | succ k ih =>
    rw [dyadic_mass60_step m k hm hm15, ih, pow_succ]
    ring

theorem mass60_dyadic_3 (k : ℕ) :
    oddCoreTruncatedMass (60*2^k) 3 =
      1-(1/8:ℚ)*(1/2:ℚ)^k := by
  apply dyadic_mass60_closed 3 (by norm_num) (by norm_num) (1/8) ?_ k
  rw [mass60_3]
  norm_num

theorem mass60_dyadic_5 (k : ℕ) :
    oddCoreTruncatedMass (60*2^k) 5 =
      1-(1/4:ℚ)*(1/2:ℚ)^k := by
  apply dyadic_mass60_closed 5 (by norm_num) (by norm_num) (1/4) ?_ k
  rw [mass60_5]
  norm_num

theorem mass60_dyadic_15 (k : ℕ) :
    oddCoreTruncatedMass (60*2^k) 15 =
      1-(3/4:ℚ)*(1/2:ℚ)^k := by
  apply dyadic_mass60_closed 15 (by norm_num) (by norm_num) (3/4) ?_ k
  rw [mass60_15]
  norm_num

/-- For EVERY k, the concrete, original squarefree semiprime
C2 connected defect has this strictly negative expression.
No asymptotic guessing or numerical interval is used. -/
theorem dyadic_c2_connected_3_5_exact (k : ℕ) :
    c2OddCoreConnectedCumulant (60*2^k) 3 5 =
      -(3/8:ℚ)*(1/2:ℚ)^k -
        (1/32:ℚ)*(1/4:ℚ)^k := by
  unfold c2OddCoreConnectedCumulant
  rw [mass60_dyadic_3, mass60_dyadic_5, mass60_dyadic_15]
  have hhalf : (1/4:ℚ)^k = (1/2:ℚ)^k * (1/2:ℚ)^k := by
    conv_lhs => rw [show (1/4:ℚ)=(1/2)*(1/2) by norm_num]
    exact mul_pow _ _ k
  rw [hhalf]
  ring

theorem dyadic_c2_connected_3_5_strictly_negative (k : ℕ) :
    c2OddCoreConnectedCumulant (60*2^k) 3 5 < 0 := by
  rw [dyadic_c2_connected_3_5_exact]
  have hhalf : 0 < (1/2:ℚ)^k := by positivity
  have hquarter : 0 < (1/4:ℚ)^k := by positivity
  linarith

end CarryWheelNativeSignedGate
