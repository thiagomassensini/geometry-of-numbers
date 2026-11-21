import CarrySelfAdjointOperator.PrimeDepthTfvdLogJetCrosswalk
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Primitive prime-power resolution of the original C2 log legs

This module starts from the prime-depth material clock, not zeta.

The original prime-depth ledger is recovered by summing von Mangoldt
over its integer divisors. Consequently the C2 centered log difference is
EXACTLY the difference of the leg and center prime-power divisor sums.
The resulting bracket has negative sign: the logarithmic profile is
concave even though n^(-sigma) is convex for positive real sigma.

The sign of a scalar log bracket does NOT determine the signed quadratic
energy of the completed native F=A*N moments.
-/

namespace CarryWheelNativeSignedGate

open CarrySelfAdjointOperator

noncomputable section

/-- Material depth ledger equals divisor-wise accumulation of prime-power
Mangoldt atoms, for every positive integer, before analytic completion. -/
theorem primeDepthLogLedger_eq_mangoldt_divisorSum
    (n : ℕ) (hn : n ≠ 0) :
    primeDepthLogLedger n =
      ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d := by
  calc
    primeDepthLogLedger n = Real.log n := primeDepthLogLedger_eq_log hn
    _ = ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d :=
      (ArithmeticFunction.vonMangoldt_sum (n := n)).symm

/-- Three positional legs/centers from the original prime-depth logarithm.
This is not the sigma-dependent function n^(-s), nor completed F. -/
def c2PrimeDepthLogBalance (c : ℕ) : ℝ :=
  primeDepthLogLedger (c - 1) -
    2 * primeDepthLogLedger c + primeDepthLogLedger (c + 1)

/-- The same source rewritten using the primitive von Mangoldt prime-power
atoms. No truncation, spectral readout, or reweighted camera is involved. -/
def c2MangoldtLegCenterBalance (c : ℕ) : ℝ :=
  (∑ d ∈ (c-1).divisors, ArithmeticFunction.vonMangoldt d) -
  2 * (∑ d ∈ c.divisors, ArithmeticFunction.vonMangoldt d) +
  (∑ d ∈ (c+1).divisors, ArithmeticFunction.vonMangoldt d)

theorem c2PrimeDepthLogBalance_eq_mangoldt_resolution
    (c : ℕ) (hc : 2 ≤ c) :
    c2PrimeDepthLogBalance c = c2MangoldtLegCenterBalance c := by
  have hm : c - 1 ≠ 0 := by omega
  have hz : c ≠ 0 := by omega
  have hp : c + 1 ≠ 0 := by omega
  simp only [c2PrimeDepthLogBalance, c2MangoldtLegCenterBalance,
    primeDepthLogLedger_eq_mangoldt_divisorSum _ hm,
    primeDepthLogLedger_eq_mangoldt_divisorSum _ hz,
    primeDepthLogLedger_eq_mangoldt_divisorSum _ hp]

/-- The same C2 bracket is a difference of three ORDINARY real logarithms,
with no assumption on any completed-native characteristic. -/
def c2IntegerLogBalance (c : ℕ) : ℝ :=
  Real.log (c-1) - 2 * Real.log c + Real.log (c+1)

theorem c2PrimeDepthLogBalance_eq_integerLog (c : ℕ) (hc : 2 ≤ c) :
    c2PrimeDepthLogBalance c = c2IntegerLogBalance c := by
  have hm : c - 1 ≠ 0 := by omega
  have hz : c ≠ 0 := by omega
  have hp : c + 1 ≠ 0 := by omega
  simp only [c2PrimeDepthLogBalance,c2IntegerLogBalance,
    primeDepthLogLedger_eq_log hm,primeDepthLogLedger_eq_log hz,
    primeDepthLogLedger_eq_log hp, Nat.cast_sub (show 1 ≤ c by omega),
    Nat.cast_add, Nat.cast_one]

/-- Local concavity changes the sign of the WHOLE centered log bracket.
In particular, positivity of the formal legs is NOT positivity of
this logarithmic channel. -/
theorem c2IntegerLogBalance_neg (c : ℕ) (hc : 2 ≤ c) :
    c2IntegerLogBalance c < 0 := by
  have hcast : (c : ℝ) - 1 = ((c-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ c by omega)]
    norm_num
  have hpcast : ((c+1:ℕ):ℝ) = (c:ℝ)+1 := by push_cast; ring
  have hcx : (1 : ℝ) < c := by exact_mod_cast (show 1 < c by omega)
  let x : ℝ := c
  have hm : 0 < x-1 := by dsimp [x]; linarith
  have hx : 0 < x := by dsimp [x]; linarith
  have hp : 0 < x+1 := by dsimp [x]; linarith
  have hmul : (x-1)*(x+1) < x^2 := by nlinarith
  have hlog := Real.log_lt_log (mul_pos hm hp) hmul
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt hp), Real.log_pow] at hlog
  unfold c2IntegerLogBalance
  dsimp [x] at hlog
  linarith

/-- The full prime-power divisor resolution inherits the strict NEGATIVE
sign of the log C2 bracket (the scalar channel, not a moment Gram). -/
theorem c2MangoldtLegCenterBalance_neg (c : ℕ) (hc : 2 ≤ c) :
    c2MangoldtLegCenterBalance c < 0 := by
  rw [← c2PrimeDepthLogBalance_eq_mangoldt_resolution c hc,
    c2PrimeDepthLogBalance_eq_integerLog c hc]
  exact c2IntegerLogBalance_neg c hc

/-- The real positive inverse-power material profile, unlike log n, has
POSITIVE C2 curvature, already visible exactly at the finite witness 5. -/
theorem c2_inverse_power_at_five_pos :
    (1/(4:ℚ) - 2/(5:ℚ) + 1/(6:ℚ)) = 1/60 := by norm_num

end
end CarryWheelNativeSignedGate
