import AllOrderTfvdHeadMarginBootstrap
import Mathlib.Tactic

/-!
# A strictly limited sign NO-GO for the HEAD+TAIL ALGEBRA, not for Native C2.

The generic source Bezout polynomial identity is exact for ANY complete
formal characteristic C. Its exact four-term splitting by H+T=C alone
does NOT force a positive even pivot, even with C0>0 and both H and T
NONZERO. The actual geometrically defined completed native C=A*N is
NOT this toy source. All-order native positivity is not contradicted.

This guards against deriving the sign from "the tail is exact"
without USING any additional structural inequality of the true C2
source or of its signed physical Green/return channels.
-/

namespace CarryWheelNativeSignedGate

open CarrySourceBezout
open scoped BigOperators
noncomputable section

def toyCharacteristicCoefficient : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | _ => 0

def toyExactHead : ℕ → ℝ := fun n => toyCharacteristicCoefficient n / 2
def toyExactTail : ℕ → ℝ := fun n => toyCharacteristicCoefficient n / 2

theorem toyExactHead_add_tail_eq_complete :
    toyExactHead + toyExactTail = toyCharacteristicCoefficient := by
  funext n
  simp only [Pi.add_apply, toyExactHead, toyExactTail]
  ring

theorem toyExactHead_nonzero : toyExactHead 0 = 1/2 := by
  norm_num [toyExactHead, toyCharacteristicCoefficient]

theorem toyExactTail_nonzero : toyExactTail 0 = 1/2 := by
  norm_num [toyExactTail, toyCharacteristicCoefficient]

/-- Already the first EVEN scalar source Bezout pivot can be NEGATIVE,
for a completely exact split and c0=1. No fact about native F is used. -/
theorem toyCompleteEvenFirstPivot_negative :
    coefficientBlock (sourceKernel toyCharacteristicCoefficient false) 1 0 0 =
      (-1 : ℝ) := by
  norm_num [coefficientBlock, sourceKernel, toyCharacteristicCoefficient,
    bezout, sourceSeries, divided, right, PowerSeries.coeff_derivative]

/-- The SAME negative value is the sum of ALL FOUR exact head, tail and
crossed bilinear terms. Both head and tail are nonzero. The exactness
therefore preserves the preexisting sign rather than determining it. -/
theorem toyExactFourTerms_firstEven_is_negative :
    coefficientBlock
      (mixedSourceKernel toyExactHead toyExactHead false +
       mixedSourceKernel toyExactHead toyExactTail false +
       mixedSourceKernel toyExactTail toyExactHead false +
       mixedSourceKernel toyExactTail toyExactTail false) 1 0 0 =
      (-1 : ℝ) := by
  rw [← sourceKernel_head_tail toyExactHead toyExactTail false]
  rw [toyExactHead_add_tail_eq_complete]
  exact toyCompleteEvenFirstPivot_negative

end
end CarryWheelNativeSignedGate
