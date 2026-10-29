import CriticalLedger
import CarrySelfAdjointOperator.CompletedNativeChiralCayleyHerglotz

/-! A two-point ledger of the ORIGINAL completed TFVD readouts.
No quotient of a head is used. The determinant identity is a transport law,
not a sign theorem and not an assertion of path independence of all cameras. -/
namespace CarryTfvdJoint
open CarrySelfAdjointOperator PhysicalSewing CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Full readouts from the enriched state, with both exact tails. -/
def value (M : ℕ) (z : ℂ) : ℂ :=
  (canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z)).valueReadout

def logJet (M : ℕ) (z : ℂ) : ℂ :=
  (canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z)).logJetReadout

/-- The original Xi and chart contribution; neither is dropped. -/
def completionResponse (z : ℂ) : ℂ :=
  nativeXiCompletionBoundaryCompanion z / nativeXiCompletionFactor z +
    Complex.I * deriv (cpChartFactor 3) (operatorHeightParameter z) /
      cpChartFactor 3 (operatorHeightParameter z)

/-- Two independent endpoints, before division or a real projection. -/
def jointNumerator (T L B : ℂ → ℂ) (a z : ℂ) : ℂ :=
  T a * T z * (B z - B a) + Complex.I * (T a * L z - L a * T z)

def numerator (M : ℕ) (a z : ℂ) : ℂ :=
  jointNumerator (value M) (logJet M) completionResponse a z

/-- Polynomial composition law, including zeros of any intermediate value.
The coefficients T are essential; raw determinants do not simply add. -/
theorem jointNumerator_cocycle (T L B : ℂ → ℂ) (a b c : ℂ) :
    T b * jointNumerator T L B a c =
      T c * jointNumerator T L B a b + T a * jointNumerator T L B b c := by
  unfold jointNumerator
  ring

theorem jointNumerator_self (T L B : ℂ → ℂ) (a : ℂ) :
    jointNumerator T L B a a = 0 := by
  unfold jointNumerator
  ring

theorem jointNumerator_swap (T L B : ℂ → ℂ) (a z : ℂ) :
    jointNumerator T L B z a = -jointNumerator T L B a z := by
  unfold jointNumerator
  ring

/-- The physical quotient difference, requiring only FULL denominators. -/
theorem jointNumerator_quotient (T L B : ℂ → ℂ) (a z : ℂ)
    (ha : T a ≠ 0) (hz : T z ≠ 0) :
    jointNumerator T L B a z = T a * T z *
      ((B z + Complex.I * L z / T z) - (B a + Complex.I * L a / T a)) := by
  unfold jointNumerator
  field_simp
  ring

theorem full_response (M : ℕ) (z : ℂ)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completionResponse z + Complex.I * logJet M z / value M z = originalResponse z := by
  have hd := tfvdCanonicalResponse_regular_denominators M z hs hF
  exact (tfvdStateResponse_threeChannels z
    (canonicalC3BracketTfvdCompletionState M (operatorHeightParameter z))
    hd.1 hd.2.1 hd.2.2).symm.trans (tfvdCanonicalResponse_eq_original M z hs hF)

/-- The same completed producer at two INDEPENDENT points. -/
theorem numerator_eq_full_difference (M : ℕ) (a z : ℂ)
    (ha : operatorHeightParameter a ∈ genuineCriticalStrip)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hFa : completedNativeOperatorCharacteristic a ≠ 0)
    (hFz : completedNativeOperatorCharacteristic z ≠ 0) :
    numerator M a z = value M a * value M z * (originalResponse z-originalResponse a) := by
  have hTa := (tfvdCanonicalResponse_regular_denominators M a ha hFa).2.2
  have hTz := (tfvdCanonicalResponse_regular_denominators M z hz hFz).2.2
  rw [numerator,jointNumerator_quotient (value M) (logJet M) completionResponse a z hTa hTz]
  rw [full_response M z hz hFz,full_response M a ha hFa]

/-- This is the actual cutoff invariance of the completed material readouts. -/
theorem readouts_cutoff_independent (M N : ℕ) (z : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    value M z = value N z ∧ logJet M z = logJet N z := by
  have hp : operatorHeightParameter z ∈ bracketHalfPlane := by
    change -1 < (operatorHeightParameter z).re
    linarith [hz.1]
  constructor
  · exact (canonicalC3BracketTfvdCompletionState_valueReadout_eq_completed M hp).trans
      (canonicalC3BracketTfvdCompletionState_valueReadout_eq_completed N hp).symm
  · exact (canonicalC3BracketTfvdCompletionState_logJetReadout_eq_completed M hp).trans
      (canonicalC3BracketTfvdCompletionState_logJetReadout_eq_completed N hp).symm

theorem numerator_cutoff_independent (M N : ℕ) (a z : ℂ)
    (ha : operatorHeightParameter a ∈ genuineCriticalStrip)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    numerator M a z = numerator N a z := by
  unfold numerator jointNumerator
  rw [(readouts_cutoff_independent M N a ha).1,
    (readouts_cutoff_independent M N a ha).2,
    (readouts_cutoff_independent M N z hz).1,
    (readouts_cutoff_independent M N z hz).2]

/-- Canonical composition without division by a finite head OR by the intermediate T. -/
theorem numerator_transport (M : ℕ) (a b c : ℂ) :
    value M b * numerator M a c =
      value M c * numerator M a b + value M a * numerator M b c :=
  jointNumerator_cocycle _ _ _ _ _ _

end
end CarryTfvdJoint
