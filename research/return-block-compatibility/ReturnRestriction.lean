import CanonicalBlock
import CarrySelfAdjointOperator.CompletedNativeChiralReturnArbitraryOrder
import Mathlib.LinearAlgebra.Isomorphisms

namespace CarryReturnCompatibility
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCorrectedGreenPorts
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Literal inclusion of source-generated incident spaces, before norms. -/
theorem incidentSpan_mono (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    RadialIncidentSpan k N ≤ RadialIncidentSpan k M := by
  rintro x ⟨c,rfl⟩
  exact ⟨radialSourcePad h c, radialIncidentSynthesis_pad k h c⟩

def incidentInclusion (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    RadialIncidentSpan k N →ₗᵢ[ℂ] RadialIncidentSpan k M where
  toLinearMap := Submodule.inclusion (incidentSpan_mono k h)
  norm_map' _ := rfl

theorem incidentInclusion_source (k : ℕ) {N M : ℕ} (h : N ≤ M) (c : Fin N → ℂ) :
    incidentInclusion k h (radialIncidentVector k N c) =
      radialIncidentVector k M (radialSourcePad h c) := by
  apply Subtype.ext
  exact (radialIncidentSynthesis_pad k h c).symm

/-- Exact operator restriction, not merely a diagonal storage comparison. -/
theorem return_restriction (k : ℕ) {N M : ℕ} (h : N ≤ M) (x : RadialIncidentSpan k N) :
    radialReturnTransfer k M (incidentInclusion k h x) = radialReturnTransfer k N x := by
  obtain ⟨c,rfl⟩ := (radialIncidentCoordinates k N).symm.surjective x
  change radialReturnTransfer k M (incidentInclusion k h (radialIncidentVector k N c)) =
    radialReturnTransfer k N (radialIncidentVector k N c)
  rw [incidentInclusion_source, radialReturnTransfer_exact, radialReturnTransfer_exact,
    radialReturnedSynthesis_pad]

/-- Compression law for the actual return defect, with two independent
source vectors. No sign, moment identity or square-root naturality is used. -/
theorem defect_compression_pairing (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x y : RadialIncidentSpan k N) :
    inner ℂ (incidentInclusion k h x)
      (radialReturnEnergyDefect k M (incidentInclusion k h y)) =
        inner ℂ x (radialReturnEnergyDefect k N y) := by
  rw [radialReturnEnergyDefect_pairing, radialReturnEnergyDefect_pairing,
    return_restriction, return_restriction, (incidentInclusion k h).inner_map_map]

/-- ALL sizes, without any sign hypothesis: the difference of the actual
positive/negative Jordan pairings is compatible. Neither channel is erased. -/
theorem jordanPorts_prefix_pairing (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x y : RadialIncidentSpan k N) :
    inner ℂ (radialReturnJordanPositivePort k M (incidentInclusion k h x))
        (radialReturnJordanPositivePort k M (incidentInclusion k h y)) -
      inner ℂ (radialReturnJordanNegativePort k M (incidentInclusion k h x))
        (radialReturnJordanNegativePort k M (incidentInclusion k h y)) =
      inner ℂ (radialReturnJordanPositivePort k N x) (radialReturnJordanPositivePort k N y) -
        inner ℂ (radialReturnJordanNegativePort k N x) (radialReturnJordanNegativePort k N y) := by
  rw [radialReturnJordanPorts_pairing, radialReturnJordanPorts_pairing,
    return_restriction, return_restriction, (incidentInclusion k h).inner_map_map]

/-- Both square-root ports have the SAME Gram on the common original input.
The vectors are not asserted equal in their ambient Cauchy coordinates. -/
theorem energyPort_prefix_pairing (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (hM : ‖radialReturnTransfer k M‖ ≤ 1) (x y : RadialIncidentSpan k N) :
    inner ℂ (radialReturnEnergyPort k M (incidentInclusion k h x))
      (radialReturnEnergyPort k M (incidentInclusion k h y)) =
        inner ℂ (radialReturnEnergyPort k N x) (radialReturnEnergyPort k N y) := by
  rw [radialReturnEnergyPort_inner k M hM,
    radialReturnEnergyPort_inner k N (radialReturnTransfer_norm_le_one_of_prefix k h hM),
    return_restriction, return_restriction, (incidentInclusion k h).inner_map_map]

/-- The size of the discarded part of the return is zero, with provenance
at vector level; the square-root defect still has its own ambient rotation. -/
theorem return_prefix_distance_zero (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : RadialIncidentSpan k N) :
    ‖radialReturnTransfer k M (incidentInclusion k h x)-radialReturnTransfer k N x‖ = 0 := by
  rw [return_restriction, sub_self, norm_zero]

/-- The same physical return norm is monotone under enlargement. This only
propagates an upper bound DOWNWARD; it cannot certify a new source channel. -/
theorem return_opNorm_mono (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    ‖radialReturnTransfer k N‖ ≤ ‖radialReturnTransfer k M‖ := by
  apply (radialReturnTransfer k N).opNorm_le_bound (norm_nonneg (radialReturnTransfer k M))
  intro x
  rw [← return_restriction k h x]
  calc
    _ ≤ ‖radialReturnTransfer k M‖ * ‖incidentInclusion k h x‖ :=
      (radialReturnTransfer k M).le_opNorm _
    _ = _ := by rw [(incidentInclusion k h).norm_map]

end
end CarryReturnCompatibility
