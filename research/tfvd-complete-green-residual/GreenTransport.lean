import CompleteTfvd
import CriticalGreen

/-! Evaluate the original COMPLETE Green ledger through lossless TFVD
coordinates. The two arguments are independent, and the compensating phase
is kept. Division occurs only on the source-derived regular chart. -/
namespace CarryCompleteTfvd
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryNativePhase CarryMixedGreen CarryCompletedGreenBalance
open CarryMaterialResponseComparison Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def tfvdCompensatedGreen (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (t u : ℝ) : ℂ :=
  greenOnData eta h0 h1
    (pairEncode eta h0 h1 (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t)))
    (pairEncode eta h0 h1 (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair u))) +
  greenOnData eta h0 h1
    (pairEncode eta h0 h1 (carryMaterialPairReduction t (carryMaterialClockCompressedPair t)))
    (pairEncode eta h0 h1 (carryMaterialPairReduction u (carryMaterialClockCompressedPair u))) -
  greenOnData eta h0 h1
    (pairEncode eta h0 h1 (carryMaterialPairComplement (carryMaterialReducedCompanionPair t)))
    (pairEncode eta h0 h1 (carryMaterialPairComplement (carryMaterialReducedCompanionPair u))) +
  phaseNumerator t u

theorem tfvd_compensated_exact (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    tfvdCompensatedGreen eta h0 h1 = compensatedGreen := by
  funext t u
  simp only [tfvdCompensatedGreen, green_roundtrip, compensatedGreen, hiddenGreen]

/-- The TRUE confluent diagonal remains the one from the complete source. -/
theorem tfvd_compensated_confluence (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U,
      Tendsto (fun u : ℝ => tfvdCompensatedGreen eta h0 h1 t u/((u-t:ℝ):ℂ))
        (nhdsWithin t ({t}ᶜ)) (nhds (compensatedCoefficient t t)) := by
  rw [tfvd_compensated_exact]
  exact compensated_diagonal_confluence

def tfvdMixedGreen (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (t u : ℝ) : ℂ :=
  greenOnData eta h0 h1
    (pairEncode eta h0 h1 (carryMaterialPairReduction t (carryMaterialClockCompressedPair t)))
    (pairEncode eta h0 h1 (carryMaterialPairReduction u (carryMaterialClockForcingPair u))) +
  greenOnData eta h0 h1
    (pairEncode eta h0 h1 (carryMaterialPairReduction t (carryMaterialClockForcingPair t)))
    (pairEncode eta h0 h1 (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)))

theorem tfvd_mixed_exact (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    tfvdMixedGreen eta h0 h1 = mixedForcingGreen := by
  funext t u
  simp only [tfvdMixedGreen, green_roundtrip, mixedForcingGreen]

/-- The literal original forcing/forcing Green term, both mixed terms,
central and compressed channels, hidden complement and the compensating
phase. Adding and subtracting the SAME phase leaves the source unchanged. -/
def tfvdWholeGreen (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (t u : ℝ) : ℂ :=
  tfvdCompensatedGreen eta h0 h1 t u + tfvdMixedGreen eta h0 h1 t u - phaseNumerator t u +
    greenOnData eta h0 h1
      (pairEncode eta h0 h1 (carryMaterialPairReduction t (carryMaterialClockForcingPair t)))
      (pairEncode eta h0 h1 (carryMaterialPairReduction u (carryMaterialClockForcingPair u)))

theorem tfvd_whole_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U,
      tfvdWholeGreen eta h0 h1 t u = ((u-t:ℝ):ℂ)*completedCoefficient t u := by
  obtain ⟨U,ho,hz,hc⟩ := compensated_source_factor
  refine ⟨U ∩ {t | carryMaterialClockForcingScalar t ≠ 0},
    ho.inter (isOpen_ne_fun forcing_scalar_continuous continuous_const),
    ⟨hz,forcing_scalar_zero_ne⟩,?_⟩
  intro t ht u hu
  have hm := mixed_confluent_numerator t u ht.2 hu.2
  have hf := carryMaterialForcingGreen_factor t u
  unfold tfvdWholeGreen
  rw [tfvd_compensated_exact, tfvd_mixed_exact, hc t ht.1 u hu.1, green_roundtrip]
  unfold compensatedCoefficient remainderCoefficient
  linear_combination hm+hf

/-- Exact equality with the CANONICAL residual, not an auxiliary positive
Gram. All literal original response factors and both parameter signs remain. -/
theorem tfvd_native_residual_regular (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U,
      t ≠ 0 → u ≠ 0 → u ≠ t → baseTwoCanonicalResponse t ≠ 0 → baseTwoCanonicalResponse u ≠ 0 →
      tfvdWholeGreen eta h0 h1 t u /
        (((u-t:ℝ):ℂ)*(2:ℂ)*((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*
          conj (baseTwoCanonicalResponse t)*baseTwoCanonicalResponse u) =
        (carryMaterialRealResidual t u:ℂ) := by
  obtain ⟨U,ho,hz,h⟩ := tfvd_whole_factor eta h0 h1
  refine ⟨U,ho,hz,?_⟩
  intro t ht u hu ht0 hu0 hne hFt hFu
  rw [h t ht u hu, completedCoefficient]
  have ha : (carryMaterialResponseScale:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr material_scale_pos.ne'
  have htc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
  have huc : (u:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0
  have hd : ((u-t:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hc : conj (baseTwoCanonicalResponse t) ≠ 0 := by simpa using hFt
  have hd' : (u:ℂ)-(t:ℂ) ≠ 0 := by simpa only [Complex.ofReal_sub] using hd
  push_cast
  field_simp

end
end CarryCompleteTfvd
