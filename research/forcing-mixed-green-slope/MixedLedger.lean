import RetainedLeg

/-! The two ordered forcing crosses in the original Green quotient.
The scalar probes below are taken only AFTER the complete compressed pair
and the hidden companion have been constructed. No source is replaced. -/
namespace CarryMixedGreen
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryCompletedGreenBalance
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

def companionProbe (t : ℝ) : ℂ :=
  inner ℂ carryMaterialClockCentralForcing (carryMaterialClockCompressedPair t).1

def valueProbe (t : ℝ) : ℂ :=
  inner ℂ carryMaterialClockCentralForcing (carryMaterialClockCompressedPair t).2

def mixedForcingGreen (t u : ℝ) : ℂ :=
  carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
    (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) +
  carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
    (carryMaterialPairReduction u (carryMaterialClockCompressedPair u))

def hiddenGreen (t u : ℝ) : ℂ :=
  carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
    (carryMaterialPairComplement (carryMaterialReducedCompanionPair u))

def mixedHiddenGreen (t u : ℝ) : ℂ := mixedForcingGreen t u - hiddenGreen t u

/-- Both legs are expanded together; the t*u term is the retained forcing
leg, and cannot be recovered from the forcing coefficient Gram alone. -/
theorem mixed_forcing_exact (t u : ℝ) :
    mixedForcingGreen t u =
      -((carryMaterialResponseScale*(u-t):ℝ):ℂ)*
        (conj (carryMaterialClockForcingScalar t)*companionProbe u +
          conj (companionProbe t)*carryMaterialClockForcingScalar u) +
      ((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*
        (conj (valueProbe t)*carryMaterialClockForcingScalar u -
          conj (carryMaterialClockForcingScalar t)*valueProbe u) := by
  unfold mixedForcingGreen
  rw [carryMaterialPairReduction_green, carryMaterialPairReduction_green]
  simp only [carryMaterialPairGreen, carryMaterialClockForcingPair,
    inner_zero_left, inner_zero_right, zero_sub, sub_zero,
    inner_smul_left, inner_smul_right, companionProbe, valueProbe, inner_conj_symm]
  push_cast
  ring

/-- The ONLY division here is the original Green divided difference. -/
theorem mixed_hidden_regular (t u : ℝ) (hne : u ≠ t) :
    mixedHiddenGreen t u / ((u-t:ℝ):ℂ) =
      -(carryMaterialResponseScale:ℂ)*
        (conj (carryMaterialClockForcingScalar t)*companionProbe u +
          conj (companionProbe t)*carryMaterialClockForcingScalar u) +
      ((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*
        ((conj (valueProbe t)*carryMaterialClockForcingScalar u -
          conj (carryMaterialClockForcingScalar t)*valueProbe u)/((u-t:ℝ):ℂ)) -
      hiddenGreen t u / ((u-t:ℝ):ℂ) := by
  rw [mixedHiddenGreen, mixed_forcing_exact]
  have hn : ((u-t:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hn' : (u:ℂ)-(t:ℂ) ≠ 0 := by simpa using hn
  push_cast
  field_simp [hn']

/-- Exact source observation chart. It does not alter a physical vector,
metric, dressing or the coefficients in the Green identity. -/
def valueRatio (t : ℝ) : ℂ := -valueProbe t / carryMaterialClockForcingScalar t

theorem retained_cross_ratio (t u : ℝ)
    (ht : carryMaterialClockForcingScalar t ≠ 0)
    (hu : carryMaterialClockForcingScalar u ≠ 0) :
    conj (valueProbe t)*carryMaterialClockForcingScalar u -
      conj (carryMaterialClockForcingScalar t)*valueProbe u =
    conj (carryMaterialClockForcingScalar t)*carryMaterialClockForcingScalar u*
      (valueRatio u - conj (valueRatio t)) := by
  simp only [valueRatio, map_div₀, map_neg]
  have hc : conj (carryMaterialClockForcingScalar t) ≠ 0 := by simpa using ht
  field_simp
  ring

/-- The conjugation defect is explicit. Replacing this by an ordinary
Loewner divided difference would silently discard the second quadrature. -/
theorem retained_cross_phase_split (t u : ℝ) :
    valueRatio u - conj (valueRatio t) =
      (valueRatio u - valueRatio t) + (valueRatio t - conj (valueRatio t)) := by ring

/-- The full physical remainder still needs both of these compensators. -/
theorem complete_mixed_hidden_factor :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U,
      mixedHiddenGreen t u +
        carryMaterialPairGreen
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t))
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair u)) +
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
          (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) =
      ((u-t:ℝ):ℂ)*remainderCoefficient t u := by
  obtain ⟨U,ho,h0,h⟩ := physical_remainder_factor
  refine ⟨U,ho,h0,?_⟩
  intro t ht u hu
  have he := h t ht u hu
  unfold carryMaterialForcingRemainderGreen at he
  unfold mixedHiddenGreen mixedForcingGreen hiddenGreen
  linear_combination he

/-- Confluence is guaranteed for the COMPLETE numerator. This identity
does not assert that the mixed/hidden group is separately divisible. -/
theorem diagonal_compensation :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U,
      mixedHiddenGreen t t =
        -carryMaterialPairGreen
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t))
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t)) -
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
          (carryMaterialPairReduction t (carryMaterialClockCompressedPair t)) := by
  obtain ⟨U,ho,h0,h⟩ := complete_mixed_hidden_factor
  refine ⟨U,ho,h0,?_⟩
  intro t ht
  have he := h t ht t ht
  simp only [sub_self, Complex.ofReal_zero, zero_mul] at he
  linear_combination he

end
end CarryMixedGreen
