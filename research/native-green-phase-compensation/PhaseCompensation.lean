import PhaseJet
import CenteredMixed

/-! Exact compensation of the native phase, before division by u-t.
The same term is added and subtracted in the SAME complete Green ledger;
neither a physical state nor a signed channel is erased or made positive. -/
namespace CarryNativePhase
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryMixedGreen CarryCompletedGreenBalance Filter Topology
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def retainedWeight (t u : ℝ) : ℂ :=
  ((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*
    conj (carryMaterialClockForcingScalar t)*carryMaterialClockForcingScalar u

def phaseNumerator (t u : ℝ) : ℂ := retainedWeight t u*(valueRatio t-conj (valueRatio t))

/-- Canonical derivative value on the diagonal, not total-field 0/0. -/
def confluentRetained (t u : ℝ) : ℂ := retainedWeight t u*dslope valueRatio t u

def compensatedGreen (t u : ℝ) : ℂ :=
  carryMaterialPairGreen
      (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t))
      (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair u)) +
    carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
      (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) -
    hiddenGreen t u + phaseNumerator t u

/-- The extension is fixed by the ORIGINAL complete residual coefficient.
It has no sign hypothesis and is not a new metric or a replacement Gram. -/
def compensatedCoefficient (t u : ℝ) : ℂ :=
  remainderCoefficient t u - companionCoefficient t u - confluentRetained t u

theorem mixed_confluent_numerator (t u : ℝ)
    (ht : carryMaterialClockForcingScalar t ≠ 0)
    (hu : carryMaterialClockForcingScalar u ≠ 0) :
    mixedForcingGreen t u = ((u-t:ℝ):ℂ)*
      (companionCoefficient t u+confluentRetained t u) + phaseNumerator t u := by
  have hd := sub_smul_dslope valueRatio t u
  simp only [Complex.real_smul] at hd
  rw [mixed_forcing_exact, retained_cross_ratio t u ht hu]
  unfold companionCoefficient confluentRetained phaseNumerator retainedWeight
  push_cast at hd ⊢
  linear_combination -((carryMaterialResponseScale:ℂ)^2*(t:ℂ)*(u:ℂ)*
    conj (carryMaterialClockForcingScalar t)*carryMaterialClockForcingScalar u)*hd

/-- Both ordered crosses and the whole hidden/central/compressed group
are present. The factorization also holds at t=u, before any quotient. -/
theorem compensated_source_factor :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U,
      compensatedGreen t u = ((u-t:ℝ):ℂ)*compensatedCoefficient t u := by
  obtain ⟨U,ho,h0,h⟩ := complete_mixed_hidden_factor
  refine ⟨U ∩ {t | carryMaterialClockForcingScalar t ≠ 0},
    ho.inter (isOpen_ne_fun forcing_scalar_continuous continuous_const),
    ⟨h0,forcing_scalar_zero_ne⟩,?_⟩
  intro t ht u hu
  have he := h t ht.1 u hu.1
  unfold mixedHiddenGreen at he
  rw [mixed_confluent_numerator t u ht.2 hu.2] at he
  unfold compensatedGreen compensatedCoefficient
  linear_combination he

theorem compensated_source_regular :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U, u ≠ t →
      compensatedGreen t u / ((u-t:ℝ):ℂ) = compensatedCoefficient t u := by
  obtain ⟨U,ho,h0,h⟩ := compensated_source_factor
  refine ⟨U,ho,h0,?_⟩
  intro t ht u hu hn
  rw [h t ht u hu]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hn))

/-- Exact location of the phase residue in the original physical channels. -/
theorem native_phase_diagonal_compensation :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U,
      phaseNumerator t t = hiddenGreen t t -
        carryMaterialPairGreen
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t))
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t)) -
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
          (carryMaterialPairReduction t (carryMaterialClockCompressedPair t)) := by
  obtain ⟨U,ho,h0,h⟩ := compensated_source_factor
  refine ⟨U,ho,h0,?_⟩
  intro t ht
  have he := h t ht t ht
  simp only [sub_self, Complex.ofReal_zero, zero_mul] at he
  unfold compensatedGreen at he
  linear_combination he

theorem phase_residue_fourth_order :
    Tendsto (fun t : ℝ => phaseNumerator t t/(t:ℂ)^4)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds ((carryMaterialResponseScale:ℂ)^2*
        conj (carryMaterialClockForcingScalar 0)*carryMaterialClockForcingScalar 0*
          (phaseCoefficient-conj phaseCoefficient))) := by
  have hf := forcing_scalar_continuous.tendsto 0
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp hf
  have hw := ((hc.mul hf).const_mul ((carryMaterialResponseScale:ℂ)^2)).mono_left
    (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  have hs := hw.mul phase_quadratic_tendsto
  simp only [mul_assoc] at hs ⊢
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by simpa using ht)
  unfold phaseNumerator retainedWeight
  simp only [Function.comp_def, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

end
end CarryNativePhase
