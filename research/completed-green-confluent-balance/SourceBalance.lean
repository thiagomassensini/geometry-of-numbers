import GeometryOfNumbers.Analysis.CarryMaterialForcingGreenEnergy
import CanonicalComparison

/-! Exact physical forcing compensation. The coefficients below are source
observations of the existing Green ledger; they are not a new positive Gram,
and neither positivity nor a target moment matrix is used to define them. -/
namespace CarryCompletedGreenBalance
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialResponseComparison CarryMaterialGreenPairComparison
open CarryMaterialClockCouplingComparison CarryMaterialMixedSchurComparison
open CarryMaterialPositiveResidualComparison
open CarrySelfAdjointOperator Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The literal coefficient of (u-t) in the complete physical residual ledger. -/
def completedCoefficient (t u : ℝ) : ℂ :=
  (2 : ℂ)*((carryMaterialResponseScale^2*t*u : ℝ) : ℂ)*
    conj (baseTwoCanonicalResponse t)*baseTwoCanonicalResponse u*
      (carryMaterialRealResidual t u : ℂ)

/-- Coefficient of the remaining physical Green channels after isolating
forcing/forcing. The next theorem identifies its entire physical numerator. -/
def remainderCoefficient (t u : ℝ) : ℂ :=
  completedCoefficient t u - carryMaterialForcingGreenKernel t u

theorem physical_remainder_factor :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U,
      carryMaterialForcingRemainderGreen t u =
        ((u-t : ℝ) : ℂ)*remainderCoefficient t u := by
  obtain ⟨U,ho,h0,h⟩ := material_clock_real_residual_numerator
  refine ⟨U,ho,h0,?_⟩
  intro t ht u hu
  have hs := h t ht u hu
  have hl := carryMaterialForcingRemainder_ledger t u
  rw [← carryMaterialClock_reduced_green_ledger] at hs
  unfold remainderCoefficient completedCoefficient
  linear_combination hs-hl

theorem physical_remainder_regular :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U, u ≠ t →
      carryMaterialForcingRemainderGreen t u / ((u-t : ℝ) : ℂ) =
        remainderCoefficient t u := by
  obtain ⟨U,ho,h0,h⟩ := physical_remainder_factor
  refine ⟨U,ho,h0,?_⟩
  intro t ht u hu hne
  rw [h t ht u hu]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne))

theorem source_forcing_energy {n : ℕ} (c : Fin n → ℂ) (t : Fin n → ℝ) :
    (∑ i, ∑ j, conj (c i)*carryMaterialForcingGreenKernel (t i) (t j)*c j).re =
      -canonicalCompletedNativeLogDerivativeMoment 0 *
        ‖∑ i, c i • carryMaterialForcingVector (t i)‖^2 := by
  rw [carryMaterialForcingGreen_energy, material_scale_eq]

theorem source_forcing_origin_neg : (carryMaterialForcingGreenKernel 0 0).re < 0 :=
  carryMaterialForcingGreen_origin_neg material_scale_pos

theorem remainder_zero_left (u : ℝ) :
    remainderCoefficient 0 u = -carryMaterialForcingGreenKernel 0 u := by
  simp [remainderCoefficient, completedCoefficient]

theorem remainder_zero_right (t : ℝ) :
    remainderCoefficient t 0 = -carryMaterialForcingGreenKernel t 0 := by
  simp [remainderCoefficient, completedCoefficient]

theorem remainder_origin_pos : 0 < (remainderCoefficient 0 0).re := by
  rw [remainder_zero_left, Complex.neg_re]
  exact neg_pos.mpr source_forcing_origin_neg

/-- The old central cancellation fixes a whole physical row, including its
forcing coefficient; no zero is silently substituted for a vector or a limit. -/
theorem physical_remainder_zero_row (u : ℝ) :
    carryMaterialForcingRemainderGreen 0 u =
      -(u : ℂ)*carryMaterialForcingGreenKernel 0 u := by
  have h := carryMaterialPairGreen_readout_ledger
    (carryMaterialReducedCompanionPair 0) (carryMaterialReducedCompanionPair u)
  rw [material_reduced_pair_center_invisible_nonzero.1] at h
  simp only [carryMaterialPairGreen, Prod.fst_zero, Prod.snd_zero,
    inner_zero_left, sub_self, mul_zero, zero_add] at h
  change carryMaterialPairGreen (carryMaterialReducedCompanionPair 0) (carryMaterialReducedCompanionPair u) =
    carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair 0))
      (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) at h
  have hl := carryMaterialForcingRemainder_ledger 0 u
  rw [h] at hl
  simp only [sub_self, sub_zero] at hl
  linear_combination -hl

/-- This diagonal is the actual punctured limit of the physical quotient.
Only continuity of the existing forcing channel is needed, not Dom(L^r). -/
theorem physical_remainder_origin_limit :
    Tendsto (fun u : ℝ => carryMaterialForcingRemainderGreen 0 u / (u : ℂ))
      (nhdsWithin 0 ({0}ᶜ)) (nhds (remainderCoefficient 0 0)) := by
  have hc : Continuous (fun u : ℝ => -carryMaterialForcingGreenKernel 0 u) :=
    (carryMaterialForcingGreen_continuous.comp (continuous_const.prodMk continuous_id)).neg
  rw [remainder_zero_left]
  apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hn : u ≠ 0 := by simpa using hu
  rw [physical_remainder_zero_row]
  field_simp [Complex.ofReal_ne_zero.mpr hn]

/-- The explicit negative forcing channel is EXACTLY the central Schur
subtraction of the remaining physical coefficient. This is an identity,
not a claim that the remaining coefficient is positive. -/
theorem physical_forcing_schur (t u : ℝ) :
    remainderCoefficient t u -
      remainderCoefficient t 0 * remainderCoefficient 0 u / remainderCoefficient 0 0 =
        completedCoefficient t u := by
  have hn : carryMaterialForcingGreenKernel 0 0 ≠ 0 := by
    intro hz
    have h := source_forcing_origin_neg
    rw [hz, Complex.zero_re] at h
    exact (lt_irrefl _ h)
  rw [remainder_zero_right, remainder_zero_left, remainder_zero_left]
  unfold remainderCoefficient
  have hcross := carryMaterialForcingGreen_cross t u
  field_simp
  linear_combination -hcross

/-- Both quadratures and every off-diagonal survive in this finite energy.
The unknown sign is in completedCoefficient; the added square is explicit. -/
theorem physical_remainder_energy {n : ℕ} (c : Fin n → ℂ) (t : Fin n → ℝ) :
    (∑ i, ∑ j, conj (c i)*remainderCoefficient (t i) (t j)*c j).re =
      (∑ i, ∑ j, conj (c i)*completedCoefficient (t i) (t j)*c j).re +
        carryMaterialResponseScale * ‖∑ i, c i • carryMaterialForcingVector (t i)‖^2 := by
  simp only [remainderCoefficient, mul_sub, sub_mul, Finset.sum_sub_distrib, Complex.sub_re]
  rw [carryMaterialForcingGreen_energy]
  ring

/-- Literal congruence with the SAME source residual, for two independent
families. The response factors and both parameter signs are retained. -/
theorem completed_coefficient_bilinear {n m : ℕ} (c : Fin n → ℂ) (d : Fin m → ℂ)
    (t : Fin n → ℝ) (u : Fin m → ℝ) :
    (∑ i, ∑ j, conj (c i)*completedCoefficient (t i) (u j)*d j) =
      (2 : ℂ)*(carryMaterialResponseScale : ℂ)^2 *
        ∑ i, ∑ j, conj (c i*(t i : ℂ)*baseTwoCanonicalResponse (t i))*
          (carryMaterialRealResidual (t i) (u j) : ℂ)*
            (d j*(u j : ℂ)*baseTwoCanonicalResponse (u j)) := by
  simp only [completedCoefficient, map_mul, Complex.conj_ofReal, Complex.ofReal_mul,
    Complex.ofReal_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Low-order source regressions: the odd diagonal and the even central
Schur correction retain the exact canonical h1 and h2, including the cross. -/
theorem low_order_source_regression :
    carryMaterialResponseScale = canonicalCompletedNativeLogDerivativeMoment 0 ∧
    carryMaterialResidualJet 1 1 = canonicalCompletedNativeLogDerivativeMoment 1 ∧
    carryMaterialResidualJet 2 2 = canonicalCompletedNativeLogDerivativeMoment 2 -
      canonicalCompletedNativeLogDerivativeMoment 1^2/canonicalCompletedNativeLogDerivativeMoment 0 := by
  refine ⟨material_scale_eq, ?_, ?_⟩
  · simpa using material_residual_jet_odd_odd 0 0
  · simpa [pow_two] using
      material_residual_jet_even_even 1 1

end
end CarryCompletedGreenBalance
