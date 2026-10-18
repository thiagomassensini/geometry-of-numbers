import GeometryOfNumbers.Analysis.CarryMaterialClockCentralCoupling

/-! The already constructed physical forcing channel after projective reduction.
The kernel below is the exact coefficient of (u-t), including its diagonal;
it changes neither source nor metric. Its sign is opposite to the source scale.
All-family energy is computed before dropping any complex quadrature. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The first slot of the EXISTING physical forcing pair. -/
def carryMaterialForcingVector (t : ℝ) : MaterialCarrier :=
  (carryMaterialClockForcingPair t).1

/-- Exact confluent coefficient of the reduced forcing/forcing Green term. -/
def carryMaterialForcingGreenKernel (t u : ℝ) : ℂ :=
  -(carryMaterialResponseScale : ℂ) *
    inner ℂ (carryMaterialForcingVector t) (carryMaterialForcingVector u)

theorem carryMaterialForcingVector_origin_ne_zero : carryMaterialForcingVector 0 ≠ 0 := by
  change carryMaterialClockForcingScalar 0 • carryMaterialClockCentralForcing ≠ 0
  apply smul_ne_zero
  · rw [carryMaterialClockForcingScalar, carryMaterialClock_central_coefficient_zero, mul_one]
    exact mul_ne_zero Complex.I_ne_zero (baseTwoCanonicalDressingScalar_ne_zero 0)
  · exact carryMaterialClock_forcing_nonzero

theorem carryMaterialForcingGreen_factor (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
      (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) =
      ((u-t : ℝ) : ℂ) * carryMaterialForcingGreenKernel t u := by
  rw [carryMaterialClock_reduced_forcing_green]
  simp only [carryMaterialForcingGreenKernel, carryMaterialForcingVector,
    carryMaterialClockForcingPair, inner_smul_left, inner_smul_right, Complex.ofReal_mul]
  ring

theorem carryMaterialForcingGreen_regular (t u : ℝ) (hne : u ≠ t) :
    carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
        (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) / ((u-t : ℝ) : ℂ) =
      carryMaterialForcingGreenKernel t u := by
  rw [carryMaterialForcingGreen_factor]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne))

theorem carryMaterialForcingGreen_diagonal (t : ℝ) :
    (carryMaterialForcingGreenKernel t t).re =
      -carryMaterialResponseScale * ‖carryMaterialForcingVector t‖^2 := by
  simp only [carryMaterialForcingGreenKernel, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero,
    inner_self_eq_norm_sq_to_K]
  norm_cast

theorem carryMaterialForcingGreen_bilinear {n m : ℕ}
    (c : Fin n → ℂ) (d : Fin m → ℂ) (t : Fin n → ℝ) (u : Fin m → ℝ) :
    (∑ i, ∑ j, conj (c i)*carryMaterialForcingGreenKernel (t i) (u j)*d j) =
      -(carryMaterialResponseScale : ℂ) *
        inner ℂ (∑ i, c i • carryMaterialForcingVector (t i))
          (∑ j, d j • carryMaterialForcingVector (u j)) := by
  simp only [carryMaterialForcingGreenKernel, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem carryMaterialForcingGreen_energy {n : ℕ}
    (c : Fin n → ℂ) (t : Fin n → ℝ) :
    (∑ i, ∑ j, conj (c i)*carryMaterialForcingGreenKernel (t i) (t j)*c j).re =
      -carryMaterialResponseScale * ‖∑ i, c i • carryMaterialForcingVector (t i)‖^2 := by
  rw [carryMaterialForcingGreen_bilinear]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem carryMaterialForcingGreen_energy_nonpos (ha : 0 ≤ carryMaterialResponseScale)
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → ℝ) :
    (∑ i, ∑ j, conj (c i)*carryMaterialForcingGreenKernel (t i) (t j)*c j).re ≤ 0 := by
  rw [carryMaterialForcingGreen_energy]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _)

theorem carryMaterialForcingGreen_origin_neg (ha : 0 < carryMaterialResponseScale) :
    (carryMaterialForcingGreenKernel 0 0).re < 0 := by
  rw [carryMaterialForcingGreen_diagonal]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos ha)
    (sq_pos_of_pos (norm_pos_iff.mpr carryMaterialForcingVector_origin_ne_zero))

/-- No sign is postulated: the whole channel is a single literal outer product. -/
theorem carryMaterialForcingGreen_rank_one (t u : ℝ) :
    carryMaterialForcingGreenKernel t u =
      -(carryMaterialResponseScale : ℂ) *
        conj (carryMaterialClockForcingScalar t)*carryMaterialClockForcingScalar u *
          inner ℂ carryMaterialClockCentralForcing carryMaterialClockCentralForcing := by
  simp only [carryMaterialForcingGreenKernel, carryMaterialForcingVector,
    carryMaterialClockForcingPair, inner_smul_left, inner_smul_right]
  ring

theorem carryMaterialForcingGreen_cross (t u : ℝ) :
    carryMaterialForcingGreenKernel t u * carryMaterialForcingGreenKernel 0 0 =
      carryMaterialForcingGreenKernel t 0 * carryMaterialForcingGreenKernel 0 u := by
  simp only [carryMaterialForcingGreen_rank_one]
  ring

/-- The four remaining physical Green channels, with the hidden readout
complement still subtracted. No sign is assigned to this remainder. -/
def carryMaterialForcingRemainderGreen (t u : ℝ) : ℂ :=
  carryMaterialPairGreen
      (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t))
      (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair u)) +
    carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
      (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) +
    carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
      (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) +
    carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
      (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) -
    carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
      (carryMaterialPairComplement (carryMaterialReducedCompanionPair u))

theorem carryMaterialForcingRemainder_ledger (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u) -
      carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
        (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) =
      carryMaterialForcingRemainderGreen t u +
        ((u-t : ℝ) : ℂ)*carryMaterialForcingGreenKernel t u := by
  rw [carryMaterialClock_reduced_green_ledger, carryMaterialForcingGreen_factor]
  unfold carryMaterialForcingRemainderGreen
  ring

/-- The factor has a continuous diagonal, independent of higher clock domains. -/
theorem carryMaterialForcingGreen_continuous :
    Continuous (fun p : ℝ × ℝ => carryMaterialForcingGreenKernel p.1 p.2) := by
  have hY : Continuous baseTwoCompletedBoundaryHilbertState :=
    continuous_iff_continuousAt.mpr (fun t =>
      (completedBoundaryState_hasDerivAt_clock t).continuousAt)
  have hD : Continuous baseTwoCanonicalDressingScalar :=
    continuous_iff_continuousAt.mpr (fun t =>
      (baseTwoCanonicalDressingScalar_analyticAt t).continuousAt)
  have hf : Continuous carryMaterialClockForcingScalar :=
    (continuous_const.mul hD).mul (carryMaterialClockCentralCoefficient.continuous.comp hY)
  have hv : Continuous carryMaterialForcingVector :=
    hf.smul continuous_const
  exact continuous_const.mul ((hv.comp continuous_fst).inner (hv.comp continuous_snd))

end
end GeometryOfNumbers.Analysis
