import ForcingCenter

namespace CarryForcingResidual
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCompletedGreenBalance CarryMaterialClockCouplingComparison
open CarryMaterialGreenPairComparison CarryMaterialResponseComparison
open CarrySelfAdjointOperator Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem material_inner_self_re (x : MaterialCarrier) : (inner ℂ x x).re = ‖x‖^2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

/-- The SAME source-dependent centering, on the actual two-legged forcing
pair. Its second slot is not removed when the coefficient Gram vanishes. -/
def centeredForcingPair (t : ℝ) : MaterialCarrier × MaterialCarrier :=
  carryMaterialPairReduction t (carryMaterialClockForcingPair t)-
    (carryMaterialClockForcingScalar t/carryMaterialClockForcingScalar 0) •
      carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0)

theorem centeredForcingPair_as_synthesis (t : ℝ) :
    centeredForcingPair t = ∑ i : Fin 2,
      centeredCoefficients (fun _ : Fin 1 => (1:ℂ)) (fun _ => t) i •
        carryMaterialPairReduction (centeredParameters (fun _ : Fin 1 => t) i)
          (carryMaterialClockForcingPair (centeredParameters (fun _ : Fin 1 => t) i)) := by
  simp [centeredForcingPair, centeredCoefficients, centeredParameters, Fin.sum_univ_two,
    neg_div, sub_eq_add_neg, add_comm]

theorem centeredForcingPair_exact (t : ℝ) :
    centeredForcingPair t = (0,
      ((carryMaterialResponseScale*t:ℝ):ℂ) • carryMaterialForcingVector t) := by
  apply Prod.ext
  · dsimp only [centeredForcingPair, carryMaterialPairReduction, LinearMap.coe_mk,
      AddHom.coe_mk, carryMaterialClockForcingPair]
    simp only [mul_zero, Complex.ofReal_zero, smul_zero, sub_zero]
    change carryMaterialClockForcingScalar t • carryMaterialClockCentralForcing-
      (carryMaterialClockForcingScalar t/carryMaterialClockForcingScalar 0) •
        (carryMaterialClockForcingScalar 0 • carryMaterialClockCentralForcing) = 0
    rw [smul_smul, div_mul_cancel₀ _ forcing_scalar_zero_ne, sub_self]
  · simp [centeredForcingPair, carryMaterialPairReduction, carryMaterialClockForcingPair,
      carryMaterialForcingVector]

/-- Native isotropy is not a zero state; the actual second leg remains. -/
theorem centeredForcingPair_ne_zero (t : ℝ) (ht : t ≠ 0)
    (hf : carryMaterialClockForcingScalar t ≠ 0) : centeredForcingPair t ≠ 0 := by
  rw [centeredForcingPair_exact]
  intro h
  have hs := congrArg Prod.snd h
  change (((carryMaterialResponseScale*t:ℝ):ℂ) •
    (carryMaterialClockForcingScalar t • carryMaterialClockCentralForcing)) = 0 at hs
  have ha : ((carryMaterialResponseScale*t:ℝ):ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero material_scale_pos.ne' ht
  exact (smul_ne_zero ha (smul_ne_zero hf carryMaterialClock_forcing_nonzero)) hs

theorem centeredForcingPair_self_green (t : ℝ) :
    carryMaterialPairGreen (centeredForcingPair t) (centeredForcingPair t) = 0 := by
  simp [centeredForcingPair_exact, carryMaterialPairGreen]

theorem centeredForcingPair_polarized_green (t u : ℝ) :
    carryMaterialPairGreen (centeredForcingPair t) (centeredForcingPair u) = 0 := by
  simp [centeredForcingPair_exact, carryMaterialPairGreen]

/-- A mixed pairing with an ORIGINAL native forcing state still detects
the centered pair. No invented probe or adjusted Hilbert product is used. -/
theorem centeredForcingPair_native_cross (t : ℝ) :
    carryMaterialPairGreen (centeredForcingPair t)
      (carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0)) =
      ((carryMaterialResponseScale*t:ℝ):ℂ)*
        inner ℂ (carryMaterialForcingVector t) (carryMaterialForcingVector 0) := by
  rw [centeredForcingPair_exact]
  simp [carryMaterialPairGreen, carryMaterialPairReduction, carryMaterialClockForcingPair,
    carryMaterialForcingVector]
  ring

theorem forcing_scalar_continuous : Continuous carryMaterialClockForcingScalar := by
  have hY : Continuous baseTwoCompletedBoundaryHilbertState :=
    continuous_iff_continuousAt.mpr (fun t =>
      (completedBoundaryState_hasDerivAt_clock t).continuousAt)
  have hD : Continuous baseTwoCanonicalDressingScalar :=
    continuous_iff_continuousAt.mpr (fun t => (baseTwoCanonicalDressingScalar_analyticAt t).continuousAt)
  exact (continuous_const.mul hD).mul (carryMaterialClockCentralCoefficient.continuous.comp hY)

theorem forcing_vector_continuous : Continuous carryMaterialForcingVector := by
  change Continuous (fun t => carryMaterialClockForcingScalar t • carryMaterialClockCentralForcing)
  exact forcing_scalar_continuous.smul continuous_const

theorem centeredForcingPair_nonzero_near :
    ∀ᶠ t : ℝ in nhdsWithin 0 ({0}ᶜ), centeredForcingPair t ≠ 0 := by
  have hf := forcing_scalar_continuous.continuousAt.eventually_ne forcing_scalar_zero_ne
  filter_upwards [hf.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn
  exact centeredForcingPair_ne_zero t (by simpa using hn) ht

/-- The complete two-legged state has a nonzero first-order limit BEFORE
any norm or scalar Green readout is taken. -/
theorem retained_pair_tangent :
    Tendsto (fun t : ℝ => (t:ℂ)⁻¹ • centeredForcingPair t)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds ((0:MaterialCarrier), (carryMaterialResponseScale:ℂ) • carryMaterialForcingVector 0)) := by
  have hc : Continuous (fun t : ℝ => ((0:MaterialCarrier),
      (carryMaterialResponseScale:ℂ) • carryMaterialForcingVector t)) :=
    continuous_const.prodMk
      ((continuous_const : Continuous (fun _ : ℝ => (carryMaterialResponseScale:ℂ))).smul
        forcing_vector_continuous)
  apply ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by simpa using ht)
  simp [centeredForcingPair_exact, smul_smul, Complex.ofReal_mul, hn, mul_comm]

theorem retained_leg_energy (t : ℝ) : ‖(centeredForcingPair t).2‖^2 =
    (carryMaterialResponseScale*t)^2*‖carryMaterialForcingVector t‖^2 := by
  rw [centeredForcingPair_exact, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem retained_leg_energy_limit :
    Tendsto (fun t : ℝ => ‖(centeredForcingPair t).2‖^2/t^2)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (carryMaterialResponseScale^2*‖carryMaterialForcingVector 0‖^2)) := by
  have h : Tendsto (fun t : ℝ => carryMaterialResponseScale^2*‖carryMaterialForcingVector t‖^2)
      (nhds 0) (nhds (carryMaterialResponseScale^2*‖carryMaterialForcingVector 0‖^2)) :=
    ((forcing_vector_continuous.norm.pow 2).tendsto 0).const_mul _
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t ≠ 0 := by simpa using ht
  rw [retained_leg_energy]
  field_simp

theorem retained_leg_limit_pos :
    0 < carryMaterialResponseScale^2*‖carryMaterialForcingVector 0‖^2 :=
  mul_pos (sq_pos_of_pos material_scale_pos)
    (sq_pos_of_pos (norm_pos_iff.mpr carryMaterialForcingVector_origin_ne_zero))

theorem native_cross_limit :
    Tendsto (fun t : ℝ =>
      (carryMaterialPairGreen (centeredForcingPair t)
        (carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0))/(t:ℂ)).re)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (carryMaterialResponseScale*‖carryMaterialForcingVector 0‖^2)) := by
  have hc : Continuous (fun t : ℝ => (carryMaterialResponseScale:ℂ)*
      inner ℂ (carryMaterialForcingVector t) (carryMaterialForcingVector 0)) :=
    (forcing_vector_continuous.inner continuous_const).const_mul _
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simp only [Function.comp_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, material_inner_self_re] at hr
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by simpa using ht)
  rw [centeredForcingPair_native_cross]
  have he : (((carryMaterialResponseScale*t:ℝ):ℂ)*
      inner ℂ (carryMaterialForcingVector t) (carryMaterialForcingVector 0))/(t:ℂ) =
      (carryMaterialResponseScale:ℂ)*
        inner ℂ (carryMaterialForcingVector t) (carryMaterialForcingVector 0) := by
    push_cast
    field_simp
  rw [he]
  simp [Complex.mul_re]

theorem native_cross_positive_near :
    ∀ᶠ t : ℝ in nhdsWithin 0 ({0}ᶜ),
      (carryMaterialResponseScale*‖carryMaterialForcingVector 0‖^2)/2 <
        (carryMaterialPairGreen (centeredForcingPair t)
          (carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0))/(t:ℂ)).re := by
  have hp : 0 < carryMaterialResponseScale*‖carryMaterialForcingVector 0‖^2 :=
    mul_pos material_scale_pos (sq_pos_of_pos (norm_pos_iff.mpr carryMaterialForcingVector_origin_ne_zero))
  exact (tendsto_order.mp native_cross_limit).1 _ (by linarith)

/-- Source-native obstruction to quotienting by zero forcing energy: a
totally isotropic family still has a nonzero cross with an original state. -/
theorem native_isotropic_not_radical :
    ∀ᶠ t : ℝ in nhdsWithin 0 ({0}ᶜ),
      (∀ u : ℝ, carryMaterialPairGreen (centeredForcingPair t) (centeredForcingPair u) = 0) ∧
      carryMaterialPairGreen (centeredForcingPair t)
        (carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0)) ≠ 0 := by
  filter_upwards [native_cross_positive_near] with t ht
  refine ⟨centeredForcingPair_polarized_green t, ?_⟩
  intro hz
  rw [hz, zero_div, Complex.zero_re] at ht
  have hp : 0 < carryMaterialResponseScale*‖carryMaterialForcingVector 0‖^2 :=
    mul_pos material_scale_pos (sq_pos_of_pos (norm_pos_iff.mpr carryMaterialForcingVector_origin_ne_zero))
  linarith

/-- Any proposed erasure of the whole centered pair loses an actual
native mixed Green value. This is not a no-go for keeping both components. -/
theorem no_green_preserving_erasure :
    ∀ᶠ t : ℝ in nhdsWithin 0 ({0}ᶜ),
      ¬ ∃ Q : (MaterialCarrier × MaterialCarrier) →ₗ[ℂ] (MaterialCarrier × MaterialCarrier),
        Q (centeredForcingPair t) = 0 ∧
        carryMaterialPairGreen (Q (centeredForcingPair t))
          (Q (carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0))) =
          carryMaterialPairGreen (centeredForcingPair t)
            (carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0)) := by
  filter_upwards [native_isotropic_not_radical] with t ht
  rintro ⟨Q,hQ,hG⟩
  apply ht.2
  rw [hQ] at hG
  simpa only [carryMaterialPairGreen, Prod.fst_zero, Prod.snd_zero,
    inner_zero_left, sub_self] using hG.symm

end
end CarryForcingResidual
