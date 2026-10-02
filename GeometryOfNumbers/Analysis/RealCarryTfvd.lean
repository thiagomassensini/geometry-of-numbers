import GeometryOfNumbers.Analysis.RealCarryWeightedValve
import GeometryOfNumbers.Analysis.RealDiscreteProjectiveReconstruction

/-!
# Critical amplitude gauge and the R2 analysis/synthesis interface

The vertical ratio is the existing depth-one amplitude. Neither camera radius
nor reciprocal center-leg deformation enters this construction.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

open RealCarry DiscreteValve ProjectiveDepth ProjectiveValve
open scoped BigOperators lp ENNReal NNReal

/-- Derived from the already realized critical amplitude, never from a prime API. -/
def criticalVerticalAmplitudeRatio (b : ℕ) (hb : 0 < b) : ℝ :=
  realCriticalAmplitude b 1 hb

theorem criticalVerticalAmplitudeRatio_eq_rpow (b : ℕ) (hb : 0 < b) :
    criticalVerticalAmplitudeRatio b hb = (b : ℝ) ^ (-(1 : ℝ) / 2) := by
  simp only [criticalVerticalAmplitudeRatio, realCriticalAmplitude_eq_rpow, Nat.cast_one]

theorem criticalVerticalAmplitudeRatio_pos (b : ℕ) (hb : 0 < b) :
    0 < criticalVerticalAmplitudeRatio b hb :=
  realCriticalAmplitude_pos b 1 hb

theorem criticalVerticalAmplitudeRatio_lt_one (b : ℕ) (hb : 2 ≤ b) :
    criticalVerticalAmplitudeRatio b (by omega) < 1 := by
  rw [criticalVerticalAmplitudeRatio_eq_rpow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hb.trans_lt' (by decide : 1 < 2))
    (by norm_num)

/-- Every depth is a power of the derived consecutive-layer ratio. -/
theorem realCriticalAmplitude_eq_verticalRatio_pow (b k : ℕ) (hb : 0 < b) :
    realCriticalAmplitude b k hb = criticalVerticalAmplitudeRatio b hb ^ k := by
  rw [realCriticalAmplitude_eq_rpow, criticalVerticalAmplitudeRatio_eq_rpow,
    ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ (b : ℝ))]
  congr 1
  ring

theorem realCriticalAmplitude_succ_verticalRatio (b k : ℕ) (hb : 0 < b) :
    realCriticalAmplitude b (k + 1) hb =
      realCriticalAmplitude b k hb * criticalVerticalAmplitudeRatio b hb := by
  rw [realCriticalAmplitude_eq_verticalRatio_pow, realCriticalAmplitude_eq_verticalRatio_pow,
    pow_succ]

def realCarryAmplitudeGauge (eta : ℝ) (f : ℕ → ℝ) : ℕ → ℝ :=
  fun k => eta ^ k * f k

theorem realCarryWeightedFirstDifference_gauge (eta : ℝ) (heta : eta ≠ 0)
    (f : ℕ → ℝ) (k : ℕ) :
    carryWeightedScalarFirstDifference eta (realCarryAmplitudeGauge eta f) k =
      eta ^ k * fdiff f k := by
  unfold carryWeightedScalarFirstDifference realCarryAmplitudeGauge fdiff
  rw [pow_succ]
  field_simp [heta]

theorem realCarryWeightedSecondDifference_gauge (eta : ℝ) (heta : eta ≠ 0)
    (f : ℕ → ℝ) (k : ℕ) :
    carryWeightedScalarSecondDifference eta (realCarryAmplitudeGauge eta f) k =
      eta ^ (k + 1) * bracket f k := by
  unfold carryWeightedScalarSecondDifference
  rw [realCarryWeightedFirstDifference_gauge eta heta f (k + 1),
    realCarryWeightedFirstDifference_gauge eta heta f k, bracket_eq_fdiff_sub, pow_succ]
  ring

/-- The Hilbert-side scalar Green and the additive Green are the same reconstruction
in amplitude units, including the historical one-coordinate shift. -/
theorem realCarryWeightedGreenSum_gauge (eta : ℝ) (heta : eta ≠ 0)
    (f : ℕ → ℝ) (n : ℕ) :
    carryWeightedScalarGreenSum eta (realCarryAmplitudeGauge eta f) (n + 1) =
      eta ^ (n + 1) * greenSum f n := by
  have h := carryWeightedScalarReconstruction heta (realCarryAmplitudeGauge eta f) (n + 1)
  rw [realCarryWeightedFirstDifference_gauge eta heta f 0] at h
  simp only [realCarryAmplitudeGauge, pow_zero, one_mul, fdiff, Nat.zero_add] at h
  have hg := realDiscreteGreenReconstruction f n
  rw [nsmul_eq_mul] at hg
  rw [hg] at h
  linear_combination -h

/-- Analysis retains the interior and the two boundary coordinates. -/
def realCarryTfvdAnalysis (eta : ℝ) :
    CarryVerticalL2 →L[ℝ] (CarryVerticalL2 × (ℝ × ℝ)) :=
  (carryWeightedVerticalCenteredBracket eta).prod (carryWeightedVerticalTrace eta)

/-- Synthesis is causal Green plus the affine return. -/
def realCarryTfvdSynthesis (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    (CarryVerticalL2 × (ℝ × ℝ)) →L[ℝ] CarryVerticalL2 :=
  carryVerticalL2WeightedGreen eta ∘L
      ContinuousLinearMap.fst ℝ CarryVerticalL2 (ℝ × ℝ) +
    carryWeightedVerticalReturn eta heta0 heta1 ∘L
      ContinuousLinearMap.snd ℝ CarryVerticalL2 (ℝ × ℝ)

theorem realCarryTfvdSynthesis_comp_analysis (eta : ℝ)
    (heta0 : 0 < eta) (heta1 : eta < 1) :
    realCarryTfvdSynthesis eta heta0.le heta1 ∘L realCarryTfvdAnalysis eta =
      ContinuousLinearMap.id ℝ CarryVerticalL2 := by
  apply ContinuousLinearMap.ext
  intro x
  ext n
  simpa [realCarryTfvdSynthesis, realCarryTfvdAnalysis] using
    carryWeightedVerticalTfvd_apply eta heta0 heta1 x n

/-- The exact vertical carry identity at the ratio derived from base b. -/
theorem realCriticalCarryTfvd_identity (b : ℕ) (hb : 2 ≤ b) :
    let eta := criticalVerticalAmplitudeRatio b (by omega)
    carryVerticalL2WeightedGreen eta ∘L carryWeightedVerticalCenteredBracket eta +
      carryWeightedVerticalReturn eta (criticalVerticalAmplitudeRatio_pos b _).le
        (criticalVerticalAmplitudeRatio_lt_one b hb) ∘L carryWeightedVerticalTrace eta =
      ContinuousLinearMap.id ℝ CarryVerticalL2 :=
  carryWeightedVerticalTfvd_identity _ (criticalVerticalAmplitudeRatio_pos b _)
    (criticalVerticalAmplitudeRatio_lt_one b hb)

theorem realCriticalCarryTfvdSynthesis_comp_analysis (b : ℕ) (hb : 2 ≤ b) :
    let eta := criticalVerticalAmplitudeRatio b (by omega)
    realCarryTfvdSynthesis eta (criticalVerticalAmplitudeRatio_pos b _).le
        (criticalVerticalAmplitudeRatio_lt_one b hb) ∘L realCarryTfvdAnalysis eta =
      ContinuousLinearMap.id ℝ CarryVerticalL2 :=
  realCarryTfvdSynthesis_comp_analysis _ (criticalVerticalAmplitudeRatio_pos b _)
    (criticalVerticalAmplitudeRatio_lt_one b hb)

/-- A proof certificate, populated below entirely by established theorems.
There are no additional semantic inputs beyond the nondegenerate base. -/
structure RealCriticalCarryTfvdGreenValveCertificate (b : ℕ) (hb : 2 ≤ b) : Prop where
  ratio_origin : criticalVerticalAmplitudeRatio b (by omega) = (b : ℝ) ^ (-(1 : ℝ) / 2)
  ratio_positive : 0 < criticalVerticalAmplitudeRatio b (by omega)
  ratio_contractive : criticalVerticalAmplitudeRatio b (by omega) < 1
  gauge : ∀ f k, carryWeightedScalarSecondDifference
      (criticalVerticalAmplitudeRatio b (by omega))
      (realCarryAmplitudeGauge (criticalVerticalAmplitudeRatio b (by omega)) f) k =
      criticalVerticalAmplitudeRatio b (by omega) ^ (k + 1) * bracket f k
  reconstruction : ∀ (f : ℕ → ℝ) n,
      f (n + 1) = f 0 + (n + 1) • (f 1 - f 0) + greenSum f n
  trace_return : ∀ (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1),
      carryWeightedVerticalTrace eta ∘L carryWeightedVerticalReturn eta h0.le h1 =
        ContinuousLinearMap.id ℝ (ℝ × ℝ)
  bracket_return : ∀ (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1),
      carryWeightedVerticalCenteredBracket eta ∘L carryWeightedVerticalReturn eta h0.le h1 = 0
  tfvd : ∀ (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1),
      carryVerticalL2WeightedGreen eta ∘L carryWeightedVerticalCenteredBracket eta +
        carryWeightedVerticalReturn eta h0.le h1 ∘L carryWeightedVerticalTrace eta =
        ContinuousLinearMap.id ℝ CarryVerticalL2
  analysis_synthesis : ∀ (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1),
      realCarryTfvdSynthesis eta h0.le h1 ∘L realCarryTfvdAnalysis eta =
        ContinuousLinearMap.id ℝ CarryVerticalL2
  projective_green : (coordinate (R := ℝ)).derivativeFun = greenKernelSeries
  projective_cancellation :
      (greenKernelSeries (R := ℝ)).subst (inverseCoordinate (R := ℝ)) *
        PowerSeries.derivative ℝ (inverseCoordinate (R := ℝ)) = 1
  mass_curvature : ∀ D : PowerSeries ℝ,
      projectiveValveCurvature (projectiveValveMass D) = D
  curvature_mass : ∀ A : PowerSeries ℝ, PowerSeries.constantCoeff A = 1 →
      projectiveValveMass (projectiveValveCurvature A) = A
  state_roundtrip : ∀ f : ℕ → ℝ, DiscreteProjective.reconstruct (DiscreteProjective.encode f) = f

theorem realCriticalCarryTfvdGreenValveCapstone (b : ℕ) (hb : 2 ≤ b) :
    RealCriticalCarryTfvdGreenValveCertificate b hb where
  ratio_origin := criticalVerticalAmplitudeRatio_eq_rpow b _
  ratio_positive := criticalVerticalAmplitudeRatio_pos b _
  ratio_contractive := criticalVerticalAmplitudeRatio_lt_one b hb
  gauge := realCarryWeightedSecondDifference_gauge _
    (criticalVerticalAmplitudeRatio_pos b _).ne'
  reconstruction := realDiscreteGreenReconstruction
  trace_return := carryWeightedVerticalTrace_comp_return
  bracket_return := carryWeightedVerticalCenteredBracket_comp_return
  tfvd := carryWeightedVerticalTfvd_identity
  analysis_synthesis := realCarryTfvdSynthesis_comp_analysis
  projective_green := coordinate_derivativeFun
  projective_cancellation := greenKernel_subst_inverse_mul_inverseDerivative
  mass_curvature := projectiveValveCurvature_projectiveValveMass
  curvature_mass := projectiveValveMass_projectiveValveCurvature
  state_roundtrip := DiscreteProjective.reconstruct_encode

end
end GeometryOfNumbers.Analysis
