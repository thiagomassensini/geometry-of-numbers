import GeometryOfNumbers.Analysis.C2RealFiberTfvdIncidence
import GeometryOfNumbers.Analysis.BaseTwoCanonicalDressingMoments
import GeometryOfNumbers.Analysis.MomentGramPositivity
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Full vertical TFVD observation, with both boundary coordinates retained.
The observed Gram is tested before reconstruction or scalar compression.
Its positive definiteness does not identify it with a canonical moment Gram. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis
open RealCarry

/-- Standard Hilbert product of the interior bracket and its two boundary data. -/
abbrev CompleteVerticalObservationCarrier :=
  WithLp 2 (CarryVerticalL2 × WithLp 2 (ℝ × ℝ))

/-- Repackage existing TFVD channels, without altering their coefficients. -/
def completeVerticalObservation (eta : ℝ) :
    CarryVerticalL2 →L[ℝ] CompleteVerticalObservationCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ CarryVerticalL2 (WithLp 2 (ℝ × ℝ))).symm.toContinuousLinearMap.comp
    ((carryWeightedVerticalCenteredBracket eta).prod
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.comp
        (carryWeightedVerticalTrace eta)))

@[simp] theorem completeVerticalObservation_apply (eta : ℝ) (x : CarryVerticalL2) :
    completeVerticalObservation eta x = WithLp.toLp 2
      (carryWeightedVerticalCenteredBracket eta x,
       WithLp.toLp 2 (x 0,eta⁻¹*x 1-x 0)) := by
  simp [completeVerticalObservation,carryWeightedVerticalTrace_apply]

/-- Exact synthesis uses both trace values, not the bracket alone. -/
theorem completeVerticalObservation_reconstruction (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) (x : CarryVerticalL2) :
    realCarryTfvdSynthesis eta h0.le h1
      ((completeVerticalObservation eta x).fst,
       WithLp.ofLp (completeVerticalObservation eta x).snd) = x := by
  have h := congrArg (fun A : CarryVerticalL2 →L[ℝ] CarryVerticalL2 => A x)
    (realCarryTfvdSynthesis_comp_analysis eta h0 h1)
  simpa [completeVerticalObservation_apply,realCarryTfvdAnalysis,
    carryWeightedVerticalTrace_apply] using h

/-- All the information in a vertical fiber remains observable. -/
theorem completeVerticalObservation_injective (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) :
    Function.Injective (completeVerticalObservation eta) := by
  intro x y h
  rw [← completeVerticalObservation_reconstruction eta h0 h1 x,
    ← completeVerticalObservation_reconstruction eta h0 h1 y,h]

/-- Existing coordinate probes; neither their coefficients nor the observer depend on moments. -/
def completeVerticalObservationJet (eta : ℝ) (n : ℕ) :
    CompleteVerticalObservationCarrier :=
  completeVerticalObservation eta (lp.single 2 n (1 : ℝ))

/-- This is the existing core-1, left-branch, first-quadrature fiber.
The natural index is decoded C2 depth-from-two, never a material edge number. -/
theorem completeVerticalObservationJet_c2_provenance (eta : ℝ) (n : ℕ) :
    completeVerticalObservationJet eta n = completeVerticalObservation eta
      (c2BranchVerticalCoordinate c2UnitOddCore 0 0 (c2RealIncidenceJet (Sum.inl n))) := by
  unfold completeVerticalObservationJet
  apply congrArg (completeVerticalObservation eta)
  apply lp.ext
  funext j
  change (lp.single 2 n (1 : ℝ) : CarryVerticalL2) j =
    (c2RealIncidenceJet (Sum.inl n) (c2UnitOddCore,(0,j))) 0
  by_cases h : j = n
  · subst j
    simp [c2RealIncidenceJet,c2ParityIncidenceAddress,lp.single_apply,realPlaneHilbertEquiv]
  · simp [c2RealIncidenceJet,c2ParityIncidenceAddress,lp.single_apply,h]

private def verticalCoordinates : CarryVerticalL2 →ₗ[ℝ] (ℕ → ℝ) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem verticalDelta_linearIndependent :
    LinearIndependent ℝ (fun n : ℕ => lp.single 2 n (1 : ℝ)) := by
  apply LinearIndependent.of_comp verticalCoordinates
  convert Pi.linearIndependent_single_one ℕ ℝ using 1
  funext i n
  rfl

/-- Independence follows from synthesis, before any energy or moment comparison. -/
theorem completeVerticalObservationJet_linearIndependent (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) :
    LinearIndependent ℝ (completeVerticalObservationJet eta) :=
  verticalDelta_linearIndependent.map_injOn (completeVerticalObservation eta).toLinearMap
    (completeVerticalObservation_injective eta h0 h1).injOn

/-- Finite observer on the actual vertical prefix, with no material-edge relabeling. -/
def completeVerticalPrefixObservation (eta : ℝ) (N : ℕ) :
    (Fin N → ℝ) →ₗ[ℝ] CompleteVerticalObservationCarrier where
  toFun x := ∑ i : Fin N, x i • completeVerticalObservationJet eta i.val
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum,smul_smul]

theorem completeVerticalPrefixObservation_injective (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) (N : ℕ) :
    Function.Injective (completeVerticalPrefixObservation eta N) := by
  have hi := (completeVerticalObservationJet_linearIndependent eta h0 h1).comp
    (fun i : Fin N => i.val) Fin.val_injective
  intro x y h
  have hz : ∑ i : Fin N, (x i-y i) • completeVerticalObservationJet eta i.val = 0 := by
    change (∑ i : Fin N, x i • completeVerticalObservationJet eta i.val) =
      ∑ i : Fin N, y i • completeVerticalObservationJet eta i.val at h
    simpa only [sub_smul,Finset.sum_sub_distrib,sub_eq_zero] using h
  have hc := (Fintype.linearIndependent_iff.mp hi) (fun i => x i-y i) hz
  funext i
  exact sub_eq_zero.mp (hc i)

/-- Own observability Gram, not a moment Hankel. -/
def completeVerticalObservabilityGram (eta : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.gram ℝ (fun i : Fin N => completeVerticalObservationJet eta i.val)

/-- Positive definiteness is derived solely from the same observed family's independence. -/
theorem completeVerticalObservabilityGram_posDef (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) (N : ℕ) :
    (completeVerticalObservabilityGram eta N).PosDef :=
  Matrix.posDef_gram_of_linearIndependent
    ((completeVerticalObservationJet_linearIndependent eta h0 h1).comp
      Fin.val Fin.val_injective)

private theorem bracket_delta_zero (eta : ℝ) :
    carryWeightedVerticalCenteredBracket eta (lp.single 2 0 (1 : ℝ)) =
      eta • lp.single 2 1 (1 : ℝ) := by
  apply lp.ext
  funext n
  cases n with
  | zero => simp
  | succ n =>
    rw [carryWeightedVerticalCenteredBracket_succ]
    by_cases hn : n = 0
    · subst n; simp [lp.single_apply]
    · simp [lp.single_apply,hn]

private theorem bracket_delta_one (eta : ℝ) :
    carryWeightedVerticalCenteredBracket eta (lp.single 2 1 (1 : ℝ)) =
      (-2:ℝ) • lp.single 2 1 (1 : ℝ) + eta • lp.single 2 2 (1 : ℝ) := by
  apply lp.ext
  funext n
  cases n with
  | zero => simp
  | succ n =>
    rw [carryWeightedVerticalCenteredBracket_succ]
    rcases n with _ | n
    · simp [lp.single_apply]
    · rcases n with _ | n
      · simp [lp.single_apply]
      · simp [lp.single_apply]

/-- Full trace energy, before scalar compression. -/
theorem completeVerticalObservationJet_inner_zero_zero (eta : ℝ) :
    inner ℝ (completeVerticalObservationJet eta 0) (completeVerticalObservationJet eta 0) =
      eta^2+2 := by
  simp only [completeVerticalObservationJet,completeVerticalObservation_apply,
    WithLp.prod_inner_apply]
  rw [bracket_delta_zero]
  simp only [inner_smul_left,inner_smul_right,lp.inner_single_left,
    lp.single_apply,RCLike.inner_apply]
  norm_num
  ring

/-- The boundary flow couples the first two probes. -/
theorem completeVerticalObservationJet_inner_zero_one (eta : ℝ) :
    inner ℝ (completeVerticalObservationJet eta 0) (completeVerticalObservationJet eta 1) =
      -2*eta-eta⁻¹ := by
  simp only [completeVerticalObservationJet,completeVerticalObservation_apply,
    WithLp.prod_inner_apply]
  rw [bracket_delta_zero,bracket_delta_one]
  simp only [inner_smul_left,inner_add_right,inner_smul_right,
    lp.inner_single_left,lp.single_apply,RCLike.inner_apply]
  norm_num
  ring

/-- The first nontrivial index-sum comparison, with the full trace still retained. -/
theorem completeVerticalObservationJet_inner_zero_two (eta : ℝ) (heta : eta ≠ 0) :
    inner ℝ (completeVerticalObservationJet eta 0) (completeVerticalObservationJet eta 2) = 1 := by
  simp only [completeVerticalObservationJet,completeVerticalObservation_apply,
    WithLp.prod_inner_apply]
  rw [bracket_delta_zero,inner_smul_left,lp.inner_single_left]
  simp [carryWeightedVerticalCenteredBracket_succ,lp.single_apply,RCLike.inner_apply,heta]

/-- Boundary flow contributes eta^-2; the bracket contributes 4+eta^2. -/
theorem completeVerticalObservationJet_inner_one_one (eta : ℝ) :
    inner ℝ (completeVerticalObservationJet eta 1) (completeVerticalObservationJet eta 1) =
      4 + eta^2 + (eta⁻¹)^2 := by
  simp only [completeVerticalObservationJet,completeVerticalObservation_apply,
    WithLp.prod_inner_apply]
  rw [bracket_delta_one]
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    lp.inner_single_left,lp.single_apply,RCLike.inner_apply]
  norm_num
  ring

/-- Full bracket+boundary observation is separating and positive, yet is not an
index-sum kernel. This excludes this channel metric, not the complete theory. -/
theorem completeVerticalObservabilityGram_not_hankel (eta : ℝ) (heta : eta ≠ 0)
    (moments : ℕ → ℝ) :
    hankelGram moments 3 ≠ completeVerticalObservabilityGram eta 3 := by
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) h
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) h
  change moments (0+2) = inner ℝ (completeVerticalObservationJet eta 0)
    (completeVerticalObservationJet eta 2) at h02
  change moments (1+1) = inner ℝ (completeVerticalObservationJet eta 1)
    (completeVerticalObservationJet eta 1) at h11
  rw [completeVerticalObservationJet_inner_zero_two eta heta] at h02
  rw [completeVerticalObservationJet_inner_one_one eta] at h11
  change moments 2 = 1 at h02
  change moments 2 = 4 + eta^2 + (eta⁻¹)^2 at h11
  nlinarith [sq_nonneg eta,sq_nonneg (eta⁻¹)]

/-- No choice of a scalar moment sequence repairs the index-sum mismatch. -/
theorem completeVerticalObservationJet_not_momentGram (eta : ℝ) (heta : eta ≠ 0)
    (moments : ℕ → ℝ) :
    ¬ IsMomentGramRepresentation moments (completeVerticalObservationJet eta) := by
  intro h
  apply completeVerticalObservabilityGram_not_hankel eta heta moments
  ext i j
  exact h i.val j.val

/-- Specialization to the existing ratio derived from base-two vertical amplitude.
The canonical moment sequence is only a comparison target, not a construction input. -/
theorem completeCriticalVerticalObservabilityGram_not_canonicalHankel :
    hankelGram BaseTwoCompletion.baseTwoCanonicalMomentSequence 3 ≠
      completeVerticalObservabilityGram (criticalVerticalAmplitudeRatio 2 (by decide)) 3 :=
  completeVerticalObservabilityGram_not_hankel _
    (criticalVerticalAmplitudeRatio_pos 2 _).ne' _

end GeometryOfNumbers.Analysis
