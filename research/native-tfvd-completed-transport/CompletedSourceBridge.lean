import CoefficientPorts
import CompletionCommutator

namespace CarryNativeTfvd
open CarrySelfAdjointOperator NativeCauchyPorts
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Corrected physical TFVD for the SAME weighted source: Green, both traces,
and the exact source commutator are synthesized before any signed pairing. -/
theorem weighted_physical_reconstruction (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    NativeLaguerre.physicalCauchySynthesis (coefficientWeight w c) =
      NativeLaguerre.physicalGreenOperator eta h0.le h1
        (NativeLaguerre.physicalCauchySynthesis (coefficientWeight w (finiteTfvdBulk eta c))) +
      ((NativeLaguerre.physicalGreenResolvent eta h0.le h1)^2)
        ((w 0 * c 0) • completedNativeChiralCauchyFeature 0 +
          (w 1 * c 1 - 2 * (eta : ℂ) * (w 0 * c 0)) • completedNativeChiralCauchyFeature 1) +
      NativeLaguerre.physicalGreenOperator eta h0.le h1
        (NativeLaguerre.physicalCauchySynthesis (completionCommutator eta w c)) := by
  rw [physical_finite_reconstruction eta h0 h1,
    completion_bulk_split, map_add, map_add,
    coefficient_weight_apply, coefficient_weight_apply]
  abel

theorem weighted_source_sum (w : ℕ → ℂ) (c : ℕ →₀ ℂ) :
    NativeLaguerre.physicalCauchySynthesis (coefficientWeight w c) =
      ∑ j ∈ c.support, (w j * c j) • completedNativeChiralCauchyFeature j := by
  classical
  unfold NativeLaguerre.physicalCauchySynthesis
  rw [Finsupp.linearCombination_apply]
  unfold coefficientWeight
  exact Finsupp.sum_onFinset _ _ _ _ (by intro j _; exact zero_smul ℂ _)

/-- The amplitude is the ORIGINAL normalized positive chiral amplitude. -/
def incidentWeight (k j : ℕ) : ℂ :=
  completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k j)

/-- The returned leg retains the SAME amplitude, once, and the original quotient. -/
def returnedWeight (k j : ℕ) : ℂ :=
  incidentWeight k j * completedNativeHermiteBiehlerChiralQuotient
    (canonicalCompletedC3RadialTiltPoint k j)

/-- Complete vector provenance into BOTH original physical legs, before readout. -/
theorem completed_source_weighted_identity (k : ℕ) (c : ℕ →₀ ℂ) :
    NativeLaguerre.physicalCompletedFiniteSource k c =
      ((Real.sqrt ((k : ℝ) + 1) : ℂ) •
        NativeLaguerre.physicalCauchySynthesis (coefficientWeight (incidentWeight k) c),
       (Real.sqrt ((k : ℝ) + 1) : ℂ) •
        NativeLaguerre.physicalCauchySynthesis (coefficientWeight (returnedWeight k) c)) := by
  rw [NativeLaguerre.physicalCompletedFiniteSource_original,
    weighted_source_sum, weighted_source_sum]
  classical
  apply Prod.ext
  all_goals
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Prod.fst_sum,
      Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      canonicalCompletedNativeRadialProjectiveChiralState,
      canonicalCompletedNativeRadialChiralDefectState,
      completedNativeRadialChiralMultiplierState, completedNativeRadialChiralCauchyState,
      Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [incidentWeight, returnedWeight]
    congr 1
    ring

/-- Three complete vector components: Green bulk, both traces, and the exact
completion commutator. The original signed metric is used only afterwards. -/
def completedSourceParts (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c : ℕ →₀ ℂ) : Fin 3 → CanonicalCompletedNativeProjectiveChiralCarrier :=
  let G := NativeLaguerre.physicalGreenOperator eta h0.le h1
  let R := (NativeLaguerre.physicalGreenResolvent eta h0.le h1)^2
  let A := incidentWeight k
  let B := returnedWeight k
  let scale := (Real.sqrt ((k : ℝ) + 1) : ℂ)
  Fin.cases
    (scale • (G (NativeLaguerre.physicalCauchySynthesis (coefficientWeight A (finiteTfvdBulk eta c))),
      G (NativeLaguerre.physicalCauchySynthesis (coefficientWeight B (finiteTfvdBulk eta c)))))
    (Fin.cases
      (scale • (R ((A 0 * c 0) • completedNativeChiralCauchyFeature 0 +
          (A 1 * c 1 - 2 * (eta : ℂ) * (A 0 * c 0)) • completedNativeChiralCauchyFeature 1),
        R ((B 0 * c 0) • completedNativeChiralCauchyFeature 0 +
          (B 1 * c 1 - 2 * (eta : ℂ) * (B 0 * c 0)) • completedNativeChiralCauchyFeature 1)))
      (fun _ => scale •
        (G (NativeLaguerre.physicalCauchySynthesis (completionCommutator eta A c)),
          G (NativeLaguerre.physicalCauchySynthesis (completionCommutator eta B c)))))

theorem completed_source_three_parts (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c : ℕ →₀ ℂ) :
    NativeLaguerre.physicalCompletedFiniteSource k c =
      completedSourceParts eta h0 h1 k c 0 + completedSourceParts eta h0 h1 k c 1 +
        completedSourceParts eta h0 h1 k c 2 := by
  rw [completed_source_weighted_identity,
    weighted_physical_reconstruction eta h0 h1 (incidentWeight k) c,
    weighted_physical_reconstruction eta h0 h1 (returnedWeight k) c]
  simp only [show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
    show (2 : Fin 3) = (0 : Fin 1).succ.succ from rfl,
    completedSourceParts, Fin.cases_zero, Fin.cases_succ]
  apply Prod.ext
  all_goals simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_add]

/-- Independent coefficient states; all nine bulk/boundary/defect pairings,
both chiral legs, and the existing factor 1/2 remain exact. -/
theorem completed_source_nine_pairings (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c d : ℕ →₀ ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (NativeLaguerre.physicalCompletedFiniteSource k c)
      (NativeLaguerre.physicalCompletedFiniteSource k d) =
      ∑ a : Fin 3, ∑ b : Fin 3, canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k c a) (completedSourceParts eta h0 h1 k d b) := by
  rw [completed_source_three_parts eta h0 h1 k c,
    completed_source_three_parts eta h0 h1 k d]
  simp only [Fin.sum_univ_three, canonicalCompletedNativeProjectiveChiralForm,
    Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]
  ring


end
end CarryNativeTfvd
