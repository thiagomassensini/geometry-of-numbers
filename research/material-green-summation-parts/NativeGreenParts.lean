import FullGreenParts

/-! Summation by parts of BOTH actual reduced companion/value slots, with
the SAME completion/dressing and global cell return. Finite observations
are made only after the original pair is assembled on its proved domain. -/
namespace CarryMaterialParts
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion DiscreteValve
open CarryCompleteTfvd CarryForcingResidual CarryNativePhase CarryMixedGreen CarryCompletedGreenBalance
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def companionSamples (t : ℝ) (n : ℕ) : ℂ :=
  Complex.I*baseTwoCanonicalDressingScalar t*clockSamples t n-
    deriv baseTwoCanonicalDressingScalar t*ordinarySamples t n

def valueSamples (t : ℝ) (n : ℕ) : ℂ :=
  2*baseTwoCanonicalDressingScalar t*ordinarySamples t n

def reducedFirstSamples (t : ℝ) (n : ℕ) : ℂ :=
  companionSamples t n-(carryMaterialResponseScale*t:ℝ)*valueSamples t n

def reducedSecondSamples (t : ℝ) (n : ℕ) : ℂ :=
  (carryMaterialResponseScale*t:ℝ)*companionSamples t n

theorem companion_difference (t : ℝ) (n : ℕ) :
    fdiff (companionSamples t) n = (carryMaterialCompanionValuePair t).1.snd.fst n := by
  have ho := ordinary_difference t n
  have hk := clock_difference t n
  have hc : (carryMaterialCompanionValuePair t).1.snd.fst n =
      Complex.I*baseTwoCanonicalDressingScalar t*baseTwoCompletedMaterialClockL2 t n-
        deriv baseTwoCanonicalDressingScalar t*criticalMaterialGradient t n := by
    change -(baseTwoCanonicalDressingScalar t *
      (-Complex.I*baseTwoCompletedMaterialClockL2 t n)+
      deriv baseTwoCanonicalDressingScalar t*criticalMaterialGradient t n) = _
    ring
  rw [hc, ← ho, ← hk]
  simp only [companionSamples, fdiff]
  ring

theorem value_difference (t : ℝ) (n : ℕ) :
    fdiff (valueSamples t) n = (carryMaterialCompanionValuePair t).2.snd.fst n := by
  have ho := ordinary_difference t n
  change fdiff (valueSamples t) n = (2:ℂ)*(baseTwoCanonicalDressingScalar t*criticalMaterialGradient t n)
  rw [← ho]
  simp only [valueSamples, fdiff]
  ring

theorem reduced_first_difference (t : ℝ) (n : ℕ) :
    fdiff (reducedFirstSamples t) n = (carryMaterialReducedCompanionPair t).1.snd.fst n := by
  have hc := companion_difference t n
  have hv := value_difference t n
  change fdiff (reducedFirstSamples t) n =
    (carryMaterialCompanionValuePair t).1.snd.fst n-
      ((carryMaterialResponseScale*t:ℝ):ℂ)*(carryMaterialCompanionValuePair t).2.snd.fst n
  rw [← hc, ← hv]
  simp only [reducedFirstSamples, fdiff]
  ring

theorem reduced_second_difference (t : ℝ) (n : ℕ) :
    fdiff (reducedSecondSamples t) n = (carryMaterialReducedCompanionPair t).2.snd.fst n := by
  have hc := companion_difference t n
  change fdiff (reducedSecondSamples t) n =
    ((carryMaterialResponseScale*t:ℝ):ℂ)*(carryMaterialCompanionValuePair t).1.snd.fst n
  rw [← hc]
  simp only [reducedSecondSamples, fdiff]
  ring

/-- Exact flux-minus-curvature expression with BOTH original orientations. -/
def nativeFluxBulk (N : ℕ) (t u : ℝ) : ℂ :=
  endpointFlux (reducedSecondSamples t) (reducedFirstSamples u) N-
    curvatureBulk (reducedSecondSamples t) (reducedFirstSamples u) N-
  (endpointFlux (reducedFirstSamples t) (reducedSecondSamples u) N-
    curvatureBulk (reducedFirstSamples t) (reducedSecondSamples u) N)

theorem native_interior_parts (N : ℕ) (t u : ℝ) :
    (∑ n ∈ Finset.range N, interiorTerm (carryMaterialReducedCompanionPair t)
      (carryMaterialReducedCompanionPair u) n) = nativeFluxBulk N t u := by
  simp only [interiorTerm, ← reduced_first_difference, ← reduced_second_difference]
  rw [Finset.sum_sub_distrib, polarized_summation_parts, polarized_summation_parts]
  rfl

theorem native_prefix_parts (N : ℕ) (t u : ℝ) :
    prefixGreen N (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u) =
      boundaryGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u)+
        nativeFluxBulk N t u := by rw [prefixGreen, native_interior_parts]

/-- The SAME finite flux and curvature expression occurs in the hidden
complement. It cannot be treated as a positive contribution to the difference. -/
theorem native_hidden_prefix_parts (N : ℕ) (t u : ℝ) :
    prefixGreen N (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
      (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) =
      boundaryGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
        (carryMaterialPairComplement (carryMaterialReducedCompanionPair u))+nativeFluxBulk N t u := by
  simp only [prefixGreen, hidden_interior_exact]
  rw [native_interior_parts]

/-- The PR57 ledger is exactly the full original reduced pair minus its
hidden readout complement. Forcing, both mixed terms and phase are included. -/
theorem native_tfvd_ledger (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (t u : ℝ) :
    tfvdWholeGreen eta h0 h1 t u =
      carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u)-
        carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
          (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) := by
  rw [carryMaterialForcingRemainder_ledger]
  simp only [tfvdWholeGreen, tfvd_compensated_exact, tfvd_mixed_exact, green_roundtrip,
    compensatedGreen, mixedForcingGreen, hiddenGreen, carryMaterialForcingRemainderGreen,
    carryMaterialForcingGreen_factor]
  ring

/-- The complete source quotient has NO independent material bulk after
hidden compensation; this is a two-argument identity for every finite cutoff. -/
theorem native_cutoff_boundary_exact (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (N : ℕ) (t u : ℝ) :
    tfvdWholeGreen eta h0 h1 t u =
      prefixGreen N (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u)-
        prefixGreen N (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
          (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) := by
  rw [native_tfvd_ledger, full_hidden_equals_finite N]

end
end CarryMaterialParts
