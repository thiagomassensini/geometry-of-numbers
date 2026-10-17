import PrimeOverlapCanary

/-! Literal camera matrices versus coherent synthesis, on the ACTUAL prime
source channels. The two cutoffs are not identified. No fitted Gram is used. -/
namespace CarryPrimeClock
open CarrySelfAdjointOperator NativeCarryC3Crosswalk
open GeometryOfNumbers.Analysis
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def twoPrimeCameras : Fin 2 → ℕ := ![2,3]

theorem twoPrimeFamily_coherent_pairing (t u : ℝ) :
    inner ℂ (coherentPrefix 2 t) (coherentPrefix 2 u) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        inner ℂ ((twoPrimeFamily t).ofLp i) ((twoPrimeFamily u).ofLp j) := by
  rw [coherentPrefix_two t, coherentPrefix_two u]
  simp only [twoPrimeFamily, WithLp.ofLp_toLp, Fin.sum_univ_two,
    Fin.isValue, ite_true, Fin.one_eq_zero_iff, Nat.reduceEqDiff, if_false,
    inner_add_left, inner_add_right]
  ring

/-- The raw row Gram is induced by its own synthesis, but its weights are
not automatically the weights of coherent addition in the material carrier. -/
theorem raw_coherent_pairing_defect
    {state : Type*} [Fintype state] (C : Matrix (Fin 2) state ℝ) (t u : ℝ) :
    inner ℂ (finiteCameraHilbertRawSynthesis C (twoPrimeFamily t))
      (finiteCameraHilbertRawSynthesis C (twoPrimeFamily u)) -
        inner ℂ (coherentPrefix 2 t) (coherentPrefix 2 u) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (((finiteCameraRowGram C i j:ℝ):ℂ)-1)*
          inner ℂ ((twoPrimeFamily t).ofLp i) ((twoPrimeFamily u).ofLp j) := by
  rw [finiteCameraHilbertRawSynthesis_inner, twoPrimeFamily_coherent_pairing,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Camera cutoff k is independent of the material/TFVD prefix, fixed here
at the first two edges to expose the arithmetic overlap. -/
theorem literal_camera_coherent_pairing_defect (k : ℕ) (t u : ℝ) :
    inner ℂ
      (finiteCameraHilbertRawSynthesis (finiteLiteralCameraMatrix k twoPrimeCameras)
        (twoPrimeFamily t))
      (finiteCameraHilbertRawSynthesis (finiteLiteralCameraMatrix k twoPrimeCameras)
        (twoPrimeFamily u)) -
      inner ℂ (coherentPrefix 2 t) (coherentPrefix 2 u) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (((literalFiniteCameraGram k (twoPrimeCameras i) (twoPrimeCameras j):ℝ):ℂ)-1)*
          inner ℂ ((twoPrimeFamily t).ofLp i) ((twoPrimeFamily u).ofLp j) := by
  rw [raw_coherent_pairing_defect]
  have hc : ∀ i : Fin 2, 2 ≤ twoPrimeCameras i := by
    intro i
    fin_cases i <;> norm_num [twoPrimeCameras]
  simp_rw [finiteLiteralCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram
    (camera := twoPrimeCameras) hc k]

/-- Coherent addition uses the original common material carrier. It is not
the norm on the orthogonal outer ledger. -/
def coherentFamilySum {index H : Type*} [Fintype index]
    [NormedAddCommGroup H] [Module ℂ H] : FiniteHilbertFamily index H →ₗ[ℂ] H where
  toFun X := ∑ i, X.ofLp i
  map_add' X Y := by simp [Finset.sum_add_distrib]
  map_smul' a X := by simp [Finset.smul_sum]

/-- Decode the camera coordinates first, then add the source contributions.
Both maps predate any target moment Gram. -/
def coherentCameraReadout {camera state H : Type*}
    [Fintype camera] [DecidableEq camera] [Fintype state]
    [NormedAddCommGroup H] [Module ℂ H] (C : Matrix camera state ℝ) :
    FiniteHilbertFamily state H →ₗ[ℂ] H :=
  coherentFamilySum.comp (finiteCanonicalCameraHilbertReadout C)

theorem coherentCameraReadout_synthesis {camera state H : Type*}
    [Fintype camera] [DecidableEq camera] [Fintype state]
    [NormedAddCommGroup H] [Module ℂ H] (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef) (X : FiniteHilbertFamily camera H) :
    coherentCameraReadout C (finiteCanonicalCameraHilbertSynthesis C X) =
      coherentFamilySum X := by
  unfold coherentCameraReadout
  simp only [LinearMap.comp_apply, finiteCanonicalCameraHilbertReadout_synthesis C hG]

/-- The arithmetic two-prime family has exactly the existing TFVD prefix. -/
theorem coherentCameraReadout_twoPrime {state : Type*} [Fintype state]
    (C : Matrix (Fin 2) state ℝ) (hG : (finiteCameraRowGram C).PosDef) (t : ℝ) :
    coherentCameraReadout C (finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily t)) =
      coherentPrefix 2 t := by
  rw [coherentCameraReadout_synthesis C hG, coherentPrefix_two]
  simp [coherentFamilySum, twoPrimeFamily, Fin.sum_univ_two]

/-- This pairing DOES recover the physical overlap, after decoding and
coherent addition. Measuring the whitened ledger norm alone does not. -/
theorem coherentCameraReadout_twoPrime_pairing {state : Type*} [Fintype state]
    (C : Matrix (Fin 2) state ℝ) (hG : (finiteCameraRowGram C).PosDef) (t u : ℝ) :
    inner ℂ
      (coherentCameraReadout C (finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily t)))
      (coherentCameraReadout C (finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily u))) =
      inner ℂ (coherentPrefix 2 t) (coherentPrefix 2 u) := by
  rw [coherentCameraReadout_twoPrime C hG, coherentCameraReadout_twoPrime C hG]

/-- Same full return and derived tail as the actual source. No new graph
condition is imposed on the independent finite prefix. -/
def decodedCompleteClock {state : Type*} [Fintype state]
    (C : Matrix (Fin 2) state ℝ) (t : ℝ) : MaterialCarrier :=
  edgeInjection (coherentCameraReadout C
      (finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily t))) +
    returnInjection (globalClockReturn t) + physicalClockTail 2 t

theorem decodedCompleteClock_eq {state : Type*} [Fintype state]
    (C : Matrix (Fin 2) state ℝ) (hG : (finiteCameraRowGram C).PosDef) (t : ℝ) :
    decodedCompleteClock C t = physicalClock t := by
  rw [decodedCompleteClock, coherentCameraReadout_twoPrime C hG]
  exact physicalClock_head_tail 2 t

theorem decodedCompleteClock_pairing {state : Type*} [Fintype state]
    (C : Matrix (Fin 2) state ℝ) (hG : (finiteCameraRowGram C).PosDef) (t u : ℝ) :
    inner ℂ (decodedCompleteClock C t) (decodedCompleteClock C u) =
      inner ℂ (physicalClock t) (physicalClock u) := by
  rw [decodedCompleteClock_eq C hG, decodedCompleteClock_eq C hG]

/-- Linear map on the enriched data, with the complete return and derived
tail as explicit INPUTS. It cannot reconstruct these from a finite head alone.
The product here is an algebraic ledger; its norm is not named physical energy. -/
def enrichedClockDecoder {state : Type*} [Fintype state]
    (C : Matrix (Fin 2) state ℝ) :
    (FiniteHilbertFamily state BaseTwoCompletion.MaterialEdgeL2 ×
      (ℂ × BaseTwoCompletion.MaterialEdgeL2)) →ₗ[ℂ] MaterialCarrier where
  toFun x := edgeInjection (coherentCameraReadout C x.1) +
    returnInjection x.2.1 + edgeInjection x.2.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' a x := by
    change edgeInjection (coherentCameraReadout C (a • x.1)) +
      returnInjection (a • x.2.1) + edgeInjection (a • x.2.2) =
        a • (edgeInjection (coherentCameraReadout C x.1) +
          returnInjection x.2.1 + edgeInjection x.2.2)
    simp only [map_smul, smul_add]

def enrichedPrimeClockInput {state : Type*} [Fintype state]
    (C : Matrix (Fin 2) state ℝ) (t : ℝ) :
    FiniteHilbertFamily state BaseTwoCompletion.MaterialEdgeL2 ×
      (ℂ × BaseTwoCompletion.MaterialEdgeL2) :=
  (finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily t),
    (globalClockReturn t, clockTail 2 t))

theorem enrichedClockDecoder_source {state : Type*} [Fintype state]
    (C : Matrix (Fin 2) state ℝ) (hG : (finiteCameraRowGram C).PosDef) (t : ℝ) :
    enrichedClockDecoder C (enrichedPrimeClockInput C t) = physicalClock t :=
  decodedCompleteClock_eq C hG t

theorem enrichedClockDecoder_rotation {state : Type*} [Fintype state]
    (C : Matrix (Fin 2) state ℝ)
    (x : FiniteHilbertFamily state BaseTwoCompletion.MaterialEdgeL2 ×
      (ℂ × BaseTwoCompletion.MaterialEdgeL2)) :
    enrichedClockDecoder C (Complex.I • x) = Complex.I • enrichedClockDecoder C x :=
  map_smul (enrichedClockDecoder C) Complex.I x

end
end CarryPrimeClock
