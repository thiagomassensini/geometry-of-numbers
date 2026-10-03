import GeometryOfNumbers.Analysis.GreenParsevalMaterialEvolution
import GeometryOfNumbers.Analysis.BaseTwoCanonicalDressingMoments
import GeometryOfNumbers.Analysis.ParityMomentGram
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Exact Parseval jet transport and the unresolved canonical first column

The vector orbit is the preexisting full provenance-correct C2 source,
followed by the same canonical Parseval analysis. No moment defines a vector.
The jet definitions below use Mathlib's total iterated derivative: regularity
is a separate obligation, explicitly preserved by the transport theorems.
Neither these orbit jets nor their first column are asserted to be the
completed boundary Green jets that realize the canonical moments.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProduct Topology lp ContDiff
open private real_inner_complex_re from GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy

namespace GeometryOfNumbers.Analysis.CanonicalGreenMomentSeam
open GreenFrame.Concrete GreenParsevalMaterialLog GreenStateMaterialLog
open GreenStateMaterialDynamics GreenParsevalMaterialDynamics C2GlobalGreenBridge
open C2GreenWhiteningGenealogy BaseTwoCompletion

private theorem parseval_left_inverse (x : State) :
    greenParsevalAnalysis.adjoint (greenParsevalAnalysis x) = x := by
  have h := congrArg (fun A : State →L[ℂ] State => A x) greenParsevalAnalysis_gram_identity
  simpa using h

/-- Parseval does not supply missing regularity: its bounded adjoint recovers it. -/
theorem greenParseval_differentiableAt_iff (f : ℝ → State) (t : ℝ) :
    DifferentiableAt ℝ (fun s => greenParsevalAnalysis (f s)) t ↔
      DifferentiableAt ℝ f t := by
  constructor
  · intro h
    have hc := ((greenParsevalAnalysis.adjoint.restrictScalars ℝ).differentiableAt).comp t h
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', parseval_left_inverse] using hc
  · intro h
    exact ((greenParsevalAnalysis.restrictScalars ℝ).differentiableAt).comp t h

/-- Exact transport of the total derivative, including its non-differentiable convention. -/
theorem greenParseval_deriv (f : ℝ → State) (t : ℝ) :
    deriv (fun s => greenParsevalAnalysis (f s)) t = greenParsevalAnalysis (deriv f t) := by
  by_cases hf : DifferentiableAt ℝ f t
  · exact ((greenParsevalAnalysis.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt).deriv
  · have hp := mt (greenParseval_differentiableAt_iff f t).mp hf
    rw [deriv_zero_of_not_differentiableAt hp, deriv_zero_of_not_differentiableAt hf, map_zero]

/-- Equality of complete vector functions before applying every iterated derivative. -/
theorem greenParseval_iteratedDeriv (f : ℝ → State) (r : ℕ) (t : ℝ) :
    iteratedDeriv r (fun s => greenParsevalAnalysis (f s)) t =
      greenParsevalAnalysis (iteratedDeriv r f t) := by
  induction r generalizing t with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have he : iteratedDeriv r (fun s => greenParsevalAnalysis (f s)) =
        fun s => greenParsevalAnalysis (iteratedDeriv r f s) := funext ih
    rw [he]
    exact greenParseval_deriv _ t

/-- All-order Hilbert regularity is equivalent before and after Parseval. -/
theorem greenParseval_contDiffAt_iff (f : ℝ → State) (n : ℕ∞ω) (t : ℝ) :
    ContDiffAt ℝ n (fun s => greenParsevalAnalysis (f s)) t ↔ ContDiffAt ℝ n f t := by
  constructor
  · intro h
    have hc := h.continuousLinearMap_comp (greenParsevalAnalysis.adjoint.restrictScalars ℝ)
    simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', parseval_left_inverse] using hc
  · intro h
    exact h.continuousLinearMap_comp (greenParsevalAnalysis.restrictScalars ℝ)

/-- Real pairings of full material vectors are preserved, not merely their norms. -/
theorem greenParseval_inner_real (x y : State) :
    inner ℝ (greenParsevalAnalysis x) (greenParsevalAnalysis y) = inner ℝ x y := by
  rw [real_inner_complex_re, real_inner_complex_re]
  exact congrArg Complex.re ((canonicalParseval canonicalRawGreenFrameBounds).inner_map_map x y)

/-- A moment representation is neither gained nor lost by the same Parseval map. -/
theorem greenParseval_parityMomentGram_iff (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → State) :
    IsParityMomentGramRepresentation moments (fun i => greenParsevalAnalysis (jet i)) ↔
      IsParityMomentGramRepresentation moments jet := by
  simp only [IsParityMomentGramRepresentation, Matrix.gram, greenParseval_inner_real]

/-- The existing factorial-normalized convention on the actual full C2 orbit. -/
def c2MaterialOrbitJet (V : CoreState) (r : ℕ) : State :=
  (r.factorial : ℂ)⁻¹ • iteratedDeriv r (fun t => c2GlobalGreenInputIsometry t V) 0

/-- Jets of the complete vector orbit after the actual Parseval synthesis. -/
def c2ParsevalOrbitJet (V : CoreState) (r : ℕ) : ConcreteAnalysisSpace :=
  (r.factorial : ℂ)⁻¹ • iteratedDeriv r
    (fun t => greenParsevalAnalysis (c2GlobalGreenInputIsometry t V)) 0

theorem c2ParsevalOrbitJet_eq_transport (V : CoreState) (r : ℕ) :
    c2ParsevalOrbitJet V r = greenParsevalAnalysis (c2MaterialOrbitJet V r) := by
  rw [c2ParsevalOrbitJet, greenParseval_iteratedDeriv, c2MaterialOrbitJet, map_smul]

theorem c2ParsevalOrbitJet_inner (V : CoreState) (r q : ℕ) :
    inner ℝ (c2ParsevalOrbitJet V r) (c2ParsevalOrbitJet V q) =
      inner ℝ (c2MaterialOrbitJet V r) (c2MaterialOrbitJet V q) := by
  rw [c2ParsevalOrbitJet_eq_transport, c2ParsevalOrbitJet_eq_transport, greenParseval_inner_real]

/-- First derivative has exactly the existing logarithmic-moment gate. -/
theorem c2ParsevalOrbit_differentiableAt_zero_iff_log_moment (V : CoreState) :
    DifferentiableAt ℝ (fun t => greenParsevalAnalysis (c2GlobalGreenInputIsometry t V)) 0 ↔
      Summable (fun n : PNat => (Real.log (n : ℝ))^2 *
        Complex.normSq (c2GlobalGreenInputIsometry 0 V n)) := by
  have he : (fun t => c2GlobalGreenInputIsometry t V) =
      (fun t => greenStateMaterialEvolution t (c2GlobalGreenInputIsometry 0 V)) := by
    funext t
    simpa using (c2GlobalGreenInput_evolution_add t 0 V).symm
  rw [greenParseval_differentiableAt_iff, he,
    greenStateMaterialEvolution_differentiableAt_zero_iff, c2Source_log_domain_iff]

/-- This is a preserved gate, not a proof that arbitrary core states are smooth. -/
theorem c2ParsevalOrbit_contDiffAt_iff (V : CoreState) (n : ℕ∞ω) (t : ℝ) :
    ContDiffAt ℝ n (fun s => greenParsevalAnalysis (c2GlobalGreenInputIsometry s V)) t ↔
      ContDiffAt ℝ n (fun s => c2GlobalGreenInputIsometry s V) t :=
  greenParseval_contDiffAt_iff _ n t

/-- Diagnostic first column of existing orbit jets; not claimed to be the
completed boundary Green first column required by the moment theorem. -/
def c2ParsevalOrbitFirstColumn (V : CoreState) (p : ℕ) : ℝ :=
  inner ℝ (c2ParsevalOrbitJet V (2*p)) (c2ParsevalOrbitJet V 0)

/-- Audit residual only; zero is neither assumed nor asserted. -/
def baseTwoCanonicalGreenFirstColumnResidual (V : CoreState) (p : ℕ) : ℝ :=
  c2ParsevalOrbitFirstColumn V p - baseTwoCanonicalMomentSequence p

theorem c2ParsevalOrbitFirstColumn_eq_material (V : CoreState) (p : ℕ) :
    c2ParsevalOrbitFirstColumn V p =
      inner ℝ (c2MaterialOrbitJet V (2*p)) (c2MaterialOrbitJet V 0) :=
  c2ParsevalOrbitJet_inner V _ _

/-- Parseval cannot remove a first-column discrepancy present in the material carrier. -/
theorem baseTwoCanonicalGreenFirstColumnResidual_eq_material (V : CoreState) (p : ℕ) :
    baseTwoCanonicalGreenFirstColumnResidual V p =
      inner ℝ (c2MaterialOrbitJet V (2*p)) (c2MaterialOrbitJet V 0) -
        baseTwoCanonicalMomentSequence p := by
  rw [baseTwoCanonicalGreenFirstColumnResidual, c2ParsevalOrbitFirstColumn_eq_material]

/-- The zeroth vector pairing remains the actual core norm, with no fitted normalization. -/
theorem c2ParsevalOrbitFirstColumn_zero (V : CoreState) :
    c2ParsevalOrbitFirstColumn V 0 = ‖V‖^2 := by
  simp only [c2ParsevalOrbitFirstColumn, c2ParsevalOrbitJet, mul_zero,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, iteratedDeriv_zero]
  rw [real_inner_self_eq_norm_sq, canonicalGreenAnalysis_norm, c2GlobalGreenInput_norm]

theorem baseTwoCanonicalGreenFirstColumnResidual_zero (V : CoreState) :
    baseTwoCanonicalGreenFirstColumnResidual V 0 = ‖V‖^2 - baseTwoCanonicalMomentSequence 0 := by
  rw [baseTwoCanonicalGreenFirstColumnResidual, c2ParsevalOrbitFirstColumn_zero]

end GeometryOfNumbers.Analysis.CanonicalGreenMomentSeam
