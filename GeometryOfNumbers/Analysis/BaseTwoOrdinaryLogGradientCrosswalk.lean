import GeometryOfNumbers.Analysis.CompletedMaterialGradientStrongClock

/-!
# Ordinary and logarithmic material-edge gradients

Both channels keep the consecutive material edge n+1 -> n+2. The clock
channel is identified with its explicit complex-power formula before using
its derivative law. No material edge is reinterpreted as a vertical depth.
The product uses the standard Hilbert norm and the existing completed vectors.
-/
noncomputable section
open scoped BigOperators lp ENNReal Topology
open Filter
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- Explicit ordinary Dirichlet difference on the existing native line. -/
def baseTwoNativeOrdinaryGradientFormula (t : ℝ) (n : ℕ) : ℂ :=
  ((n+2 : ℕ) : ℂ)^(-baseTwoDressingParameter (t : ℂ)) -
    ((n+1 : ℕ) : ℂ)^(-baseTwoDressingParameter (t : ℂ))

/-- Logarithmic companion, defined by material powers, not by differentiation. -/
def baseTwoNativeLogGradientFormula (t : ℝ) (n : ℕ) : ℂ :=
  (Real.log ((n+2 : ℕ) : ℝ) : ℂ) *
      ((n+2 : ℕ) : ℂ)^(-baseTwoDressingParameter (t : ℂ)) -
    (Real.log ((n+1 : ℕ) : ℝ) : ℂ) *
      ((n+1 : ℕ) : ℂ)^(-baseTwoDressingParameter (t : ℂ))

theorem criticalMaterialGradient_eq_nativeOrdinaryFormula (t : ℝ) (n : ℕ) :
    criticalMaterialGradient t n = baseTwoNativeOrdinaryGradientFormula t n :=
  criticalMaterialGradient_eq_nativeLinePowerDifference t n

/-- The transported triangular clock is exactly the logarithmic difference. -/
theorem baseTwoCompletedClockCoordinate_eq_nativeLogFormula (t : ℝ) (n : ℕ) :
    baseTwoCompletedBoundaryHilbertClockCoordinate
      (baseTwoCompletedBoundaryHilbertState t) n = baseTwoNativeLogGradientFormula t n := by
  have he : criticalMaterialExponent t = -baseTwoDressingParameter (t : ℂ) := by
    unfold criticalMaterialExponent baseTwoDressingParameter
    ring
  rw [baseTwoCompletedBoundaryHilbertClockCoordinate_eq,
    criticalMaterialSample_eq_cpow t (by omega),
    criticalMaterialSample_eq_cpow t (by omega), he]
  rfl

/-- The sign is -i; the logarithmic channel was defined independently above. -/
theorem criticalMaterialGradient_hasDerivAt_nativeLogFormula (t : ℝ) (n : ℕ) :
    HasDerivAt (fun u => criticalMaterialGradient u n)
      (-Complex.I * baseTwoNativeLogGradientFormula t n) t := by
  have h := criticalMaterialGradient_hasDerivAt t n
  rw [← baseTwoCompletedBoundaryHilbertClockCoordinate_eq,
    baseTwoCompletedClockCoordinate_eq_nativeLogFormula] at h
  exact h

theorem criticalMaterialGradient_deriv_eq_nativeLogFormula (t : ℝ) (n : ℕ) :
    deriv (fun u => criticalMaterialGradient u n) t =
      -Complex.I * baseTwoNativeLogGradientFormula t n :=
  (criticalMaterialGradient_hasDerivAt_nativeLogFormula t n).deriv

/-- Standard product Hilbert carrier; both labels are material edges. -/
abbrev BaseTwoOrdinaryLogGradientCarrier := WithLp 2 (MaterialEdgeL2 × MaterialEdgeL2)

/-- Reuse the completed finite-energy channels; no nodal decoding occurs. -/
def baseTwoOrdinaryLogGradientState (t : ℝ) : BaseTwoOrdinaryLogGradientCarrier :=
  WithLp.toLp 2 (baseTwoCompletedMaterialGradientL2 t, baseTwoCompletedMaterialClockL2 t)

@[simp] theorem baseTwoOrdinaryLogGradientState_ordinary (t : ℝ) :
    (baseTwoOrdinaryLogGradientState t).fst = baseTwoCompletedMaterialGradientL2 t := rfl

@[simp] theorem baseTwoOrdinaryLogGradientState_log (t : ℝ) :
    (baseTwoOrdinaryLogGradientState t).snd = baseTwoCompletedMaterialClockL2 t := rfl

@[simp] theorem baseTwoOrdinaryLogGradientState_ordinary_apply (t : ℝ) (n : ℕ) :
    (baseTwoOrdinaryLogGradientState t).fst n = baseTwoNativeOrdinaryGradientFormula t n :=
  criticalMaterialGradient_eq_nativeOrdinaryFormula t n

@[simp] theorem baseTwoOrdinaryLogGradientState_log_apply (t : ℝ) (n : ℕ) :
    (baseTwoOrdinaryLogGradientState t).snd n = baseTwoNativeLogGradientFormula t n :=
  baseTwoCompletedClockCoordinate_eq_nativeLogFormula t n

/-- Energy of the pair, in the unmodified product norm. -/
theorem baseTwoOrdinaryLogGradientState_norm_sq (t : ℝ) :
    ‖baseTwoOrdinaryLogGradientState t‖^2 =
      ‖baseTwoCompletedMaterialGradientL2 t‖^2 + ‖baseTwoCompletedMaterialClockL2 t‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

/-- Truncate the two difference channels directly, never reconstructed nodes. -/
def baseTwoOrdinaryLogGradientPrefixState (N : ℕ) (t : ℝ) :
    BaseTwoOrdinaryLogGradientCarrier :=
  WithLp.toLp 2
    (∑ n ∈ Finset.range N, lp.single 2 n (baseTwoCompletedMaterialGradientL2 t n),
     ∑ n ∈ Finset.range N, lp.single 2 n (baseTwoCompletedMaterialClockL2 t n))

private theorem materialEdgePrefix_tendsto (x : MaterialEdgeL2) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, lp.single 2 n (x n)) atTop (𝓝 x) := by
  exact (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat

/-- Norm convergence of the entire pair follows from its two existing lp states. -/
theorem baseTwoOrdinaryLogGradientPrefixState_tendsto (t : ℝ) :
    Tendsto (fun N => baseTwoOrdinaryLogGradientPrefixState N t) atTop
      (𝓝 (baseTwoOrdinaryLogGradientState t)) := by
  have hp := (materialEdgePrefix_tendsto (baseTwoCompletedMaterialGradientL2 t)).prodMk_nhds
    (materialEdgePrefix_tendsto (baseTwoCompletedMaterialClockL2 t))
  exact (WithLp.prod_continuous_toLp 2 MaterialEdgeL2 MaterialEdgeL2).continuousAt.tendsto.comp hp

end GeometryOfNumbers.Analysis.BaseTwoCompletion
