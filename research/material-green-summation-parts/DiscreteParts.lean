import GreenTransport

/-! Exact polarized summation by parts on the MATERIAL index. The existing
fdiff/bracket stencil is evaluated on explicitly shifted material samples;
no material index is identified with a vertical carry depth. -/
namespace CarryMaterialParts
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion DiscreteValve
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

/-- Endpoint flux, with both arguments independent. -/
def endpointFlux (f g : ℕ → ℂ) (N : ℕ) : ℂ :=
  conj (f N)*fdiff g N-conj (f 0)*fdiff g 0

/-- The curvature is the original three-point bracket, not a new Laplacian. -/
def curvatureBulk (f g : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, conj (f (n+1))*bracket g n

theorem polarized_summation_parts (f g : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, conj (fdiff f n)*fdiff g n) =
      endpointFlux f g N-curvatureBulk f g N := by
  induction N with
  | zero => simp [endpointFlux, curvatureBulk]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [endpointFlux, curvatureBulk, Finset.sum_range_succ, fdiff, bracket,
      map_sub, nsmul_eq_mul, Nat.cast_ofNat]
    ring

/-- The native ordinary sample sequence, before either quadrature readout. -/
def ordinarySamples (t : ℝ) (n : ℕ) : ℂ := criticalMaterialSample t (n+1)

/-- Original material log multiplier; it is not a moment-driven operator. -/
def clockSamples (t : ℝ) (n : ℕ) : ℂ :=
  (Real.log ((n+1:ℕ):ℝ):ℂ)*criticalMaterialSample t (n+1)

theorem ordinary_difference (t : ℝ) (n : ℕ) :
    fdiff (ordinarySamples t) n = criticalMaterialGradient t n := rfl

theorem clock_difference (t : ℝ) (n : ℕ) :
    fdiff (clockSamples t) n = baseTwoCompletedMaterialClockL2 t n := by
  rw [baseTwoCompletedMaterialClockL2_apply, baseTwoCompletedBoundaryHilbertClockCoordinate_eq]
  rfl

theorem ordinary_clock_parts (t u : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, conj (criticalMaterialGradient t n)*baseTwoCompletedMaterialClockL2 u n) =
      endpointFlux (ordinarySamples t) (clockSamples u) N-
        curvatureBulk (ordinarySamples t) (clockSamples u) N := by
  simpa only [ordinary_difference, clock_difference] using
    polarized_summation_parts (ordinarySamples t) (clockSamples u) N

theorem clock_ordinary_parts (t u : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, conj (baseTwoCompletedMaterialClockL2 t n)*criticalMaterialGradient u n) =
      endpointFlux (clockSamples t) (ordinarySamples u) N-
        curvatureBulk (clockSamples t) (ordinarySamples u) N := by
  simpa only [ordinary_difference, clock_difference] using
    polarized_summation_parts (clockSamples t) (ordinarySamples u) N

end
end CarryMaterialParts
