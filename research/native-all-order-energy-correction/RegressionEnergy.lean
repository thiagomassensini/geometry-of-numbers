import FiniteEnergy

namespace CarryEnergyCorrection
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Free coefficients of the same J4-a J2-b J0 family. -/
def quarticCoefficients (a b : ℝ) (r : ℕ) : ℝ :=
  if r=0 then -b else if r=1 then -a else if r=2 then 1 else 0

theorem finite_quartic_source (a b : ℝ) (k : ℕ) :
    finiteJetSource (Finset.range 3) (quarticCoefficients a b) k=
      radialJetCoefficients k 4-(a:ℂ) • radialJetCoefficients k 2-
        (b:ℂ) • radialJetCoefficients k 0 := by
  norm_num [finiteJetSource, Finset.sum_range_succ, quarticCoefficients]
  module

theorem finite_quartic_form (a b : ℝ) :
    canonicalForm (Finset.range 3) (quarticCoefficients a b)=
      h 4-2*a*h 3+(a^2-2*b)*h 2+2*a*b*h 1+b^2*h 0 := by
  norm_num [canonicalForm, Finset.sum_range_succ, quarticCoefficients]
  ring

theorem finite_quartic_correction (a b : ℝ) :
    canonicalCorrection (Finset.range 3) (quarticCoefficients a b)=
      -55*h 5+150*a*h 4-14*a^2*h 3+252*b*h 3-40*a*b*h 2-b^2*h 1 := by
  norm_num [canonicalCorrection, Finset.sum_range_succ, quarticCoefficients,
    spatialCorrection, curvature, CarrySpatialCorrection.slope]
  ring

/-- Recovery of the PR104 correction from the arbitrary finite-order theorem. -/
theorem quartic_correction_regression (a b : ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (fullEnergy k (radialJetCoefficients k 4-(a:ℂ) • radialJetCoefficients k 2-
        (b:ℂ) • radialJetCoefficients k 0)-
      (h 4-2*a*h 3+(a^2-2*b)*h 2+2*a*b*h 1+b^2*h 0))) atTop
      (nhds (-55*h 5+150*a*h 4-14*a^2*h 3+252*b*h 3-40*a*b*h 2-b^2*h 1)) := by
  simpa only [finite_quartic_source, finite_quartic_form, finite_quartic_correction] using
    finite_energy_correction_tendsto (Finset.range 3) (quarticCoefficients a b)

/-- The native signed form keeps its ORIGINAL factor 1/2. -/
theorem original_norm_difference (k : ℕ) (c : ℕ →₀ ℂ) :
    2*fullEnergy k c=‖(physicalCompletedFiniteSource k c).1‖^2-
      ‖(physicalCompletedFiniteSource k c).2‖^2 := by
  unfold fullEnergy canonicalCompletedNativeProjectiveChiralForm
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
  norm_num [Complex.mul_re, Complex.sub_re, ← Complex.ofReal_pow]
  ring

/-- Same theorem for the complete incidence-minus-return balance. -/
theorem finite_norm_difference_correction (S : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (‖(physicalCompletedFiniteSource k (finiteJetSource S c k)).1‖^2-
        ‖(physicalCompletedFiniteSource k (finiteJetSource S c k)).2‖^2-
          2*canonicalForm S c)) atTop (nhds (2*canonicalCorrection S c)) := by
  have ht := (tendsto_const_nhds (x := (2:ℝ))).mul (finite_energy_correction_tendsto S c)
  apply ht.congr'
  filter_upwards [] with k
  rw [← original_norm_difference]
  ring

end
end CarryEnergyCorrection
