import OddFiniteEnergy

namespace CarryOddEnergy
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The first odd input retains its two imaginary coefficients. -/
theorem odd_profile_zero : nativeOddProfile 0=
    Finsupp.single 0 Complex.I+Finsupp.single 1 (-Complex.I) := by
  ext j
  simp only [nativeOddProfile, staticStencil, Finsupp.smul_apply, smul_eq_mul,
    raw_stencil_apply]
  rcases j with _ | _ | j
  all_goals try { norm_num [completedGreenForwardWeight, Nat.factorial] }

/-- The cubic odd input retains all four addresses and its original 3!. -/
theorem odd_profile_one : nativeOddProfile 1=
    Finsupp.single 0 (-Complex.I/6)+Finsupp.single 1 (Complex.I/2)+
      Finsupp.single 2 (-Complex.I/2)+Finsupp.single 3 (Complex.I/6) := by
  ext j
  simp only [nativeOddProfile, staticStencil, Finsupp.smul_apply, smul_eq_mul,
    raw_stencil_apply]
  rcases j with _ | _ | _ | _ | j
  all_goals try { norm_num [completedGreenForwardWeight, Nat.choose, Nat.factorial]; ring }
  simp [completedGreenForwardWeight, Nat.choose_eq_zero_of_lt (show 3 < j+4 by omega)]

theorem odd_coefficient_regression :
    spatialCorrection 1 1=5 ∧ spatialCorrection 1 3=42 ∧ spatialCorrection 3 3=30 := by
  norm_num [spatialCorrection, curvature, CarrySpatialCorrection.slope]

/-- This coefficient table is not a positive Gram, even in the odd sector.
It is a coefficient-only control, not a negative canonical Hankel pivot. -/
theorem odd_coefficient_minor_negative :
    (spatialCorrection 1 1).re*(spatialCorrection 3 3).re-
      (spatialCorrection 1 3).re^2= -1614 := by
  norm_num [spatialCorrection, curvature, CarrySpatialCorrection.slope]

/-- The first shifted moment and its correction, with the SAME native J1. -/
theorem first_odd_correction :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (fullEnergy k (radialJetCoefficients k 1)-h 1)) atTop (nhds (-5*h 2)) := by
  have ht := finite_odd_energy_correction_tendsto {0} (fun _ => 1)
  norm_num [finiteOddJetSource, oddCanonicalForm, oddCanonicalCorrection,
    spatialCorrection, curvature, CarrySpatialCorrection.slope] at ht
  simpa only [neg_mul] using ht

def cubicOddCoefficients (a : ℝ) (r : ℕ) : ℝ :=
  if r=0 then -a else if r=1 then 1 else 0

theorem odd_cubic_source (a : ℝ) (k : ℕ) :
    finiteOddJetSource (Finset.range 2) (cubicOddCoefficients a) k=
      radialJetCoefficients k 3-(a:ℂ) • radialJetCoefficients k 1 := by
  norm_num [finiteOddJetSource, Finset.sum_range_succ, cubicOddCoefficients]
  module

theorem odd_cubic_form (a : ℝ) :
    oddCanonicalForm (Finset.range 2) (cubicOddCoefficients a)=
      h 3-2*a*h 2+a^2*h 1 := by
  norm_num [oddCanonicalForm, Finset.sum_range_succ, cubicOddCoefficients]
  ring

theorem odd_cubic_correction (a : ℝ) :
    oddCanonicalCorrection (Finset.range 2) (cubicOddCoefficients a)=
      -30*h 4+84*a*h 3-5*a^2*h 2 := by
  norm_num [oddCanonicalCorrection, Finset.sum_range_succ, cubicOddCoefficients,
    spatialCorrection, curvature, CarrySpatialCorrection.slope]
  ring

theorem odd_cubic_correction_tendsto (a : ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (fullEnergy k (radialJetCoefficients k 3-(a:ℂ) • radialJetCoefficients k 1)-
        (h 3-2*a*h 2+a^2*h 1))) atTop (nhds (-30*h 4+84*a*h 3-5*a^2*h 2)) := by
  simpa only [odd_cubic_source, odd_cubic_form, odd_cubic_correction] using
    finite_odd_energy_correction_tendsto (Finset.range 2) (cubicOddCoefficients a)

/-- The signed incidence-minus-return balance keeps its original factor TWO. -/
theorem finite_odd_norm_difference_correction (S : Finset ℕ) (c : ℕ → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2*
      (‖(physicalCompletedFiniteSource k (finiteOddJetSource S c k)).1‖^2-
        ‖(physicalCompletedFiniteSource k (finiteOddJetSource S c k)).2‖^2-
          2*oddCanonicalForm S c)) atTop (nhds (2*oddCanonicalCorrection S c)) := by
  have ht := (tendsto_const_nhds (x := (2:ℝ))).mul (finite_odd_energy_correction_tendsto S c)
  apply ht.congr'
  filter_upwards [] with k
  rw [← original_norm_difference]
  ring

end
end CarryOddEnergy
