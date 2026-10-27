import OddVectors

namespace CarryOddGreen
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- Exact cancellation of the 3^d terms in the ORIGINAL bulk plus residual,
while retaining the 2^d response and both Green columns as vectors. -/
theorem odd_bulk_residual_cancellation (d : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 (monomialWeight d) (nativeOddProfile 0) 0+
      partField eta h0 h1 (monomialWeight d) (nativeOddProfile 0) 2=
      Complex.I •
        (((2:ℂ)^(d+1)+(eta:ℂ)) • greenColumn eta h0 h1 1-
          ((eta:ℂ)*(2:ℂ)^d) • greenColumn eta h0 h1 2) := by
  rw [odd_bulk_vector,odd_residual_vector,pow_succ]
  module

/-- Complete vector reconstruction. The odd native phase and the second
material address remain; this is not a normalization of the source. -/
theorem odd_complete_vector_reconstruction (d : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    (∑ a : Fin 3, partField eta h0 h1 (monomialWeight d) (nativeOddProfile 0) a)=
      Complex.I • completedNativeChiralCauchyFeature 0+
      (-Complex.I*(2:ℂ)^d) • completedNativeChiralCauchyFeature 1 := by
  rw [part_field_reconstruction,odd_weighted_coefficients]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single]

/-- All three explicit original vectors, including BOTH traces, are recomposed
before any inner product or real/imaginary readout. -/
theorem odd_three_vector_identity (d : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ((Complex.I*((2:ℂ)^d*(2+(eta:ℂ)))) • greenColumn eta h0 h1 1+
      (-Complex.I*(eta:ℂ)*(3:ℂ)^d) • greenColumn eta h0 h1 2)+
    Complex.I • (traceColumn eta h0 h1 0-
      ((2:ℂ)^d+2*(eta:ℂ)) • traceColumn eta h0 h1 1)+
    (Complex.I*(eta:ℂ)) •
      ((1-(2:ℂ)^d) • greenColumn eta h0 h1 1+
       ((3:ℂ)^d-(2:ℂ)^d) • greenColumn eta h0 h1 2)=
    Complex.I • completedNativeChiralCauchyFeature 0+
      (-Complex.I*(2:ℂ)^d) • completedNativeChiralCauchyFeature 1 := by
  have h := odd_complete_vector_reconstruction d eta h0 h1
  rw [Fin.sum_univ_three,odd_bulk_vector,odd_boundary_vector,odd_residual_vector] at h
  exact h

/-- The TWO original legs of the radial odd jet, before any signed pairing. -/
theorem odd_physical_jet_calibration (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k : ℕ) (a : Fin 3) :
    completedSourceParts eta h0 h1 k (radialJetCoefficients k 1) a=
      ((k:ℂ)+1) • completedSourceParts eta h0 h1 k (nativeOddProfile 0) a := by
  rw [odd_profile_radial_jet,completed_part_scale_input]

end
end CarryOddGreen
