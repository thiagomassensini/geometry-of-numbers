import DoubledMixedExpansion
import ImaginaryRegression
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy

namespace CarryCrossRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The exact diagonal recovers the old literal first mixed source. -/
theorem first_cross_diagonal (k : ℕ) : firstCrossPair k k=firstMixedPair k := rfl

theorem first_cross_diagonal_scaled_tendsto :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*firstCrossPair k k) atTop
      (nhds (2*Complex.I*(h 1:ℂ))) := by
  simpa only [first_cross_diagonal] using CarryMixedImaginary.first_mixed_from_all_order

/-- Nonvanishing is separated from the sign-free source expansion. -/
theorem doubled_leading_eq_zero_iff : doubledLeading=0 ↔ h 0=0 := by
  have hs : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hf : Complex.I*(Real.sqrt 2:ℂ)/6≠0 :=
    div_ne_zero (mul_ne_zero Complex.I_ne_zero hs) (by norm_num)
  have he : doubledLeading=(Complex.I*(Real.sqrt 2:ℂ)/6)*(h 0:ℂ) := by
    unfold doubledLeading; ring
  simp only [he, mul_eq_zero, hf, false_or, Complex.ofReal_eq_zero]

/-- A finite limit of the unaltered doubled-radial pair would force h0=0. -/
theorem doubled_finite_limit_forces_h0_zero {L : ℂ}
    (hL : Tendsto doubledFirstPair atTop (nhds L)) : h 0=0 := by
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have hz := ht.mul hL
  simp only [zero_mul] at hz
  exact doubled_leading_eq_zero_iff.mp (tendsto_nhds_unique doubled_scaled_tendsto hz)

theorem doubled_no_finite_limit_of_h0_ne_zero (hn : h 0≠0) :
    ¬ ∃ L : ℂ, Tendsto doubledFirstPair atTop (nhds L) := by
  rintro ⟨L,hL⟩
  exact hn (doubled_finite_limit_forces_h0_zero hL)

/-- Isolated strict obstruction using ONLY the PREEXISTING first theta/native
sign certificate. No such sign is used in any identity or expansion above. -/
theorem doubled_no_finite_limit :
    ¬ ∃ L : ℂ, Tendsto doubledFirstPair atTop (nhds L) := by
  apply doubled_no_finite_limit_of_h0_ne_zero
  exact canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'

/-- Final imaginary projection of the already synthesized complex path. -/
theorem doubled_imaginary_scaled_tendsto :
    Tendsto (fun k : ℕ => radialStep k*(doubledFirstPair k).im) atTop
      (nhds (Real.sqrt 2*h 0/6)) := by
  have hh := Complex.continuous_im.continuousAt.tendsto.comp doubled_scaled_tendsto
  simpa [Function.comp_def, doubledLeading, Complex.mul_im] using hh

end
end CarryCrossRadial
