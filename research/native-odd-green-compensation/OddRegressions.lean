import OddHankelTransport
import GeometryOfNumbers.Analysis.LogarithmicMomentHankel
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

namespace CarryOddGreen
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

theorem odd_linear_residual (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 (monomialWeight 1) (nativeOddProfile 0) 2=
      (Complex.I*(eta:ℂ)) •
        (-greenColumn eta h0 h1 1+greenColumn eta h0 h1 2) := by
  simpa only [pow_one,show (1:ℂ)-2= -1 by norm_num,
    show (3:ℂ)-2=1 by norm_num,neg_one_smul,one_smul] using odd_residual_vector 1 eta h0 h1

theorem odd_cubic_residual (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 (monomialWeight 3) (nativeOddProfile 0) 2=
      (Complex.I*(eta:ℂ)) •
        ((-7:ℂ) • greenColumn eta h0 h1 1+(19:ℂ) • greenColumn eta h0 h1 2) := by
  simpa only [show (2:ℂ)^3=8 by norm_num,show (3:ℂ)^3=27 by norm_num,
    show (1:ℂ)-8= -7 by norm_num,show (27:ℂ)-8=19 by norm_num] using odd_residual_vector 3 eta h0 h1

/-- The two EXISTING definitions of the canonical odd matrix agree literally. -/
theorem shifted_hankel_eq_source (N : ℕ) :
    GeometryOfNumbers.Analysis.shiftedHankel h N=sourceMomentMatrix h 1 N := rfl

/-- Every entry of the original shifted Hankel, from the SAME independent
native odd radial jets. The ambient form remains explicitly SIGNED. -/
theorem odd_matrix_entry_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k : ℕ => signedPair k
      (radialJetCoefficients k (2*(i:ℕ)+1)) (radialJetCoefficients k (2*(j:ℕ)+1))) atTop
      (nhds ((sourceMomentMatrix h 1 N i j:ℝ):ℂ)) := by
  change Tendsto (fun k : ℕ => signedPair k
    (radialJetCoefficients k (2*(i:ℕ)+1)) (radialJetCoefficients k (2*(j:ℕ)+1))) atTop
    (nhds (h ((i:ℕ)+(j:ℕ)+1):ℂ))
  have he := odd_pairing_tendsto {(i:ℕ)} {(j:ℕ)} (fun _ => 1) (fun _ => 1)
  have hv : (oddBilinear {(i:ℕ)} {(j:ℕ)} (fun _ => 1) (fun _ => 1):ℂ)=
      (h ((i:ℕ)+(j:ℕ)+1):ℂ) := by simp [oddBilinear]
  rw [hv] at he
  apply he.congr'
  filter_upwards [] with k
  simp only [oddPairing,finiteOddJetSource,Finset.sum_singleton,Complex.ofReal_one,one_smul]

/-- The full Green reconstruction has the same entry limit: no bulk/boundary
or residual crossing is projected away. -/
theorem odd_matrix_green_entry_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (N : ℕ) (i j : Fin N) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k
      (radialJetCoefficients k (2*(i:ℕ)+1)) (radialJetCoefficients k (2*(j:ℕ)+1))) atTop
      (nhds ((sourceMomentMatrix h 1 N i j:ℝ):ℂ)) := by
  have he := odd_green_pairing_tendsto eta h0 h1 {(i:ℕ)} {(j:ℕ)} (fun _ => 1) (fun _ => 1)
  simpa [finiteOddJetSource,oddBilinear,sourceMomentMatrix] using he

/-- Real projection only AFTER the full complex synthesis and its limit. -/
theorem odd_matrix_entry_real_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k : ℕ => (signedPair k
      (radialJetCoefficients k (2*(i:ℕ)+1)) (radialJetCoefficients k (2*(j:ℕ)+1))).re) atTop
      (nhds (GeometryOfNumbers.Analysis.shiftedHankel h N i j)) := by
  have he := Complex.continuous_re.continuousAt.tendsto.comp (odd_matrix_entry_tendsto N i j)
  simpa only [Function.comp_def,Complex.ofReal_re,GeometryOfNumbers.Analysis.shiftedHankel,sourceMomentMatrix] using he

/-- Reindexing only: the polarized native readout is the EXISTING matrix K_N. -/
theorem odd_bilinear_eq_matrix (N : ℕ) (c d : ℕ → ℝ) :
    oddBilinear (Finset.range N) (Finset.range N) c d=
      ∑ i : Fin N, ∑ j : Fin N, c i*d j*sourceMomentMatrix h 1 N i j := by
  unfold oddBilinear
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_range]
  rfl

/-- Full two-input MATRIX form, with all crosses and arbitrary finite order. -/
theorem odd_matrix_bilinear_tendsto (N : ℕ) (c d : ℕ → ℝ) :
    Tendsto (oddPairing (Finset.range N) (Finset.range N) c d) atTop
      (nhds ((∑ i : Fin N, ∑ j : Fin N, c i*d j*sourceMomentMatrix h 1 N i j:ℝ):ℂ)) := by
  simpa only [odd_bilinear_eq_matrix] using odd_pairing_tendsto (Finset.range N) (Finset.range N) c d

/-- The SAME polarized matrix form after complete nine-cross Green synthesis. -/
theorem odd_matrix_green_bilinear_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (N : ℕ) (c d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => crossGreenPair eta h0 h1 k k
      (finiteOddJetSource (Finset.range N) c k) (finiteOddJetSource (Finset.range N) d k)) atTop
      (nhds ((∑ i : Fin N, ∑ j : Fin N, c i*d j*sourceMomentMatrix h 1 N i j:ℝ):ℂ)) := by
  simpa only [odd_bilinear_eq_matrix] using
    odd_green_pairing_tendsto eta h0 h1 (Finset.range N) (Finset.range N) c d

/-- Compatibility with the preexisting diagonal odd form, not a new moment sequence. -/
theorem odd_bilinear_diagonal_eq (S : Finset ℕ) (c : ℕ → ℝ) :
    oddBilinear S S c c=oddCanonicalForm S c := rfl

end
end CarryOddGreen
