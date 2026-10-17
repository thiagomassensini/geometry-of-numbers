import PrimeCameraGramComparison
import PrimeClockCanonicalGate

/-! A completely concrete literal matrix, from the existing native stencils
of cameras 2 and 3 at camera cutoff one. Its Gram is computed from those
stencils, never selected from the desired Hankel. -/
namespace CarryPrimeClock
open CarrySelfAdjointOperator NativeCarryC3Crosswalk
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open NativeCarrySpectralWeyl.Limits NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open scoped BigOperators InnerProductSpace Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem literal_two_camera_gram :
    finiteCameraRowGram (finiteLiteralCameraMatrix 1 twoPrimeCameras) =
      !![(7:ℝ),-3; -3,7] := by
  ext i j
  rw [finiteLiteralCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram
    (by intro i; fin_cases i <;> norm_num [twoPrimeCameras])]
  fin_cases i <;> fin_cases j <;>
    norm_num [twoPrimeCameras, literalFiniteCameraGram, pairFiniteWindow,
      finiteCameraWindow, cameraSlope, cameraBoundaryWidth, finiteCoefficientAt,
      finiteCoefficient, seedCoefficient, centerCoefficient, bracketCoefficient,
      FiniteNativeCarryOperator.Camera.radiusSet,
      FiniteNativeCarryOperator.Camera.halfRange,
      FiniteNativeCarryOperator.Camera.alignedCenter, Finset.sum_range_succ]

theorem literal_two_camera_gram_posDef :
    (finiteCameraRowGram (finiteLiteralCameraMatrix 1 twoPrimeCameras)).PosDef := by
  rw [literal_two_camera_gram]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  · intro x hx
    have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h.1, h.2]
    have hp : 0 < (x 0)^2+(x 1)^2 := by
      rcases hn with h|h
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 1)]
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0)]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, star_trivial,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    nlinarith [sq_nonneg (x 0-x 1)]

/-- Unconditional realization of the SAME completed clock by the concrete
literal camera encoder, its decoder, coherent addition, full return and tail. -/
theorem literal_decoded_clock_eq (t : ℝ) :
    decodedCompleteClock (finiteLiteralCameraMatrix 1 twoPrimeCameras) t = physicalClock t :=
  decodedCompleteClock_eq _ literal_two_camera_gram_posDef t

theorem literal_decoded_clock_pairing (t u : ℝ) :
    inner ℂ (decodedCompleteClock (finiteLiteralCameraMatrix 1 twoPrimeCameras) t)
      (decodedCompleteClock (finiteLiteralCameraMatrix 1 twoPrimeCameras) u) =
      inner ℂ (physicalClock t) (physicalClock u) :=
  decodedCompleteClock_pairing _ literal_two_camera_gram_posDef t u

theorem literal_enriched_clock_source (t : ℝ) :
    enrichedClockDecoder (finiteLiteralCameraMatrix 1 twoPrimeCameras)
      (enrichedPrimeClockInput (finiteLiteralCameraMatrix 1 twoPrimeCameras) t) =
        physicalClock t :=
  enrichedClockDecoder_source _ literal_two_camera_gram_posDef t

theorem literal_enriched_clock_pairing (t u : ℝ) :
    inner ℂ
      (enrichedClockDecoder (finiteLiteralCameraMatrix 1 twoPrimeCameras)
        (enrichedPrimeClockInput (finiteLiteralCameraMatrix 1 twoPrimeCameras) t))
      (enrichedClockDecoder (finiteLiteralCameraMatrix 1 twoPrimeCameras)
        (enrichedPrimeClockInput (finiteLiteralCameraMatrix 1 twoPrimeCameras) u)) =
      inner ℂ (physicalClock t) (physicalClock u) := by
  rw [literal_enriched_clock_source, literal_enriched_clock_source]

theorem literal_whitened_origin_gap :
    ‖finiteCanonicalCameraHilbertSynthesis (finiteLiteralCameraMatrix 1 twoPrimeCameras)
        (twoPrimeFamily 0)‖^2 - ‖coherentPrefix 2 0‖^2 =
      2*(Real.log 2/Real.sqrt 2)*(Real.log 3/Real.sqrt 3) :=
  whitened_coherent_origin_gap _ literal_two_camera_gram_posDef

end
end CarryPrimeClock
