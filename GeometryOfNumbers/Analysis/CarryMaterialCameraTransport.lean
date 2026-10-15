import GeometryOfNumbers.Analysis.CarryMaterialSourceRealization

/-! Both camera readouts act on the SAME completed material source. The
integer cells, their different radii and ordered crossings remain explicit.
No new free field, positive Gram realization or height operator is used. -/
namespace GeometryOfNumbers.Analysis
open Geometry BaseTwoCompletion
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

def carryMaterialCameraReadout (cell : IntegerCameraCell) :
    BaseTwoCompletedBoundaryHilbertCarrier →L[ℂ] ℂ :=
  carryMaterialPointReadout (integerCameraPoint cell .left).toNat -
    2 • carryMaterialPointReadout (integerCameraPoint cell .center).toNat +
    carryMaterialPointReadout (integerCameraPoint cell .right).toNat

theorem carryMaterialCameraReadout_apply (cell : IntegerCameraCell)
    (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialCameraReadout cell y =
      carryMaterialPointReadout (integerCameraPoint cell .left).toNat y -
        2 * carryMaterialPointReadout (integerCameraPoint cell .center).toNat y +
        carryMaterialPointReadout (integerCameraPoint cell .right).toNat y := by
  simp [carryMaterialCameraReadout]

theorem carryMaterialCameraReadout_source (cell : IntegerCameraCell)
    (hp : ∀ r, 0 < integerCameraPoint cell r) (t : ℝ) :
    carryMaterialCameraReadout cell (baseTwoCompletedBoundaryHilbertState t) =
      criticalMaterialSample t (integerCameraPoint cell .left).toNat -
        2 * criticalMaterialSample t (integerCameraPoint cell .center).toNat +
        criticalMaterialSample t (integerCameraPoint cell .right).toNat := by
  rw [carryMaterialCameraReadout_apply,
    carryMaterialPointReadout_source _ (by have := hp .left; omega),
    carryMaterialPointReadout_source _ (by have := hp .center; omega),
    carryMaterialPointReadout_source _ (by have := hp .right; omega)]

def carryMaterialRealCamera (cell : IntegerCameraCell) (t : ℝ) : RealPlaneState :=
  ((carryMaterialCameraReadout cell (baseTwoCompletedBoundaryHilbertState t)).re,
    (carryMaterialCameraReadout cell (baseTwoCompletedBoundaryHilbertState t)).im)

/-- Exact specialization of PR 1's incidence readout to the existing source. -/
theorem carryMaterialRealCamera_eq_integerReadout (cell : IntegerCameraCell)
    (hp : ∀ r, 0 < integerCameraPoint cell r) (t : ℝ) :
    carryMaterialRealCamera cell t =
      integerCameraReadout cell (fun n => carryMaterialRealSample t n.toNat) := by
  rw [carryMaterialRealCamera, carryMaterialCameraReadout_source cell hp]
  apply Prod.ext <;>
    simp [integerCameraReadout, carryMaterialRealSample, realPlaneCenteredReadout,
      realCenteredReadout, Complex.mul_re, Complex.mul_im]

/-- Exact linear identity on the original completed carrier. The two new
outer edges are retained; common center cancellation is proved, not assumed. -/
theorem carryMaterialCamera72_transport (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialCameraReadout integerCamera72Three y =
      carryMaterialCameraReadout integerCamera72Two y + (y.snd.fst 79 - y.snd.fst 62) := by
  have hi := carryMaterialPointReadout_step 79 y
  have hl := carryMaterialPointReadout_step 62 y
  simp only [carryMaterialCameraReadout_apply]
  norm_num [integerCameraPoint, integerCameraCenter, integerCameraRadius,
    integerCamera72Two, integerCamera72Three, leftLeg, rightLeg] at hi hl ⊢
  change carryMaterialPointReadout 63 y - 2 * carryMaterialPointReadout 72 y +
      carryMaterialPointReadout 81 y =
    carryMaterialPointReadout 64 y - 2 * carryMaterialPointReadout 72 y +
      carryMaterialPointReadout 80 y + (y.snd.fst 79 - y.snd.fst 62)
  linear_combination hi - hl

theorem carryMaterialCamera72_source_transport (t : ℝ) :
    carryMaterialCameraReadout integerCamera72Three (baseTwoCompletedBoundaryHilbertState t) =
      carryMaterialCameraReadout integerCamera72Two (baseTwoCompletedBoundaryHilbertState t) +
        (criticalMaterialGradient t 79 - criticalMaterialGradient t 62) := by
  simpa only [baseTwoCompletedBoundaryHilbertState_interior,
    baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply] using
      carryMaterialCamera72_transport (baseTwoCompletedBoundaryHilbertState t)

theorem carryMaterialCamera72_source_values (t : ℝ) :
    carryMaterialCameraReadout integerCamera72Two (baseTwoCompletedBoundaryHilbertState t) =
      criticalMaterialSample t 64 - 2 * criticalMaterialSample t 72 + criticalMaterialSample t 80 ∧
    carryMaterialCameraReadout integerCamera72Three (baseTwoCompletedBoundaryHilbertState t) =
      criticalMaterialSample t 63 - 2 * criticalMaterialSample t 72 + criticalMaterialSample t 81 := by
  constructor
  · simpa [integerCameraPoint, integerCameraCenter, integerCameraRadius,
      integerCamera72Two, leftLeg, rightLeg] using
      carryMaterialCameraReadout_source integerCamera72Two
        (by intro r; cases r <;> decide) t
  · simpa [integerCameraPoint, integerCameraCenter, integerCameraRadius,
      integerCamera72Three, leftLeg, rightLeg] using
      carryMaterialCameraReadout_source integerCamera72Three
        (by intro r; cases r <;> decide) t

/-- The actual prescribed source has a nonzero transport defect already
at zero phase. These rational square-root bounds are exact, not a numerical
positivity test or a counterexample with independently chosen camera fields. -/
theorem carryMaterialCamera72_defect_zero_positive :
    0 < (criticalMaterialGradient 0 79 - criticalMaterialGradient 0 62).re := by
  have hs63 : 0 < Real.sqrt (63 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs80 : 0 < Real.sqrt (80 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq63 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 63)
  have hsq80 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 80)
  have hb63 : 7937 / 1000 < Real.sqrt (63 : ℝ) := by nlinarith
  have hb80 : Real.sqrt (80 : ℝ) < 1789 / 200 := by nlinarith
  norm_num [criticalMaterialGradient, criticalMaterialSample]
  linarith

/-- A genuine material-clock connection on any positive integer cell. This
uses finite coordinate derivatives, without postulating a strong derivative
of the completed Hilbert state or identifying the material and height clocks. -/
theorem carryMaterialCamera_clock_connection (cell : IntegerCameraCell)
    (hp : ∀ r, 0 < integerCameraPoint cell r) (t : ℝ) :
    let l := (integerCameraPoint cell .left).toNat
    let c := (integerCameraPoint cell .center).toNat
    let r := (integerCameraPoint cell .right).toNat
    HasDerivAt (fun s => carryMaterialCameraReadout cell (baseTwoCompletedBoundaryHilbertState s))
      (-Complex.I * (Real.log c : ℂ) *
          carryMaterialCameraReadout cell (baseTwoCompletedBoundaryHilbertState t) -
        Complex.I * (((Real.log l : ℂ) - (Real.log c : ℂ)) * criticalMaterialSample t l +
          ((Real.log r : ℂ) - (Real.log c : ℂ)) * criticalMaterialSample t r)) t := by
  dsimp only
  simp_rw [carryMaterialCameraReadout_source cell hp]
  convert ((criticalMaterialSample_hasDerivAt t _).sub
    ((criticalMaterialSample_hasDerivAt t _).const_mul 2)).add
      (criticalMaterialSample_hasDerivAt t _) using 1 <;> first | rfl | ring

/-- Two independent arguments and all three correction pairings. On the
diagonal this gives the energy ledger only after both mixed terms are kept. -/
theorem carryMaterialCamera72_pairing_transport (t u : ℝ) :
    let a := carryMaterialCameraReadout integerCamera72Two (baseTwoCompletedBoundaryHilbertState t)
    let b := carryMaterialCameraReadout integerCamera72Two (baseTwoCompletedBoundaryHilbertState u)
    let dt := criticalMaterialGradient t 79 - criticalMaterialGradient t 62
    let du := criticalMaterialGradient u 79 - criticalMaterialGradient u 62
    conj (carryMaterialCameraReadout integerCamera72Three (baseTwoCompletedBoundaryHilbertState t)) *
        carryMaterialCameraReadout integerCamera72Three (baseTwoCompletedBoundaryHilbertState u) =
      conj a * b + conj a * du + conj dt * b + conj dt * du := by
  dsimp only
  rw [carryMaterialCamera72_source_transport, carryMaterialCamera72_source_transport]
  simp only [map_add]
  ring

/-- A pairing of the prescribed source samples, never a chosen target Gram. -/
def carryMaterialSamplePair (t u : ℝ) (n m : ℕ) : ℂ :=
  conj (criticalMaterialSample t n) * criticalMaterialSample u m

theorem carryMaterialSamplePair_real_forms (t u : ℝ) (n m : ℕ) :
    (carryMaterialSamplePair t u n m).re =
        integerObservationPair (carryMaterialRealSample t n) (carryMaterialRealSample u m) ∧
      (carryMaterialSamplePair t u n m).im =
        integerObservationPair (-(carryMaterialRealSample t n).2,
          (carryMaterialRealSample t n).1) (carryMaterialRealSample u m) := by
  simp only [carryMaterialSamplePair, carryMaterialRealSample, integerObservationPair,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  constructor <;> ring

/-- Both independent phases, both quadratures, and the original amplitudes. -/
theorem carryMaterialSamplePair_phase (t u : ℝ) (n m : ℕ) :
    (carryMaterialSamplePair t u n m).re =
        (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ *
          Real.cos (t * Real.log n - u * Real.log m) ∧
      (carryMaterialSamplePair t u n m).im =
        (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ *
          Real.sin (t * Real.log n - u * Real.log m) := by
  rw [(carryMaterialSamplePair_real_forms t u n m).1,
    (carryMaterialSamplePair_real_forms t u n m).2,
    carryMaterialRealSample_coordinates, carryMaterialRealSample_coordinates]
  simp only [integerObservationPair, Real.cos_sub, Real.sin_sub,
    neg_mul, Real.cos_neg, Real.sin_neg]
  constructor <;> ring

def carryMaterialCamera72NineTerms (t u : ℝ) : ℂ :=
  carryMaterialSamplePair t u 64 63 - 2 * carryMaterialSamplePair t u 64 72 +
    carryMaterialSamplePair t u 64 81 - 2 * carryMaterialSamplePair t u 72 63 +
    4 * carryMaterialSamplePair t u 72 72 - 2 * carryMaterialSamplePair t u 72 81 +
    carryMaterialSamplePair t u 80 63 - 2 * carryMaterialSamplePair t u 80 72 +
    carryMaterialSamplePair t u 80 81

/-- All nine ordered center/leg crossings, before taking either real form. -/
theorem carryMaterialCamera72_pairing (t u : ℝ) :
    conj (carryMaterialCameraReadout integerCamera72Two (baseTwoCompletedBoundaryHilbertState t)) *
      carryMaterialCameraReadout integerCamera72Three (baseTwoCompletedBoundaryHilbertState u) =
        carryMaterialCamera72NineTerms t u := by
  rw [(carryMaterialCamera72_source_values t).1, (carryMaterialCamera72_source_values u).2]
  simp only [carryMaterialCamera72NineTerms, carryMaterialSamplePair, map_add, map_sub,
    map_mul, map_ofNat]
  ring

theorem carryMaterialCamera72_real_pairing (t u : ℝ) :
    integerObservationPair (carryMaterialRealCamera integerCamera72Two t)
        (carryMaterialRealCamera integerCamera72Three u) = (carryMaterialCamera72NineTerms t u).re ∧
      integerObservationPair (-(carryMaterialRealCamera integerCamera72Two t).2,
          (carryMaterialRealCamera integerCamera72Two t).1)
        (carryMaterialRealCamera integerCamera72Three u) = (carryMaterialCamera72NineTerms t u).im := by
  have h := carryMaterialCamera72_pairing t u
  constructor
  · simpa only [carryMaterialRealCamera, integerObservationPair, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add] using congrArg Complex.re h
  · have hh := congrArg Complex.im h
    simpa only [carryMaterialRealCamera, integerObservationPair, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, neg_mul, add_comm] using hh

/-- An actual completed source specialization of the existing dressing/readout
law; the return remains in the carrier. This is not a moment Gram theorem. -/
theorem carryMaterial_dressed_completed_readout (t : ℝ) :
    baseTwoCompletedBoundaryHilbertReadout
      (baseTwoVectorDressing t (baseTwoCompletedBoundaryHilbertState t)) =
        baseTwoCanonicalResponse t := by
  rw [baseTwoVectorDressing_apply, map_smul, smul_eq_mul,
    baseTwoCompletedBoundaryHilbertReadout_eq_signal,
    baseTwoCanonicalResponse_eq_dressing_mul_signal]

theorem carryMaterial_dressed_completed_pairing (t u : ℝ) :
    inner ℂ (baseTwoVectorDressing t (baseTwoCompletedBoundaryHilbertState t))
      (baseTwoVectorDressing u (baseTwoCompletedBoundaryHilbertState u)) =
      conj (baseTwoCanonicalDressingScalar t) * baseTwoCanonicalDressingScalar u *
        inner ℂ (baseTwoCompletedBoundaryHilbertState t) (baseTwoCompletedBoundaryHilbertState u) := by
  simp only [baseTwoVectorDressing_apply, inner_smul_left, inner_smul_right]
  ring

end
end GeometryOfNumbers.Analysis
