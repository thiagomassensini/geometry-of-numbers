import GeometryOfNumbers.Analysis.CarryMaterialCameraTransport

/-! Transport of the SAME material source through actual integer cells.
Intervals use material points p and the existing edge index p-1. No radius
is used as a vertical TFVD coordinate. Equal radii are allowed. -/
namespace GeometryOfNumbers.Analysis
open Geometry BaseTwoCompletion
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false

def carryMaterialIntervalReadout (a b : ℕ) :
    BaseTwoCompletedBoundaryHilbertCarrier →L[ℂ] ℂ :=
  ∑ p ∈ Finset.Ico a b, carryMaterialGradientReadout (p - 1)

theorem carryMaterialIntervalReadout_apply (a b : ℕ)
    (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialIntervalReadout a b y = ∑ p ∈ Finset.Ico a b, y.snd.fst (p - 1) := by
  simp [carryMaterialIntervalReadout, carryMaterialGradientReadout_apply]

theorem carryMaterialIntervalReadout_telescope (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialIntervalReadout a b y = carryMaterialPointReadout b y - carryMaterialPointReadout a y := by
  rw [carryMaterialIntervalReadout_apply]
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    have h := carryMaterialPointReadout_step (b - 1) y
    have h1 : b - 1 + 1 = b := by omega
    have h2 : b - 1 + 2 = b + 1 := by omega
    rw [h1, h2] at h
    linear_combination -h

def carryMaterialRadiusCorrection (c h H : ℕ) :
    BaseTwoCompletedBoundaryHilbertCarrier →L[ℂ] ℂ :=
  carryMaterialIntervalReadout (c + h) (c + H) -
    carryMaterialIntervalReadout (c - H) (c - h)

theorem carryMaterialRadiusCorrection_source (c h H : ℕ) (t : ℝ) :
    carryMaterialRadiusCorrection c h H (baseTwoCompletedBoundaryHilbertState t) =
      (∑ p ∈ Finset.Ico (c + h) (c + H), criticalMaterialGradient t (p - 1)) -
        ∑ p ∈ Finset.Ico (c - H) (c - h), criticalMaterialGradient t (p - 1) := by
  simp [carryMaterialRadiusCorrection, carryMaterialIntervalReadout_apply,
    baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply]

theorem carryMaterialCamera_radius_readout (cell : IntegerCameraCell) (c : ℕ)
    (hc : integerCameraCenter cell = (c : ℤ)) (hr : integerCameraRadius cell ≤ c)
    (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialCameraReadout cell y =
      carryMaterialPointReadout (c - integerCameraRadius cell) y -
        2 * carryMaterialPointReadout c y +
        carryMaterialPointReadout (c + integerCameraRadius cell) y := by
  rw [carryMaterialCameraReadout_apply]
  have hl : (integerCameraPoint cell .left).toNat = c - integerCameraRadius cell := by
    simp only [integerCameraPoint, leftLeg, hc]
    omega
  have hm : (integerCameraPoint cell .center).toNat = c := by
    simp only [integerCameraPoint, hc, Int.toNat_natCast]
  have hh : (integerCameraPoint cell .right).toNat = c + integerCameraRadius cell := by
    simp only [integerCameraPoint, rightLeg, hc]
    omega
  rw [hl, hm, hh]

/-- General law for two actual cells at the same integer center. No isometry
or correspondence between their legs is postulated. -/
theorem carryMaterialCamera_general_transport (a b : IntegerCameraCell) (c : ℕ)
    (ha : integerCameraCenter a = (c : ℤ)) (hb : integerCameraCenter b = (c : ℤ))
    (hr : integerCameraRadius a ≤ integerCameraRadius b)
    (hH : integerCameraRadius b < c) (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialCameraReadout b y = carryMaterialCameraReadout a y +
      carryMaterialRadiusCorrection c (integerCameraRadius a) (integerCameraRadius b) y := by
  rw [carryMaterialCamera_radius_readout a c ha (by omega),
    carryMaterialCamera_radius_readout b c hb (by omega)]
  simp only [carryMaterialRadiusCorrection, sub_apply]
  rw [carryMaterialIntervalReadout_telescope _ _ (by omega) (by omega),
    carryMaterialIntervalReadout_telescope _ _ (by omega) (by omega)]
  ring

/-- The camera presentations come from the original residual towers. -/
theorem carryMaterialTower_general_transport (b d n k l : ℕ) (hb : 0 < b) (hd : 0 < d)
    (hk : HasCarryDepthAtLeast b n k) (hl : HasCarryDepthAtLeast d n l)
    (hr : b ^ k ≤ d ^ l) (hH : d ^ l < n) (t : ℝ) :
    carryMaterialCameraReadout (integerCameraTowerCell d n l) (baseTwoCompletedBoundaryHilbertState t) =
      carryMaterialCameraReadout (integerCameraTowerCell b n k) (baseTwoCompletedBoundaryHilbertState t) +
        carryMaterialRadiusCorrection n (b ^ k) (d ^ l) (baseTwoCompletedBoundaryHilbertState t) :=
  carryMaterialCamera_general_transport _ _ n
    (integerCameraTowerCell_center b n k hb hk) (integerCameraTowerCell_center d n l hd hl) hr hH _

theorem carryMaterialRadiusCorrection_equal (c h : ℕ) : carryMaterialRadiusCorrection c h h = 0 := by
  simp [carryMaterialRadiusCorrection, carryMaterialIntervalReadout]

theorem carryMaterialCamera_general_reverse (a b : IntegerCameraCell) (c : ℕ)
    (ha : integerCameraCenter a = (c : ℤ)) (hb : integerCameraCenter b = (c : ℤ))
    (hr : integerCameraRadius a ≤ integerCameraRadius b)
    (hH : integerCameraRadius b < c) (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialCameraReadout a y = carryMaterialCameraReadout b y -
      carryMaterialRadiusCorrection c (integerCameraRadius a) (integerCameraRadius b) y := by
  rw [carryMaterialCamera_general_transport a b c ha hb hr hH]
  abel

theorem carryMaterialRadiusCorrection72 (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialRadiusCorrection 72 8 9 y = y.snd.fst 79 - y.snd.fst 62 := by
  norm_num [carryMaterialRadiusCorrection, carryMaterialIntervalReadout_apply,
    Finset.sum_Ico_succ_top]

/-- Exact regression of the general law, with the original ordered indices. -/
theorem carryMaterialCamera_general_transport72 (t : ℝ) :
    carryMaterialCameraReadout integerCamera72Three (baseTwoCompletedBoundaryHilbertState t) =
      carryMaterialCameraReadout integerCamera72Two (baseTwoCompletedBoundaryHilbertState t) +
        (criticalMaterialGradient t 79 - criticalMaterialGradient t 62) := by
  have h := carryMaterialCamera_general_transport integerCamera72Two integerCamera72Three 72
    (by decide) (by decide) (by decide) (by decide) (baseTwoCompletedBoundaryHilbertState t)
  simpa only [show integerCameraRadius integerCamera72Two = 8 from rfl,
    show integerCameraRadius integerCamera72Three = 9 from rfl, carryMaterialRadiusCorrection72,
    baseTwoCompletedBoundaryHilbertState_interior,
    baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply] using h

theorem carryMaterialCamera_general_pairing_transport (a b : IntegerCameraCell) (c : ℕ)
    (ha : integerCameraCenter a = (c : ℤ)) (hb : integerCameraCenter b = (c : ℤ))
    (hr : integerCameraRadius a ≤ integerCameraRadius b) (hH : integerCameraRadius b < c)
    (t u : ℝ) :
    let Y := baseTwoCompletedBoundaryHilbertState
    let D := carryMaterialRadiusCorrection c (integerCameraRadius a) (integerCameraRadius b)
    conj (carryMaterialCameraReadout b (Y t)) * carryMaterialCameraReadout b (Y u) =
      conj (carryMaterialCameraReadout a (Y t)) * carryMaterialCameraReadout a (Y u) +
      conj (carryMaterialCameraReadout a (Y t)) * D (Y u) +
      conj (D (Y t)) * carryMaterialCameraReadout a (Y u) + conj (D (Y t)) * D (Y u) := by
  dsimp only
  rw [carryMaterialCamera_general_transport a b c ha hb hr hH,
    carryMaterialCamera_general_transport a b c ha hb hr hH]
  simp only [map_add]
  ring

theorem carryMaterialCamera_general_energy_defect (a b : IntegerCameraCell) (c : ℕ)
    (ha : integerCameraCenter a = (c : ℤ)) (hb : integerCameraCenter b = (c : ℤ))
    (hr : integerCameraRadius a ≤ integerCameraRadius b) (hH : integerCameraRadius b < c)
    (t : ℝ) :
    let d := carryMaterialRadiusCorrection c (integerCameraRadius a) (integerCameraRadius b)
      (baseTwoCompletedBoundaryHilbertState t)
    realPlaneEnergy (carryMaterialRealCamera b t) - realPlaneEnergy (carryMaterialRealCamera a t) =
      2 * integerObservationPair (carryMaterialRealCamera a t) (d.re, d.im) +
        realPlaneEnergy (d.re, d.im) := by
  dsimp only
  have h := carryMaterialCamera_general_transport a b c ha hb hr hH (baseTwoCompletedBoundaryHilbertState t)
  simp only [carryMaterialRealCamera, realPlaneEnergy, integerObservationPair]
  rw [h]
  simp only [Complex.add_re, Complex.add_im]
  ring

def carryMaterialCameraNineTerms (a b : IntegerCameraCell) (t u : ℝ) : ℂ :=
  let K := fun r s => carryMaterialSamplePair t u (integerCameraPoint a r).toNat (integerCameraPoint b s).toNat
  K .left .left - 2 * K .left .center + K .left .right -
    2 * K .center .left + 4 * K .center .center - 2 * K .center .right +
    K .right .left - 2 * K .right .center + K .right .right

theorem carryMaterialCamera_nine_pairing (a b : IntegerCameraCell)
    (ha : ∀ r, 0 < integerCameraPoint a r) (hb : ∀ r, 0 < integerCameraPoint b r) (t u : ℝ) :
    conj (carryMaterialCameraReadout a (baseTwoCompletedBoundaryHilbertState t)) *
      carryMaterialCameraReadout b (baseTwoCompletedBoundaryHilbertState u) =
        carryMaterialCameraNineTerms a b t u := by
  rw [carryMaterialCameraReadout_source a ha, carryMaterialCameraReadout_source b hb]
  simp only [carryMaterialCameraNineTerms, carryMaterialSamplePair, map_add, map_sub, map_mul, map_ofNat]
  ring

theorem carryMaterialCamera_nine_real_pairing (a b : IntegerCameraCell)
    (ha : ∀ r, 0 < integerCameraPoint a r) (hb : ∀ r, 0 < integerCameraPoint b r) (t u : ℝ) :
    integerObservationPair (carryMaterialRealCamera a t) (carryMaterialRealCamera b u) =
        (carryMaterialCameraNineTerms a b t u).re ∧
      integerObservationPair (-(carryMaterialRealCamera a t).2, (carryMaterialRealCamera a t).1)
        (carryMaterialRealCamera b u) = (carryMaterialCameraNineTerms a b t u).im := by
  have h := carryMaterialCamera_nine_pairing a b ha hb t u
  constructor
  · simpa only [carryMaterialRealCamera, integerObservationPair, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add] using congrArg Complex.re h
  · simpa only [carryMaterialRealCamera, integerObservationPair, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, neg_mul, add_comm] using congrArg Complex.im h

theorem carryMaterialCameraNineTerms72 (t u : ℝ) :
    carryMaterialCameraNineTerms integerCamera72Two integerCamera72Three t u =
      carryMaterialCamera72NineTerms t u := rfl

end
end GeometryOfNumbers.Analysis
