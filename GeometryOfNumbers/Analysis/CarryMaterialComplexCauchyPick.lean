import GeometryOfNumbers.Analysis.CarryMaterialComplexCompletedPair
import Mathlib.Tactic

/-!
# Source-first C2 complex Cauchy--Pick quotient

The two Hilbert arms are ACTUAL complex-time C2 material states and their
full vector derivatives, with the readout-hidden complement in opposite
chirality. The signed Gram difference is a physical Wronskian. Only THEN
do we divide by the native-style Cauchy separation and two full scalar
physical boundary values; no target Gram, Pick sign, or xi identity is
inserted into the source.
-/

namespace GeometryOfNumbers.Analysis

open BaseTwoCompletion
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false

def carryMaterialComplexChiralPositive (z : ℂ) : CarryMaterialCompleteChiralArm :=
  carryMaterialCompleteChiralPositive (carryMaterialComplexCompanionValuePair z)

def carryMaterialComplexChiralNegative (z : ℂ) : CarryMaterialCompleteChiralArm :=
  carryMaterialCompleteChiralNegative (carryMaterialComplexCompanionValuePair z)

/-- Direct signed physical source Gram; no normalization yet. -/
def carryMaterialComplexChiralGreen (z w : ℂ) : ℂ :=
  (Complex.I/2) *
    (inner ℂ (carryMaterialComplexChiralPositive z)
        (carryMaterialComplexChiralPositive w) -
      inner ℂ (carryMaterialComplexChiralNegative z)
        (carryMaterialComplexChiralNegative w))

/-- Source-derived scalar response, without identifying it to native xi. -/
def carryMaterialComplexResponse (z : ℂ) : ℂ :=
  carryMaterialComplexCompanionReadout z /
    (2 * carryMaterialComplexValueReadout z)

/-- The complex source Green balance is its exact scalar boundary Wronskian,
including BOTH incoming and hidden return channels. -/
theorem carryMaterialComplexChiralGreen_eq_boundary (z w : ℂ) :
    carryMaterialComplexChiralGreen z w =
      conj (carryMaterialComplexValueReadout z) *
          carryMaterialComplexCompanionReadout w -
        conj (carryMaterialComplexCompanionReadout z) *
          carryMaterialComplexValueReadout w := by
  unfold carryMaterialComplexChiralGreen
  simp only [carryMaterialComplexChiralPositive,
    carryMaterialComplexChiralNegative]
  rw [carryMaterialCompleteChiralDifference_eq_green]
  have h := carryMaterialPairGreen_readout_ledger
    (carryMaterialComplexCompanionValuePair z)
    (carryMaterialComplexCompanionValuePair w)
  unfold carryMaterialPairGreen at h
  have hgreen :
      carryMaterialPairGreen (carryMaterialComplexCompanionValuePair z)
        (carryMaterialComplexCompanionValuePair w) -
      carryMaterialPairGreen
        (carryMaterialPairComplement (carryMaterialComplexCompanionValuePair z))
        (carryMaterialPairComplement (carryMaterialComplexCompanionValuePair w)) =
        (1/2 : ℂ) *
          (conj (carryMaterialPairReadout (carryMaterialComplexCompanionValuePair z)).2 *
            (carryMaterialPairReadout (carryMaterialComplexCompanionValuePair w)).1 -
           conj (carryMaterialPairReadout (carryMaterialComplexCompanionValuePair z)).1 *
             (carryMaterialPairReadout (carryMaterialComplexCompanionValuePair w)).2) := by
    unfold carryMaterialPairGreen
    rw [h]
    simp only [RCLike.inner_apply]
    ring
  have hread (v : ℂ) :
      carryMaterialPairReadout (carryMaterialComplexCompanionValuePair v) =
        (carryMaterialComplexCompanionReadout v,
          2 * carryMaterialComplexValueReadout v) := by
    apply Prod.ext
    · rfl
    · simp [carryMaterialPairReadout, carryMaterialComplexCompanionValuePair,
        carryMaterialComplexValueReadout, map_smul, smul_eq_mul]
  rw [hgreen, hread z, hread w]
  simp only [map_mul, map_ofNat]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]


/-- The actual source's complex Cauchy--Pick quotient.
On the upper-half-plane radial grid its denominator is nonzero off zeros
of the completed physical value. -/
def carryMaterialComplexPickKernel (z w : ℂ) : ℂ :=
  carryMaterialComplexChiralGreen z w /
    (2 * conj (carryMaterialComplexValueReadout z) *
      carryMaterialComplexValueReadout w * (w-conj z))

/-- Pure scalar normalization of the GENUINE C2 source pair; no positivity. -/
theorem carryMaterialComplexPickKernel_eq_polarizedResponse (z w : ℂ)
    (hz : carryMaterialComplexValueReadout z ≠ 0)
    (hw : carryMaterialComplexValueReadout w ≠ 0)
    (hsep : w ≠ conj z) :
    carryMaterialComplexPickKernel z w =
      (carryMaterialComplexResponse w -
        conj (carryMaterialComplexResponse z)) / (w-conj z) := by
  rw [carryMaterialComplexPickKernel,
    carryMaterialComplexChiralGreen_eq_boundary]
  unfold carryMaterialComplexResponse
  have hzstar : conj (carryMaterialComplexValueReadout z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hz
  have hsepd : w-conj z ≠ 0 := sub_ne_zero.mpr hsep
  field_simp [hzstar, hw, hsepd]
  simp only [map_div₀, map_mul, map_ofNat]
  field_simp [hzstar, hw]

/-- Positive imaginary heights remove the putative Cauchy diagonal
singularity: the conjugate of an upper-half-plane point lies below it. -/
theorem carryMaterialComplexPick_separated_of_positive_im
    (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) : w ≠ conj z := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.conj_im] at him
  linarith

theorem carryMaterialComplexPick_diagonal_of_positive_im (z : ℂ)
    (hzIm : 0 < z.im)
    (hzF : carryMaterialComplexValueReadout z ≠ 0) :
    carryMaterialComplexPickKernel z z =
      (carryMaterialComplexResponse z -
        conj (carryMaterialComplexResponse z)) / (z-conj z) := by
  exact carryMaterialComplexPickKernel_eq_polarizedResponse z z hzF hzF
    (carryMaterialComplexPick_separated_of_positive_im z z hzIm hzIm)

theorem carryMaterialComplexChiralPositive_ofReal (t : ℝ) :
    carryMaterialComplexChiralPositive (t : ℂ) =
      carryMaterialCompleteChiralPositive (carryMaterialCompanionValuePair t) := by
  rw [carryMaterialComplexChiralPositive,
    carryMaterialComplexCompanionValuePair_ofReal]

theorem carryMaterialComplexChiralNegative_ofReal (t : ℝ) :
    carryMaterialComplexChiralNegative (t : ℂ) =
      carryMaterialCompleteChiralNegative (carryMaterialCompanionValuePair t) := by
  rw [carryMaterialComplexChiralNegative,
    carryMaterialComplexCompanionValuePair_ofReal]

theorem carryMaterialComplexChiralGreen_ofReal (t u : ℝ) :
    carryMaterialComplexChiralGreen (t : ℂ) (u : ℂ) =
      carryMaterialCompleteChiralGreenPairing t u := by
  simp [carryMaterialComplexChiralGreen,
    carryMaterialCompleteChiralGreenPairing,
    carryMaterialComplexChiralPositive_ofReal,
    carryMaterialComplexChiralNegative_ofReal]

/-! ## Finite complex samples: retain every cross and both physical arms. -/

/-- Every finite matrix of physical complex Green responses is exactly a
rotated difference of the two concrete Hilbert Grams. No Pick sign is
inserted, and no head/tail term is dropped. -/
theorem carryMaterialComplexChiralGreenMatrix_eq_signedGram
    (N : ℕ) (z : Fin N → ℂ) :
    Matrix.of (fun i j : Fin N =>
      carryMaterialComplexChiralGreen (z i) (z j)) =
      (Complex.I / 2) •
        (Matrix.gram ℂ (fun i : Fin N => carryMaterialComplexChiralPositive (z i)) -
         Matrix.gram ℂ (fun i : Fin N => carryMaterialComplexChiralNegative (z i))) := by
  ext i j
  rfl

/-- On the upper-half-plane with the ORIGINAL source characteristic nonzero,
the complete complex Cauchy-Pick matrix is the polarized divided response
for all ordered crossings, INCLUDING the diagonal. This is a signed
construction, not a claim of positive semidefiniteness. -/
theorem carryMaterialComplexPickMatrix_eq_response (N : ℕ)
    (height : Fin N → ℂ)
    (hUpper : ∀ i : Fin N, 0 < (height i).im)
    (hF : ∀ i : Fin N, carryMaterialComplexValueReadout (height i) ≠ 0) :
    Matrix.of (fun i j : Fin N =>
      carryMaterialComplexPickKernel (height i) (height j)) =
    Matrix.of (fun i j : Fin N =>
      (carryMaterialComplexResponse (height j) -
        conj (carryMaterialComplexResponse (height i))) /
          (height j - conj (height i))) := by
  ext i j
  exact carryMaterialComplexPickKernel_eq_polarizedResponse
    (height i) (height j) (hF i) (hF j)
      (carryMaterialComplexPick_separated_of_positive_im
        (height i) (height j) (hUpper i) (hUpper j))

/-- The normalized physical response is precisely the earlier real axis
normalized material response; its equality to the native xi response is
checked separately by the cross-repository material response comparison. -/
theorem carryMaterialComplexResponse_ofReal (t : ℝ) :
    carryMaterialComplexResponse (t : ℂ) = carryMaterialNormalizedResponse t := by
  unfold carryMaterialComplexResponse
  rw [carryMaterialComplexValueReadout_ofReal]
  have hcomp : carryMaterialComplexCompanionReadout (t : ℂ) =
      baseTwoCompletedBoundaryHilbertReadout
        (carryMaterialDressedCompanion t
          ⟨baseTwoCompletedBoundaryHilbertState t,
            baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩) := by
    unfold carryMaterialComplexCompanionReadout
    rw [carryMaterialComplexCompanion_ofReal]
  rw [hcomp]
  rw [carryMaterialNormalizedResponse, carryMaterialResponseReadout,
      carryMaterialDressedCompanion_source_readout,
      carryMaterial_dressed_completed_readout]


/-! ## Nonzero material value in the genuine centered complex germ. -/

/-- The completed C2 source is nonzero at the center because its actual
material complete signal is nonzero, and neither physical dressing factor
vanishes there. No target xi nonzero fact is imported. -/
theorem carryMaterialComplexValueReadout_zero_ne_zero :
    carryMaterialComplexValueReadout 0 ≠ 0 := by
  change carryMaterialComplexValueReadout ((0 : ℝ) : ℂ) ≠ 0
  rw [carryMaterialComplexValueReadout_ofReal,
      baseTwoCanonicalResponse_eq_dressing_mul_signal]
  exact mul_ne_zero (baseTwoCanonicalDressingScalar_ne_zero 0)
    carryMaterial_origin_signal_ne_zero

/-- The complex physical readout is genuinely differentiable at the center
by differentiability of the entire dressed material vector and boundedness
of its original readout. -/
theorem carryMaterialComplexValueReadout_differentiableAt_zero :
    DifferentiableAt ℂ carryMaterialComplexValueReadout 0 := by
  have h := carryMaterialComplexDressedState_differentiableAt_ofReal 0
  exact (baseTwoCompletedBoundaryHilbertReadout.hasFDerivAt.comp_hasDerivAt
    (0 : ℂ) h.hasDerivAt).differentiableAt

/-- A neighborhood of complex heights exists in which the denominator of
the C2 source Pick kernel never vanishes due to source nonzero values. -/
theorem carryMaterialComplexValueReadout_eventually_ne_zero :
    ∀ᶠ z : ℂ in nhds 0, carryMaterialComplexValueReadout z ≠ 0 :=
  carryMaterialComplexValueReadout_differentiableAt_zero.continuousAt.eventually_ne
    carryMaterialComplexValueReadout_zero_ne_zero



/-! ## Source-first Hermite--Biehler projective quotient and Pick gauge. -/

/-- Positive HB coordinate from the ACTUAL material completed-vector readout. -/
def carryMaterialComplexPositiveHB (z : ℂ) : ℂ :=
  carryMaterialComplexCompanionReadout z +
    Complex.I * carryMaterialComplexValueReadout z

/-- Negative HB coordinate from the same source and companion. -/
def carryMaterialComplexNegativeHB (z : ℂ) : ℂ :=
  carryMaterialComplexCompanionReadout z -
    Complex.I * carryMaterialComplexValueReadout z

def carryMaterialComplexChiralQuotient (z : ℂ) : ℂ :=
  carryMaterialComplexNegativeHB z / carryMaterialComplexPositiveHB z

def carryMaterialComplexChiralGauge (z : ℂ) : ℂ :=
  carryMaterialComplexPositiveHB z / (2 * carryMaterialComplexValueReadout z)

/-- Exact two-channel Cauchy/Pick defect, formed from the physical source
rather than introducing a new positive metric or the target native quotient.
The two nonzero HB coordinates are explicit regularity hypotheses. -/
theorem carryMaterialComplexPickKernel_eq_sourceHermiteBiehler
    (z w : ℂ)
    (hzF : carryMaterialComplexValueReadout z ≠ 0)
    (hwF : carryMaterialComplexValueReadout w ≠ 0)
    (hzP : carryMaterialComplexPositiveHB z ≠ 0)
    (hwP : carryMaterialComplexPositiveHB w ≠ 0)
    (hsep : w ≠ conj z) :
    carryMaterialComplexPickKernel z w =
      (Complex.I / (w-conj z)) *
        conj (carryMaterialComplexChiralGauge z) *
          carryMaterialComplexChiralGauge w *
            (1 - conj (carryMaterialComplexChiralQuotient z) *
              carryMaterialComplexChiralQuotient w) := by
  rw [carryMaterialComplexPickKernel,
    carryMaterialComplexChiralGreen_eq_boundary]
  unfold carryMaterialComplexChiralGauge carryMaterialComplexChiralQuotient
    carryMaterialComplexPositiveHB carryMaterialComplexNegativeHB
  have hzStar : conj (carryMaterialComplexValueReadout z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzF
  have hzPStar : conj (carryMaterialComplexCompanionReadout z +
      Complex.I * carryMaterialComplexValueReadout z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzP
  have hsep' : w-conj z ≠ 0 := sub_ne_zero.mpr hsep
  simp only [map_div₀, map_mul, map_add, map_sub, map_ofNat,
    Complex.conj_I]
  field_simp [hzF, hwF, hzP, hwP, hzStar, hzPStar, hsep']
  have hzPStar' :
      ((starRingEnd ℂ) (carryMaterialComplexCompanionReadout z) +
        -((starRingEnd ℂ) (carryMaterialComplexValueReadout z) * Complex.I)) ≠ 0 := by
    convert hzPStar using 1; simp only [map_add, map_mul, Complex.conj_I]
    ring
  have hwP' :
      carryMaterialComplexCompanionReadout w +
        carryMaterialComplexValueReadout w * Complex.I ≠ 0 := by
    simpa [carryMaterialComplexPositiveHB, mul_comm] using hwP
  have hprod :
      (((starRingEnd ℂ) (carryMaterialComplexCompanionReadout z) +
        -((starRingEnd ℂ) (carryMaterialComplexValueReadout z) * Complex.I)) *
        (carryMaterialComplexCompanionReadout w +
          carryMaterialComplexValueReadout w * Complex.I)) ≠ 0 :=
    mul_ne_zero hzPStar' hwP'
  field_simp [hprod, hwP']
  ring_nf
  simp only [Complex.I_sq]
  ring


end
end GeometryOfNumbers.Analysis

#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexChiralGreen_eq_boundary
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexPickKernel_eq_polarizedResponse
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexPick_diagonal_of_positive_im
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexChiralGreen_ofReal
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexChiralGreenMatrix_eq_signedGram
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexPickMatrix_eq_response
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexResponse_ofReal
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexValueReadout_zero_ne_zero
#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexValueReadout_eventually_ne_zero

#print axioms GeometryOfNumbers.Analysis.carryMaterialComplexPickKernel_eq_sourceHermiteBiehler
