import GeometryOfNumbers.Analysis.MultiplicativeOffsetTransport
import GeometryOfNumbers.Analysis.QuadraticCenteredBracket

/-!
# A real observable on the already constructed integer legs

Orientation is center - point: the spatial LEFT leg has positive offset.
The profile realizes a supplied compatible transport. It is not a power of
the absolute point, nor a transport selected by vertical depth.
-/

namespace GeometryOfNumbers.Analysis

open Foundation Geometry

noncomputable section

def centeredMultiplicativeProfile (centerValue : ℝ) (Q : Int → ℝ)
    (center point : Int) : ℝ := centerValue * Q (center - point)

theorem centeredMultiplicativeProfile_center (C : ℝ) {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) :
    centeredMultiplicativeProfile C Q c c = C := by
  simp [centeredMultiplicativeProfile, multiplicativeOffsetTransport_zero hQ]

theorem centeredMultiplicativeProfile_leftLeg (C : ℝ) (Q : Int → ℝ) (c : Int) (r : Nat) :
    centeredMultiplicativeProfile C Q c (leftLeg c (r : Int)) = C * Q (r : Int) := by
  have hoffset : c - leftLeg c (r : Int) = (r : Int) := by unfold leftLeg; omega
  simp only [centeredMultiplicativeProfile, hoffset]

theorem centeredMultiplicativeProfile_rightLeg (C : ℝ) (Q : Int → ℝ) (c : Int) (r : Nat) :
    centeredMultiplicativeProfile C Q c (rightLeg c (r : Int)) = C * Q (-(r : Int)) := by
  have hoffset : c - rightLeg c (r : Int) = -(r : Int) := by unfold rightLeg; omega
  simp only [centeredMultiplicativeProfile, hoffset]

theorem profile_leftLeg_eq_quadraticLeftLeg (C : ℝ) (Q : Int → ℝ) (c : Int) (r : Nat) :
    centeredMultiplicativeProfile C Q c (leftLeg c (r : Int)) =
      quadraticLeftLeg C (Q (r : Int)) := centeredMultiplicativeProfile_leftLeg C Q c r

theorem profile_rightLeg_eq_quadraticRightLeg (C : ℝ) {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) (r : Nat) :
    centeredMultiplicativeProfile C Q c (rightLeg c (r : Int)) =
      quadraticRightLeg C (Q (r : Int)) := by
  rw [centeredMultiplicativeProfile_rightLeg, multiplicativeOffsetTransport_neg hQ]
  rfl

theorem centeredMultiplicativeProfile_leftLeg_eq_pow (C : ℝ) {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) (r : Nat) :
    centeredMultiplicativeProfile C Q c (leftLeg c (r : Int)) = C * (Q 1) ^ r := by
  rw [centeredMultiplicativeProfile_leftLeg, multiplicativeOffsetTransport_natCast hQ]

theorem centeredMultiplicativeProfile_rightLeg_eq_inv_pow (C : ℝ) {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) (r : Nat) :
    centeredMultiplicativeProfile C Q c (rightLeg c (r : Int)) = C * ((Q 1) ^ r)⁻¹ := by
  rw [centeredMultiplicativeProfile_rightLeg, multiplicativeOffsetTransport_neg_natCast hQ]

theorem centeredMultiplicativeProfile_reflected_product (C : ℝ) {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) (r : Nat) :
    centeredMultiplicativeProfile C Q c (leftLeg c (r : Int)) *
      centeredMultiplicativeProfile C Q c (rightLeg c (r : Int)) = C ^ 2 := by
  rw [profile_leftLeg_eq_quadraticLeftLeg, profile_rightLeg_eq_quadraticRightLeg C hQ]
  exact quadraticReflectedLegs_product C _ (multiplicativeOffsetTransport_ne_zero hQ _)

def realCenteredSecondDifference (F : Int → ℝ) (center : Int) (radius : Nat) : ℝ :=
  realCenteredReadout (F (leftLeg center (radius : Int))) (F center)
    (F (rightLeg center (radius : Int)))

theorem profile_realCenteredSecondDifference_eq_local (C : ℝ) {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) (r : Nat) :
    realCenteredSecondDifference (centeredMultiplicativeProfile C Q c) c r =
      quadraticCenteredBracket C (Q (r : Int)) := by
  unfold realCenteredSecondDifference
  rw [profile_leftLeg_eq_quadraticLeftLeg, centeredMultiplicativeProfile_center C hQ,
    profile_rightLeg_eq_quadraticRightLeg C hQ]
  rfl

theorem profile_realCenteredSecondDifference_eq_pow (C : ℝ) {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) (r : Nat) :
    realCenteredSecondDifference (centeredMultiplicativeProfile C Q c) c r =
      quadraticCenteredBracket C ((Q 1) ^ r) := by
  rw [profile_realCenteredSecondDifference_eq_local C hQ,
    multiplicativeOffsetTransport_natCast hQ]

theorem profile_realCenteredSecondDifference_eq_closed (C : ℝ) {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) (r : Nat) :
    realCenteredSecondDifference (centeredMultiplicativeProfile C Q c) c r =
      C * ((Q 1) ^ r + ((Q 1) ^ r)⁻¹ - 2) := by
  rw [profile_realCenteredSecondDifference_eq_pow C hQ, quadraticCenteredBracket_eq_closed]

theorem profile_realCenteredSecondDifference_eq_factor (C : ℝ) {Q : Int → ℝ}
    (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) (r : Nat) :
    realCenteredSecondDifference (centeredMultiplicativeProfile C Q c) c r =
      C * (((Q 1) ^ r - 1) ^ 2) * ((Q 1) ^ r)⁻¹ := by
  rw [profile_realCenteredSecondDifference_eq_pow C hQ]
  exact quadraticCenteredBracket_eq_factor C _ (ne_of_gt (pow_pos hQ.2.2 r))

def criticalCenteredMultiplicativeProfile (b k : Nat) (hb : 0 < b)
    (Q : Int → ℝ) (center : Int) : Int → ℝ :=
  centeredMultiplicativeProfile (realCriticalAmplitude b k hb) Q center

theorem criticalCenteredMultiplicativeProfile_product (b k : Nat) (hb : 0 < b)
    {Q : Int → ℝ} (hQ : IsPositiveMultiplicativeOffsetTransport Q) (c : Int) (r : Nat) :
    criticalCenteredMultiplicativeProfile b k hb Q c (leftLeg c (r : Int)) *
      criticalCenteredMultiplicativeProfile b k hb Q c (rightLeg c (r : Int)) =
        realDepthMass b k hb := by
  unfold criticalCenteredMultiplicativeProfile
  rw [profile_leftLeg_eq_quadraticLeftLeg,
    profile_rightLeg_eq_quadraticRightLeg _ hQ]
  exact criticalQuadraticLegs_product b k hb _ (multiplicativeOffsetTransport_ne_zero hQ _)

end

end GeometryOfNumbers.Analysis
