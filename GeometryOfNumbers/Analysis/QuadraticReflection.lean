import GeometryOfNumbers.Analysis.RealCriticalDepthState

/-!
# Reciprocal legs of an already selected quadratic center

The center is an input, not reconstructed from its mass. Specialization uses
the existing positive critical amplitude and its square theorem. Reciprocal
reflection swaps the legs and preserves their product. The parameter is not
an angle or a selected physical parameter. Real inversion is total in Lean;
the reflected product law deliberately excludes zero.
-/

namespace GeometryOfNumbers.Analysis

open Foundation Geometry

noncomputable section

def reciprocalReflection (q : ℝ) : ℝ := q⁻¹

theorem reciprocalReflection_involutive (q : ℝ) :
    reciprocalReflection (reciprocalReflection q) = q := inv_inv q

theorem reciprocalReflection_pos {q : ℝ} (hq : 0 < q) :
    0 < reciprocalReflection q := inv_pos.mpr hq

def quadraticLeftLeg (center q : ℝ) : ℝ := center * q

def quadraticRightLeg (center q : ℝ) : ℝ := center * reciprocalReflection q

theorem quadraticLeftLeg_reflection (center q : ℝ) :
    quadraticLeftLeg center (reciprocalReflection q) = quadraticRightLeg center q := rfl

theorem quadraticRightLeg_reflection (center q : ℝ) :
    quadraticRightLeg center (reciprocalReflection q) = quadraticLeftLeg center q := by
  unfold quadraticRightLeg
  rw [reciprocalReflection_involutive]
  rfl

theorem quadraticReflectedLegs_at_one (center : ℝ) :
    quadraticLeftLeg center 1 = center ∧ quadraticRightLeg center 1 = center := by
  simp [quadraticLeftLeg, quadraticRightLeg, reciprocalReflection]

theorem quadraticReflectedLegs_product (center q : ℝ) (hq : q ≠ 0) :
    quadraticLeftLeg center q * quadraticRightLeg center q = center ^ 2 := by
  unfold quadraticLeftLeg quadraticRightLeg reciprocalReflection
  calc
    (center * q) * (center * q⁻¹) = center ^ 2 * (q * q⁻¹) := by ring
    _ = center ^ 2 := by rw [mul_inv_cancel₀ hq, mul_one]

/-- A functional reflection identity for the left-leg function itself. -/
theorem quadraticReflection_product (center q : ℝ) (hq : q ≠ 0) :
    quadraticLeftLeg center q * quadraticLeftLeg center (reciprocalReflection q) =
      center ^ 2 := by
  rw [quadraticLeftLeg_reflection]
  exact quadraticReflectedLegs_product center q hq

def criticalQuadraticLeftLeg (b k : ℕ) (hb : 0 < b) (q : ℝ) : ℝ :=
  quadraticLeftLeg (realCriticalAmplitude b k hb) q

def criticalQuadraticRightLeg (b k : ℕ) (hb : 0 < b) (q : ℝ) : ℝ :=
  quadraticRightLeg (realCriticalAmplitude b k hb) q

theorem criticalQuadraticLegs_product (b k : ℕ) (hb : 0 < b) (q : ℝ) (hq : q ≠ 0) :
    criticalQuadraticLeftLeg b k hb q * criticalQuadraticRightLeg b k hb q =
      realDepthMass b k hb := by
  rw [criticalQuadraticLeftLeg, criticalQuadraticRightLeg,
    quadraticReflectedLegs_product _ _ hq]
  exact realCriticalAmplitude_sq_eq_realDepthMass b k hb

theorem criticalQuadraticReflection_product
    (b k : ℕ) (hb : 0 < b) (q : ℝ) (hq : q ≠ 0) :
    criticalQuadraticLeftLeg b k hb q *
      criticalQuadraticLeftLeg b k hb (reciprocalReflection q) = realDepthMass b k hb := by
  rw [criticalQuadraticLeftLeg, criticalQuadraticLeftLeg,
    quadraticReflection_product _ _ hq]
  exact realCriticalAmplitude_sq_eq_realDepthMass b k hb

/-- The preserved mass is literally the realization of the earlier formal share. -/
theorem criticalQuadraticLegs_product_realizes_formalMass
    (b k : ℕ) (hb : 0 < b) (q : ℝ) (hq : q ≠ 0) :
    criticalQuadraticLeftLeg b k hb q * criticalQuadraticRightLeg b k hb q =
      realizeCountingShare (canonicalResidualDepthMass b k hb) :=
  criticalQuadraticLegs_product b k hb q hq

/-- Support of the index is provenance, not a premise of the product algebra. -/
theorem balancedCarryDepth_quadraticLegs_product
    (b n k : ℕ) (hodd : IsOddCapacity b)
    (_hdepth : HasIntegerCarryDepthAtLeast b (balancedCarryCenter b n hodd) k)
    (q : ℝ) (hq : q ≠ 0) :
    criticalQuadraticLeftLeg b k (oddCapacity_pos hodd) q *
      criticalQuadraticRightLeg b k (oddCapacity_pos hodd) q =
        realizeCountingShare (canonicalResidualDepthMass b k (oddCapacity_pos hodd)) :=
  criticalQuadraticLegs_product_realizes_formalMass b k (oddCapacity_pos hodd) q hq

end

end GeometryOfNumbers.Analysis
