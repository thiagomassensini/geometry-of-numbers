import AllOrderPattern

/-! Residual certificates for the original source Schur complement.  These
identities do not estimate the native source at arbitrary order.  The lower
quadratic bound is required only for the OLD prefix; no sign is required of
the new pivot, and no physical carrier is constructed from a target Gram. -/
namespace CarryVariationalSchur
open CarrySelfAdjointOperator CarryCriticalSource CarryThetaPattern
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- An arbitrary trial solve, before any inverse is evaluated. -/
def sourceTrialResidual (m : ℕ → ℝ) (s n : ℕ) (z : Fin n → ℝ) : Fin n → ℝ :=
  sourceMomentCoupling m s n - sourceMomentMatrix m s n *ᵥ z

/-- The original extended quadratic form on the trial direction (-z,1). -/
def sourceTrialEnergy (m : ℕ → ℝ) (s n : ℕ) (z : Fin n → ℝ) : ℝ :=
  sourceMomentQuadratic m s (n+1) (Fin.snoc (-z) 1)

theorem sourceTrialEnergy_expansion (m : ℕ → ℝ) (s n : ℕ) (z : Fin n → ℝ) :
    sourceTrialEnergy m s n z =
      m (2*n+s) - 2*(sourceMomentCoupling m s n ⬝ᵥ z) +
        sourceMomentQuadratic m s n z := by
  rw [sourceTrialEnergy, sourceMomentQuadratic_snoc]
  simp only [sourceMomentQuadratic, star_trivial, Matrix.mulVec_neg,
    neg_dotProduct, dotProduct_neg, neg_neg]
  ring

/-- Invertibility of the OLD prefix suffices for the residual normal equation. -/
theorem sourceTrialResidual_inverse_of_isUnit (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) (z : Fin n → ℝ) :
    (sourceMomentMatrix m s n)⁻¹ *ᵥ sourceTrialResidual m s n z =
      (sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n - z := by
  letI := hA.invertible
  rw [sourceTrialResidual, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

/-- The residual measures the error of the trial solve against the OLD block. -/
theorem sourceTrialResidual_inverse (m : ℕ → ℝ) (s n : ℕ)
    (hA : (sourceMomentMatrix m s n).PosDef) (z : Fin n → ℝ) :
    (sourceMomentMatrix m s n)⁻¹ *ᵥ sourceTrialResidual m s n z =
      (sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n - z :=
  sourceTrialResidual_inverse_of_isUnit m s n hA.isUnit z

/-- Exact error identity with only an invertible old prefix.  Symmetry is
inherited from the original moment matrix; no pivot sign enters. -/
theorem sourceTrialEnergy_eq_schur_add_residual_of_isUnit (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) (z : Fin n → ℝ) :
    sourceTrialEnergy m s n z = sourceMomentSchur m s n +
      sourceTrialResidual m s n z ⬝ᵥ
        ((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceTrialResidual m s n z) := by
  let A := sourceMomentMatrix m s n
  let b := sourceMomentCoupling m s n
  let v := A⁻¹ *ᵥ b
  letI := hA.invertible
  have hv : A *ᵥ v = b := by
    dsimp [v, A]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have ht : Aᵀ = A := by
    ext i j
    simp [A, sourceMomentMatrix, add_comm]
  have hcross : (A *ᵥ z) ⬝ᵥ v = b ⬝ᵥ z := by
    rw [dotProduct_comm (A *ᵥ z) v, Matrix.dotProduct_mulVec,
      ← ht, Matrix.vecMul_transpose, hv]
  have he : sourceTrialResidual m s n z ⬝ᵥ
      (A⁻¹ *ᵥ sourceTrialResidual m s n z) =
      b ⬝ᵥ v - 2*(b ⬝ᵥ z) + sourceMomentQuadratic m s n z := by
    rw [sourceTrialResidual_inverse_of_isUnit m s n hA]
    change (b-A *ᵥ z) ⬝ᵥ (v-z) = _
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hcross]
    change _ = b ⬝ᵥ v - 2*(b ⬝ᵥ z) + z ⬝ᵥ (A *ᵥ z)
    rw [dotProduct_comm (A *ᵥ z) z]
    ring
  rw [sourceTrialEnergy_expansion]
  change _ = (m (2*n+s)-b ⬝ᵥ v) + _
  rw [he]
  ring

/-- The same identity specialized to the established positive OLD prefix. -/
theorem sourceTrialEnergy_eq_schur_add_residual (m : ℕ → ℝ) (s n : ℕ)
    (hA : (sourceMomentMatrix m s n).PosDef) (z : Fin n → ℝ) :
    sourceTrialEnergy m s n z = sourceMomentSchur m s n +
      sourceTrialResidual m s n z ⬝ᵥ
        ((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceTrialResidual m s n z) :=
  sourceTrialEnergy_eq_schur_add_residual_of_isUnit m s n hA.isUnit z

/-- Our b-Az convention is the negative of the usual solve residual Az-b. -/
theorem sourceTrialResidual_eq_neg_solveResidual (m : ℕ → ℝ) (s n : ℕ)
    (z : Fin n → ℝ) :
    sourceTrialResidual m s n z =
      -(sourceMomentMatrix m s n *ᵥ z-sourceMomentCoupling m s n) := by
  simp only [sourceTrialResidual, neg_sub]

/-- Reversing a residual preserves its inverse quadratic form. -/
theorem residualQuadratic_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) :
    (-r) ⬝ᵥ (A⁻¹ *ᵥ (-r)) = r ⬝ᵥ (A⁻¹ *ᵥ r) := by
  rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

/-- Reversing a residual also preserves its Euclidean squared length. -/
theorem residualSquared_neg {n : ℕ} (r : Fin n → ℝ) :
    (-r) ⬝ᵥ (-r) = r ⬝ᵥ r := by
  rw [neg_dotProduct, dotProduct_neg, neg_neg]

/-- Literal identity using the usual solve residual Az-b. -/
theorem sourceTrialEnergy_eq_schur_add_solveResidual (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) (z : Fin n → ℝ) :
    sourceTrialEnergy m s n z = sourceMomentSchur m s n +
      (sourceMomentMatrix m s n *ᵥ z-sourceMomentCoupling m s n) ⬝ᵥ
        ((sourceMomentMatrix m s n)⁻¹ *ᵥ
          (sourceMomentMatrix m s n *ᵥ z-sourceMomentCoupling m s n)) := by
  rw [sourceTrialEnergy_eq_schur_add_residual_of_isUnit m s n hA z,
    sourceTrialResidual_eq_neg_solveResidual, residualQuadratic_neg]

/-- Solve for the pivot before applying an independently established bound. -/
theorem sourceMomentSchur_eq_trialEnergy_sub_residual (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) (z : Fin n → ℝ) :
    sourceMomentSchur m s n = sourceTrialEnergy m s n z -
      sourceTrialResidual m s n z ⬝ᵥ
        ((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceTrialResidual m s n z) := by
  rw [sourceTrialEnergy_eq_schur_add_residual_of_isUnit m s n hA z]
  ring

/-- Explicit lower bound from a quadratic inverse bound M.  Neither the
invertibility assumption nor this bound includes the sign of the new pivot. -/
theorem sourceMomentSchur_lower_bound_of_inverseBound (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) (M : ℝ)
    (hM : ∀ r : Fin n → ℝ,
      r ⬝ᵥ ((sourceMomentMatrix m s n)⁻¹ *ᵥ r) ≤ M*(r ⬝ᵥ r))
    (z : Fin n → ℝ) :
    sourceTrialEnergy m s n z -
      M*(sourceTrialResidual m s n z ⬝ᵥ sourceTrialResidual m s n z) ≤
        sourceMomentSchur m s n := by
  rw [sourceMomentSchur_eq_trialEnergy_sub_residual m s n hA z]
  exact sub_le_sub_left (hM (sourceTrialResidual m s n z)) _

/-- Sufficient strict positivity from the explicit M error budget. -/
theorem sourceMomentSchur_pos_of_inverseBound (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) (M : ℝ)
    (hM : ∀ r : Fin n → ℝ,
      r ⬝ᵥ ((sourceMomentMatrix m s n)⁻¹ *ᵥ r) ≤ M*(r ⬝ᵥ r))
    (z : Fin n → ℝ)
    (hcert : M*(sourceTrialResidual m s n z ⬝ᵥ sourceTrialResidual m s n z) <
      sourceTrialEnergy m s n z) :
    0 < sourceMomentSchur m s n :=
  lt_of_lt_of_le (sub_pos.mpr hcert)
    (sourceMomentSchur_lower_bound_of_inverseBound m s n hA M hM z)

/-- The same explicit lower bound in the usual Az-b convention. -/
theorem sourceMomentSchur_lower_bound_of_solveResidual (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) (M : ℝ)
    (hM : ∀ r : Fin n → ℝ,
      r ⬝ᵥ ((sourceMomentMatrix m s n)⁻¹ *ᵥ r) ≤ M*(r ⬝ᵥ r))
    (z : Fin n → ℝ) :
    sourceTrialEnergy m s n z -
      M*((sourceMomentMatrix m s n *ᵥ z-sourceMomentCoupling m s n) ⬝ᵥ
        (sourceMomentMatrix m s n *ᵥ z-sourceMomentCoupling m s n)) ≤
        sourceMomentSchur m s n := by
  have hb := sourceMomentSchur_lower_bound_of_inverseBound m s n hA M hM z
  rwa [sourceTrialResidual_eq_neg_solveResidual, residualSquared_neg] at hb

/-- Every trial energy bounds the next pivot above; using a positive trial
energy alone would have the wrong implication for the desired sign. -/
theorem sourceMomentSchur_le_trialEnergy (m : ℕ → ℝ) (s n : ℕ)
    (hA : (sourceMomentMatrix m s n).PosDef) (z : Fin n → ℝ) :
    sourceMomentSchur m s n ≤ sourceTrialEnergy m s n z := by
  rw [sourceTrialEnergy, sourceMomentSchur_sewing m s n hA]
  simp only [one_smul, one_pow, mul_one]
  exact le_add_of_nonneg_left (hA.posSemidef.dotProduct_mulVec_nonneg _)

/-- A lower quadratic bound for the old matrix controls the inverse residual.
The proof uses its normal equation and a Euclidean square, not a factorization
of the extended Gram. -/
theorem inverseResidual_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (α : ℝ) (hα : 0 < α)
    (hcoerc : ∀ y : Fin n → ℝ, α*(y ⬝ᵥ y) ≤ y ⬝ᵥ (A *ᵥ y))
    (r : Fin n → ℝ) :
    α*(r ⬝ᵥ (A⁻¹ *ᵥ r)) ≤ r ⬝ᵥ r := by
  let w := A⁻¹ *ᵥ r
  letI := hA.isUnit.invertible
  have hw : A *ᵥ w = r := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hc := hcoerc w
  rw [hw, dotProduct_comm w r] at hc
  have hs : 0 ≤ (r-α • w) ⬝ᵥ (r-α • w) := by
    simpa only [Pi.star_apply, star_trivial] using
      dotProduct_star_self_nonneg (r-α • w)
  have he : (r-α • w) ⬝ᵥ (r-α • w) =
      r ⬝ᵥ r - 2*α*(r ⬝ᵥ w) + α^2*(w ⬝ᵥ w) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm w r]
    ring
  rw [he] at hs
  have hm := mul_le_mul_of_nonneg_left hc hα.le
  change α*(r ⬝ᵥ w) ≤ r ⬝ᵥ r
  nlinarith

/-- A coercivity certificate supplies the explicit inverse bound M=1/alpha. -/
theorem inverseResidual_le_of_coercive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (α : ℝ) (hα : 0 < α)
    (hcoerc : ∀ y : Fin n → ℝ, α*(y ⬝ᵥ y) ≤ y ⬝ᵥ (A *ᵥ y))
    (r : Fin n → ℝ) :
    r ⬝ᵥ (A⁻¹ *ᵥ r) ≤ (1/α)*(r ⬝ᵥ r) := by
  have hb := inverseResidual_bound A hA α hα hcoerc r
  rw [one_div, inv_mul_eq_div]
  exact (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using hb)

/-- A sufficient certificate with no division and no positive-new-pivot
premise.  Its lower bound and residual must still be certified from the source. -/
theorem sourceMomentSchur_pos_of_trialResidual (m : ℕ → ℝ) (s n : ℕ)
    (hA : (sourceMomentMatrix m s n).PosDef) (α : ℝ) (hα : 0 < α)
    (hcoerc : ∀ y : Fin n → ℝ,
      α*(y ⬝ᵥ y) ≤ sourceMomentQuadratic m s n y)
    (z : Fin n → ℝ)
    (hcert : sourceTrialResidual m s n z ⬝ᵥ sourceTrialResidual m s n z <
      α*sourceTrialEnergy m s n z) :
    0 < sourceMomentSchur m s n := by
  have hc : ∀ y : Fin n → ℝ,
      α*(y ⬝ᵥ y) ≤ y ⬝ᵥ (sourceMomentMatrix m s n *ᵥ y) := by
    simpa only [sourceMomentQuadratic, Pi.star_apply, star_trivial] using hcoerc
  have hb := inverseResidual_bound (sourceMomentMatrix m s n) hA α hα hc
    (sourceTrialResidual m s n z)
  rw [sourceTrialEnergy_eq_schur_add_residual m s n hA z] at hcert
  have hp : 0 < α*sourceMomentSchur m s n := by nlinarith
  exact (mul_pos_iff_of_pos_left hα).mp hp

/-- Transport the independent residual certificate to the literal signed
theta gap.  The parity parameter and complete old couplings remain present. -/
theorem sourceThetaGap_pos_of_trialResidual (s : Fin 2) (n : ℕ)
    (hA : (sourceMomentMatrix h s.val n).PosDef) (α : ℝ) (hα : 0 < α)
    (hcoerc : ∀ y : Fin n → ℝ,
      α*(y ⬝ᵥ y) ≤ sourceMomentQuadratic h s.val n y)
    (z : Fin n → ℝ)
    (hcert : sourceTrialResidual h s.val n z ⬝ᵥ sourceTrialResidual h s.val n z <
      α*sourceTrialEnergy h s.val n z) :
    0 < sourceThetaGap s n := by
  have hp := sourceMomentSchur_pos_of_trialResidual h s.val n hA α hα hcoerc z hcert
  exact (criticalMargin_iff_thetaGap s n hA).mp
    ((criticalMargin_iff_pivot s n hA).mpr hp)

end
end CarryVariationalSchur
