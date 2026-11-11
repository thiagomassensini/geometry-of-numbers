import BorderedDeterminant
import SourceSchur

namespace CarrySourceBezout
open CarrySelfAdjointOperator
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false

def sourceBoundaryCoefficientIndex (n : ℕ) (b : Bool) : ℕ :=
  if b then 2*n+2 else 2*n+1

def sourceCoefficientZero (c : ℕ → ℝ) (m : ℕ) : ℕ → ℝ :=
  fun r => if r = m then 0 else c r

theorem sourceCoefficientZero_eq_update (c : ℕ → ℝ) (m : ℕ) :
    sourceCoefficientZero c m = sourceCoefficientUpdate c m (-c m) := by
  funext r
  by_cases hr : r = m
  · subst r
    simp [sourceCoefficientZero, sourceCoefficientUpdate]
  · simp [sourceCoefficientZero, sourceCoefficientUpdate, hr]

/-- Coefficients admitted before order `n` leave the old Bézout prefix unchanged. -/
theorem sourceBezout_oldPrefix_unchanged (c : ℕ → ℝ) (n : ℕ) (b : Bool) (δ : ℝ) :
    coefficientBlock
      (sourceKernel (sourceCoefficientUpdate c (sourceBoundaryCoefficientIndex n b) δ) b) n =
        coefficientBlock (sourceKernel c b) n := by
  ext i j
  cases b with
  | false =>
      have hcut : i.val+j.val+1 < 2*n+1 := by omega
      have hp : ∀ r, r ≤ i.val+j.val+1 →
          sourceCoefficientUpdate c (2*n+1) δ r = c r := by
        intro r hr
        exact sourceCoefficientUpdate_eq_of_lt c (2*n+1) δ r (by omega)
      exact sourceKernel_coefficient_depends_on_prefix
        (sourceCoefficientUpdate c (2*n+1) δ) c false i.val j.val hp
  | true =>
      have hcut : i.val+j.val+2 < 2*n+2 := by omega
      have hp : ∀ r, r ≤ i.val+j.val+2 →
          sourceCoefficientUpdate c (2*n+2) δ r = c r := by
        intro r hr
        exact sourceCoefficientUpdate_eq_of_lt c (2*n+2) δ r (by omega)
      exact sourceKernel_coefficient_depends_on_prefix
        (sourceCoefficientUpdate c (2*n+2) δ) c true i.val j.val hp

/-- The new coefficient also leaves every old-to-new coupling entry unchanged. -/
theorem sourceBezout_oldCoupling_unchanged (c : ℕ → ℝ) (n : ℕ) (b : Bool) (δ : ℝ) :
    sourceCoupling (sourceCoefficientUpdate c (sourceBoundaryCoefficientIndex n b) δ) b n =
      sourceCoupling c b n := by
  funext i
  unfold sourceCoupling
  change PowerSeries.coeff n (PowerSeries.coeff i.val
      (sourceKernel (sourceCoefficientUpdate c (sourceBoundaryCoefficientIndex n b) δ) b)) =
    PowerSeries.coeff n (PowerSeries.coeff i.val (sourceKernel c b))
  cases b with
  | false =>
      have hcut : i.val+n+1 < 2*n+1 := by omega
      have hp : ∀ r, r ≤ i.val+n+1 →
          sourceCoefficientUpdate c (2*n+1) δ r = c r := by
        intro r hr
        exact sourceCoefficientUpdate_eq_of_lt c (2*n+1) δ r (by omega)
      exact sourceKernel_coefficient_depends_on_prefix
        (sourceCoefficientUpdate c (2*n+1) δ) c false i.val n hp
  | true =>
      have hcut : i.val+n+2 < 2*n+2 := by omega
      have hp : ∀ r, r ≤ i.val+n+2 →
          sourceCoefficientUpdate c (2*n+2) δ r = c r := by
        intro r hr
        exact sourceCoefficientUpdate_eq_of_lt c (2*n+2) δ r (by omega)
      exact sourceKernel_coefficient_depends_on_prefix
        (sourceCoefficientUpdate c (2*n+2) δ) c true i.val n hp

/-- The source-defined Schur complement is affine in the newly admitted
coefficient. No sign or invertibility assumption is used in this identity. -/
theorem sourceSchur_lastCoefficient_update
    (c : ℕ → ℝ) (n : ℕ) (b : Bool) (δ : ℝ) :
    sourceSchur (sourceCoefficientUpdate c (sourceBoundaryCoefficientIndex n b) δ) b n =
      sourceSchur c b n - (sourceBoundaryCoefficientIndex n b : ℝ) * c 0 * δ := by
  cases b with
  | false =>
      have hblock := sourceBezout_lastCoefficient_rankOne c n false δ
      have hdiag := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
        M (Fin.last n) (Fin.last n)) hblock
      have hprefix := sourceBezout_oldPrefix_unchanged c n false δ
      have hcoupling := sourceBezout_oldCoupling_unchanged c n false δ
      unfold sourceSchur
      simp [sourceBoundaryCoefficientIndex] at hprefix hcoupling ⊢
      rw [hprefix, hcoupling]
      simp [lastCoordinateMatrix] at hdiag
      rw [hdiag]
      ring
  | true =>
      have hblock := sourceBezout_lastCoefficient_rankOne c n true δ
      have hdiag := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
        M (Fin.last n) (Fin.last n)) hblock
      have hprefix := sourceBezout_oldPrefix_unchanged c n true δ
      have hcoupling := sourceBezout_oldCoupling_unchanged c n true δ
      unfold sourceSchur
      simp [sourceBoundaryCoefficientIndex] at hprefix hcoupling ⊢
      rw [hprefix, hcoupling]
      simp [lastCoordinateMatrix] at hdiag
      rw [hdiag]
      ring

/-- Schur threshold for the only new coefficient of the `(n+1)`-block. The
equivalence is not itself a proof that either side has the desired sign. -/
theorem sourceBezout_lastCoefficient_threshold
    (c : ℕ → ℝ) (n : ℕ) (b : Bool) (hc0 : 0 < c 0) :
    0 < sourceSchur c b n ↔
      c (sourceBoundaryCoefficientIndex n b) <
        sourceSchur (sourceCoefficientZero c (sourceBoundaryCoefficientIndex n b)) b n /
          ((sourceBoundaryCoefficientIndex n b : ℝ) * c 0) := by
  have hzero := sourceCoefficientZero_eq_update c (sourceBoundaryCoefficientIndex n b)
  have hshift := sourceSchur_lastCoefficient_update c n b (-c (sourceBoundaryCoefficientIndex n b))
  rw [← hzero] at hshift
  have hidentity : sourceSchur c b n =
      sourceSchur (sourceCoefficientZero c (sourceBoundaryCoefficientIndex n b)) b n -
        (sourceBoundaryCoefficientIndex n b : ℝ) * c 0 *
          c (sourceBoundaryCoefficientIndex n b) := by
    linarith
  rw [hidentity]
  have hm : 0 < (sourceBoundaryCoefficientIndex n b : ℝ) * c 0 := by
    cases b <;> simp [sourceBoundaryCoefficientIndex] <;> positivity
  rw [lt_div_iff₀ hm]
  constructor <;> intro h <;> nlinarith

def sourceBezoutLastCoefficientRemainderDet (c : ℕ → ℝ) (b : Bool) (n : ℕ) : ℝ :=
  (coefficientBlock
    (sourceKernel (sourceCoefficientZero c (sourceBoundaryCoefficientIndex n b)) b)
    (n+1)).det

/-- The full source determinant is affine in the last coefficient. The constant
term is the determinant after setting exactly that coefficient to zero; no
invertibility or positivity assumption is used. -/
theorem sourceBezout_borderedDet_lastCoefficient_exact
    (c : ℕ → ℝ) (n : ℕ) (b : Bool) :
    (coefficientBlock (sourceKernel c b) (n+1)).det =
      sourceBezoutLastCoefficientRemainderDet c b n -
        (sourceBoundaryCoefficientIndex n b : ℝ) * c 0 *
          (coefficientBlock (sourceKernel c b) n).det *
            c (sourceBoundaryCoefficientIndex n b) := by
  have hzero := sourceCoefficientZero_eq_update c (sourceBoundaryCoefficientIndex n b)
  have hzero' :
      sourceCoefficientZero c (if b then 2*n+2 else 2*n+1) =
        sourceCoefficientUpdate c (if b then 2*n+2 else 2*n+1)
          (-c (if b then 2*n+2 else 2*n+1)) := by
    simpa only [sourceBoundaryCoefficientIndex] using hzero
  have hdet := sourceBezout_borderedDet_lastCoefficient c n b
    (-c (sourceBoundaryCoefficientIndex n b))
  simp only [sourceBoundaryCoefficientIndex] at hdet
  rw [← hzero'] at hdet
  unfold sourceBezoutLastCoefficientRemainderDet
  simp only [sourceBoundaryCoefficientIndex]
  linear_combination -hdet

theorem nativeSource_lastCoefficient_threshold (n : ℕ) (b : Bool) :
    sourceSchur nativeC b n =
      sourceSchur
        (sourceCoefficientZero nativeC (sourceBoundaryCoefficientIndex n b)) b n -
        (sourceBoundaryCoefficientIndex n b : ℝ) * nativeC 0 *
          nativeC (sourceBoundaryCoefficientIndex n b) := by
  have hzero := sourceCoefficientZero_eq_update nativeC
    (sourceBoundaryCoefficientIndex n b)
  have hshift := sourceSchur_lastCoefficient_update nativeC n b
    (-nativeC (sourceBoundaryCoefficientIndex n b))
  rw [← hzero] at hshift
  linarith

theorem nativeSource_pivot_iff_source_threshold (n : ℕ) (b : Bool)
    (hc0 : 0 < nativeC 0)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    0 < sourceMomentSchur nativeH (if b then 1 else 0) n ↔
      nativeC (sourceBoundaryCoefficientIndex n b) <
        sourceSchur
          (sourceCoefficientZero nativeC (sourceBoundaryCoefficientIndex n b)) b n /
            ((sourceBoundaryCoefficientIndex n b : ℝ) * nativeC 0) := by
  have h := sourceBezout_lastCoefficient_threshold nativeC n b hc0
  rw [sourceSchur_eq_scaled nativeC nativeH
    (ne_of_gt hc0)
    native_source_recurrence b n hA] at h
  simpa only [mul_pos_iff_of_pos_left (sq_pos_of_pos hc0)] using h

#print axioms sourceSchur_lastCoefficient_update
#print axioms sourceBezout_oldPrefix_unchanged
#print axioms sourceBezout_oldCoupling_unchanged
#print axioms sourceBezout_lastCoefficient_threshold
#print axioms sourceBezout_borderedDet_lastCoefficient_exact
#print axioms nativeSource_lastCoefficient_threshold
#print axioms nativeSource_pivot_iff_source_threshold

end
end CarrySourceBezout
