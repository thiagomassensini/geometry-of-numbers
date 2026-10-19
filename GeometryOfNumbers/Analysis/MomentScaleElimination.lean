import GeometryOfNumbers.Analysis.FiniteClockHeightLedger
import GeometryOfNumbers.Analysis.CarryMaterialSourceFactor

/-! Scale covariance of the existing signed elimination and Cholesky
candidate. No positivity of canonical moments or replacement source is used. -/
namespace GeometryOfNumbers.Analysis.CarryScale
open FiniteClockHeightLedger
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The mass factor multiplies the EXISTING scaledMoment action. -/
def massScaledMoment (a q : ℝ) (h : ℕ → ℝ) (r : ℕ) : ℝ := a * scaledMoment q h r

def diagonalScale (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => q^i.val)

theorem scaled_hankel (a q : ℝ) (h : ℕ → ℝ) (N : ℕ) :
    hankelGram (massScaledMoment a q h) N =
      a • (diagonalScale q N * hankelGram h N * diagonalScale q N) := by
  ext i j
  simp only [massScaledMoment, scaledMoment, diagonalScale, hankelGram, pow_add,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  ring

theorem scaled_shifted (a q : ℝ) (h : ℕ → ℝ) (N : ℕ) :
    shiftedHankel (massScaledMoment a q h) N =
      (a*q) • (diagonalScale q N * shiftedHankel h N * diagonalScale q N) := by
  ext i j
  simp [massScaledMoment, scaledMoment, diagonalScale, shiftedHankel, pow_add]
  ring

/-- Arbitrary nonzero diagonal action; even zero pivots retain their remainder. -/
theorem elimination_scale (K : ℕ → ℕ → ℝ) (a : ℝ) (d : ℕ → ℝ)
    (ha : a ≠ 0) (hd : ∀ i, d i ≠ 0) (r i j : ℕ) :
    carryPairingRemainder (fun i j => a*d i*d j*K i j) r i j =
      a*d i*d j*carryPairingRemainder K r i j := by
  induction r generalizing i j with
  | zero => rfl
  | succ r ih =>
    simp only [carryPairingRemainder, ih]
    by_cases hp : carryPairingRemainder K r r r = 0
    · simp [hp]
    · field_simp [ha, hd r, hp]

theorem pivot_scale (K : ℕ → ℕ → ℝ) (a : ℝ) (d : ℕ → ℝ)
    (ha : a ≠ 0) (hd : ∀ i, d i ≠ 0) (r : ℕ) :
    carryPairingPivot (fun i j => a*d i*d j*K i j) r =
      a*(d r)^2*carryPairingPivot K r := by
  rw [carryPairingPivot, elimination_scale K a d ha hd]
  unfold carryPairingPivot
  ring

theorem column_scale (K : ℕ → ℕ → ℝ) (a : ℝ) (d : ℕ → ℝ)
    (ha : a ≠ 0) (hd : ∀ i, d i ≠ 0) (r i : ℕ) :
    carryPairingColumn (fun i j => a*d i*d j*K i j) r i =
      (d i/d r)*carryPairingColumn K r i := by
  simp only [carryPairingColumn, carryPairingPivot,
    elimination_scale K a d ha hd]
  by_cases hp : carryPairingRemainder K r r r = 0
  · simp [hp]
  · field_simp [ha, hd r, hp]

/-- The deterministic Cholesky candidate itself, not just some square factor. -/
theorem cholesky_scale (K : ℕ → ℕ → ℝ) (a : ℝ) (d : ℕ → ℝ)
    (ha : 0 < a) (hd : ∀ i, 0 < d i) (N : ℕ) :
    carryPairingCholesky (fun i j => a*d i*d j*K i j) N =
      Real.sqrt a • (Matrix.diagonal (fun i : Fin N => d i.val)*carryPairingCholesky K N) := by
  ext i j
  rw [carryPairingCholesky, column_scale K a d ha.ne' (fun i => (hd i).ne'),
    pivot_scale K a d ha.ne' (fun i => (hd i).ne')]
  rw [Real.sqrt_mul (mul_nonneg ha.le (sq_nonneg _)), Real.sqrt_mul ha.le,
    Real.sqrt_sq (hd j).le]
  simp only [Matrix.smul_apply, Matrix.diagonal_mul, carryPairingCholesky, smul_eq_mul]
  field_simp [(hd j).ne']

/-- The row scale is q^i for Hankel, and the old crossings remain present. -/
theorem hankel_pivot_scale (h : ℕ → ℝ) (a q : ℝ)
    (ha : a ≠ 0) (hq : q ≠ 0) (r : ℕ) :
    carryPairingPivot (fun i j => massScaledMoment a q h (i+j)) r =
      a*q^(2*r)*carryPairingPivot (fun i j => h (i+j)) r := by
  have he : (fun i j => massScaledMoment a q h (i+j)) =
      (fun i j => a*q^i*q^j*h (i+j)) := by
    funext i j; simp [massScaledMoment, scaledMoment, pow_add, mul_assoc]
  rw [he, pivot_scale _ a (fun i => q^i) ha (fun i => pow_ne_zero i hq)]
  simp [← pow_mul, Nat.mul_comm]

theorem hankel_cholesky_scale (h : ℕ → ℝ) (a q : ℝ)
    (ha : 0 < a) (hq : 0 < q) (N : ℕ) :
    carryPairingCholesky (fun i j => massScaledMoment a q h (i+j)) N =
      Real.sqrt a • (diagonalScale q N * carryPairingCholesky (fun i j => h (i+j)) N) := by
  have he : (fun i j => massScaledMoment a q h (i+j)) =
      (fun i j => a*q^i*q^j*h (i+j)) := by
    funext i j; simp [massScaledMoment, scaledMoment, pow_add, mul_assoc]
  rw [he]
  exact cholesky_scale _ a (fun i => q^i) ha (fun i => pow_pos hq i) N

/-- Three consecutive pivot ratios are invariant. The totalized identity also
covers a zero denominator; its ordinary ratio interpretation requires nonzero. -/
theorem pivot_ratio_invariant (K : ℕ → ℕ → ℝ) (a q : ℝ)
    (ha : a ≠ 0) (hq : q ≠ 0) (r : ℕ) :
    carryPairingPivot (fun i j => a*q^i*q^j*K i j) (r+2)*
        carryPairingPivot (fun i j => a*q^i*q^j*K i j) r /
        (carryPairingPivot (fun i j => a*q^i*q^j*K i j) (r+1))^2 =
      carryPairingPivot K (r+2)*carryPairingPivot K r/(carryPairingPivot K (r+1))^2 := by
  simp only [pivot_scale K a (fun i => q^i) ha (fun i => pow_ne_zero i hq)]
  by_cases hp : carryPairingPivot K (r+1) = 0
  · simp [hp]
  · simp only [pow_succ]
    field_simp [ha, hq, hp]

/-- Both parity sectors, with the original shift retained. -/
theorem sector_pivot_scale (h : ℕ → ℝ) (a q : ℝ)
    (ha : a ≠ 0) (hq : q ≠ 0) (sector r : ℕ) :
    carryPairingPivot (fun i j => massScaledMoment a q h (i+j+sector)) r =
      a*q^(2*r+sector)*carryPairingPivot (fun i j => h (i+j+sector)) r := by
  have he : (fun i j => massScaledMoment a q h (i+j+sector)) =
      (fun i j => (a*q^sector)*q^i*q^j*h (i+j+sector)) := by
    funext i j; simp only [massScaledMoment, scaledMoment, pow_add]; ring
  rw [he, pivot_scale _ (a*q^sector) (fun i => q^i)
    (mul_ne_zero ha (pow_ne_zero sector hq)) (fun i => pow_ne_zero i hq)]
  simp only [pow_add, pow_mul]
  ring

theorem hankel_pivot_sign (h : ℕ → ℝ) (a q : ℝ)
    (ha : 0 < a) (hq : 0 < q) (r : ℕ) :
    (0 < carryPairingPivot (fun i j => massScaledMoment a q h (i+j)) r) ↔
      0 < carryPairingPivot (fun i j => h (i+j)) r := by
  rw [hankel_pivot_scale h a q ha.ne' hq.ne']
  exact mul_pos_iff_of_pos_left (mul_pos ha (pow_pos hq _))

/-- Camera invariance and a nontrivial moment dilation cannot be the same action. -/
theorem fixed_moment_scale_rigid (h : ℕ → ℝ) (a q : ℝ)
    (h0 : h 0 ≠ 0) (h1 : h 1 ≠ 0) (he : massScaledMoment a q h = h) : a = 1 ∧ q = 1 := by
  have hz := congrFun he 0
  have ho := congrFun he 1
  simp only [massScaledMoment, scaledMoment, pow_zero, one_mul, pow_one] at hz ho
  have ha : a = 1 := (mul_left_inj' h0).mp (by simpa using hz)
  refine ⟨ha, ?_⟩
  rw [ha, one_mul] at ho
  exact (mul_left_inj' h1).mp (by simpa using ho)

end
end GeometryOfNumbers.Analysis.CarryScale
