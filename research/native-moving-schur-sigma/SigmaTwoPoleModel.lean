import SigmaPadeCorrespondence
import Mathlib.Tactic

/-!
# Auxiliary conjugate two-pole model

This file studies a separate model sequence `m * Re (zeta^(n+1))`.  None of its
theorems identify this sequence with the original completed sigma jets.
-/

open CarryMovingSigma CarrySigmaSource
open scoped Matrix

namespace CarrySigmaPade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Real moments in the auxiliary conjugate two-pole model. -/
def twoPoleMoment (m : ℝ) (ζ : ℂ) (n : ℕ) : ℝ := m * (ζ ^ (n + 1)).re

/-- The model Hankel window at shift `s`. -/
def twoPoleGram (m : ℝ) (ζ : ℂ) (s : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => twoPoleMoment m ζ (s + i.val + j.val)

/-- The next model Hankel window. -/
def twoPoleShifted (m : ℝ) (ζ : ℂ) (s : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => twoPoleMoment m ζ (s + 1 + i.val + j.val)

theorem normSq_pow_aux (ζ : ℂ) (n : ℕ) : Complex.normSq (ζ ^ n) = Complex.normSq ζ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.normSq_mul, ih, pow_succ]

/-- Determinant of the shifted auxiliary Hankel window. -/
theorem twoPoleGram_det (m : ℝ) (ζ : ℂ) (s : ℕ) :
    (twoPoleGram m ζ s).det =
      -m ^ 2 * ζ.im ^ 2 * (Complex.normSq ζ) ^ (s + 1) := by
  let x : ℂ := ζ ^ (s + 1)
  have hp1 : ζ ^ ((s + 1) + 1) = x * ζ := by
    simp [x, pow_succ, Nat.add_assoc]
  have hp2 : ζ ^ ((s + 1) + 2) = x * ζ ^ 2 := by
    rw [pow_add]
  have h0 : twoPoleMoment m ζ s = m * x.re := by
    simp [twoPoleMoment, x]
  have h1 : twoPoleMoment m ζ (s + 1) = m * (x * ζ).re := by
    simp only [twoPoleMoment]
    rw [show s + 1 + 1 = (s + 1) + 1 by omega, hp1]
  have h2 : twoPoleMoment m ζ (s + 2) = m * (x * ζ ^ 2).re := by
    simp only [twoPoleMoment]
    rw [show s + 2 + 1 = (s + 1) + 2 by omega, hp2]
  have hdet : (twoPoleGram m ζ s).det =
      twoPoleMoment m ζ s * twoPoleMoment m ζ (s + 2) -
        twoPoleMoment m ζ (s + 1) ^ 2 := by
    simp [twoPoleGram, Matrix.det_fin_two]
    ring
  have hsqr : (ζ ^ 2).re = ζ.re ^ 2 - ζ.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  have hsqi : (ζ ^ 2).im = 2 * ζ.re * ζ.im := by
    rw [pow_two, Complex.mul_im]
    ring
  have hxnorm : Complex.normSq x = Complex.normSq ζ ^ (s + 1) := by
    simp [x, normSq_pow_aux]
  calc
    (twoPoleGram m ζ s).det =
        m * x.re * (m * (x.re * ζ.re ^ 2 - x.re * ζ.im ^ 2 -
          x.im * (2 * ζ.re * ζ.im))) -
          (m * (x.re * ζ.re - x.im * ζ.im)) ^ 2 := by
            rw [hdet, h0, h1, h2, Complex.mul_re, Complex.mul_re, hsqr, hsqi]
            ring
    _ = -m ^ 2 * ζ.im ^ 2 * Complex.normSq x := by
          simp only [Complex.normSq_apply]
          ring
    _ = -m ^ 2 * ζ.im ^ 2 * Complex.normSq ζ ^ (s + 1) := by rw [hxnorm]

/-- Every model window has a negative determinant when the node is non-real and
the model weight is positive. -/
theorem twoPoleGram_det_neg (m : ℝ) (ζ : ℂ) (s : ℕ)
    (hm : 0 < m) (hIm : ζ.im ≠ 0) : (twoPoleGram m ζ s).det < 0 := by
  rw [twoPoleGram_det]
  have hn : 0 < Complex.normSq ζ := Complex.normSq_pos.mpr (by
    intro hz
    apply hIm
    have := congrArg Complex.im hz
    simpa using this)
  have hp : 0 < (Complex.normSq ζ) ^ (s + 1) := pow_pos hn _
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hi2 : 0 < ζ.im ^ 2 := sq_pos_of_ne_zero hIm
  have hall : 0 < m ^ 2 * ζ.im ^ 2 * Complex.normSq ζ ^ (s + 1) :=
    mul_pos (mul_pos hm2 hi2) hp
  nlinarith

/-- A negative determinant excludes semidefiniteness for a real symmetric
two by two matrix. -/
theorem twoPoleGram_not_posSemidef (m : ℝ) (ζ : ℂ) (s : ℕ)
    (hm : 0 < m) (hIm : ζ.im ≠ 0) : ¬ (twoPoleGram m ζ s).PosSemidef := by
  intro hpsd
  have hdet := hpsd.det_nonneg
  have hneg := twoPoleGram_det_neg m ζ s hm hIm
  linarith

/-- A vector realizing a negative quadratic value exists for every model
window.  The statement is about this auxiliary model only. -/
theorem twoPoleGram_negative_direction (m : ℝ) (ζ : ℂ) (s : ℕ)
    (hm : 0 < m) (hIm : ζ.im ≠ 0) :
    ∃ v : Fin 2 → ℝ, v ⬝ᵥ (twoPoleGram m ζ s *ᵥ v) < 0 := by
  classical
  by_contra h
  have hnonneg : ∀ v : Fin 2 → ℝ, 0 ≤ v ⬝ᵥ (twoPoleGram m ζ s *ᵥ v) := by
    intro v
    by_contra hv
    exact h ⟨v, lt_of_not_ge hv⟩
  have hherm : (twoPoleGram m ζ s).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [twoPoleGram, twoPoleMoment, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hpsd : (twoPoleGram m ζ s).PosSemidef :=
    Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hherm, hnonneg⟩
  exact (twoPoleGram_not_posSemidef m ζ s hm hIm hpsd).elim

/-- The moments obey the second order recurrence with characteristic roots
`zeta` and its conjugate. -/
theorem twoPoleMoment_recurrence (m : ℝ) (ζ : ℂ) (n : ℕ) :
    twoPoleMoment m ζ (n + 2) =
      2 * ζ.re * twoPoleMoment m ζ (n + 1) -
        Complex.normSq ζ * twoPoleMoment m ζ n := by
  have hquad : ζ ^ 2 - (2 * ζ.re : ℂ) * ζ + (Complex.normSq ζ : ℂ) = 0 := by
    apply Complex.ext
    · simp [pow_two, Complex.mul_re, Complex.normSq_apply]
      ring
    · simp [pow_two, Complex.mul_im]
      ring
  have hquad' : ζ ^ 2 = (2 * ζ.re : ℂ) * ζ - (Complex.normSq ζ : ℂ) := by
    linear_combination hquad
  have hp2 : ζ ^ (n + 3) = ζ ^ 2 * ζ ^ (n + 1) := by
    rw [show n + 3 = 2 + (n + 1) by omega, pow_add]
  have hp1 : ζ ^ (n + 2) = ζ * ζ ^ (n + 1) := by
    rw [show n + 2 = 1 + (n + 1) by omega, pow_add]
    simp
  have hrec : ζ ^ (n + 3) =
      (2 * ζ.re : ℂ) * ζ ^ (n + 2) - (Complex.normSq ζ : ℂ) * ζ ^ (n + 1) := by
    calc
      ζ ^ (n + 3) = ζ ^ 2 * ζ ^ (n + 1) := hp2
      _ = ((2 * ζ.re : ℂ) * ζ - (Complex.normSq ζ : ℂ)) * ζ ^ (n + 1) := by rw [hquad']
      _ = (2 * ζ.re : ℂ) * (ζ * ζ ^ (n + 1)) - (Complex.normSq ζ : ℂ) * ζ ^ (n + 1) := by ring
      _ = (2 * ζ.re : ℂ) * ζ ^ (n + 2) - (Complex.normSq ζ : ℂ) * ζ ^ (n + 1) := by rw [hp1]
  have hre := congrArg Complex.re hrec
  have hre' : (ζ ^ (n + 3)).re =
      2 * ζ.re * (ζ ^ (n + 2)).re - Complex.normSq ζ * (ζ ^ (n + 1)).re := by
    simpa [Complex.sub_re, Complex.mul_re] using hre
  change m * (ζ ^ (n + 3)).re =
    2 * ζ.re * (m * (ζ ^ (n + 2)).re) -
      Complex.normSq ζ * (m * (ζ ^ (n + 1)).re)
  rw [hre']
  ring

private theorem twoPole_char_factor_generic (p q r t a b : ℝ) (lam : ℂ)
    (hr : r = 2 * a * q - b * p) (ht : t = 2 * a * r - b * q) :
    ((q : ℂ) - lam * p) * ((t : ℂ) - lam * r) -
        ((r : ℂ) - lam * q) ^ 2 =
      ((p * r - q ^ 2 : ℝ) : ℂ) *
        (lam ^ 2 - (2 * a : ℂ) * lam + (b : ℂ)) := by
  have hlin : q * r - p * t = -2 * a * (p * r - q ^ 2) := by
    rw [ht]
    linear_combination q * hr
  have hconst : q * t - r ^ 2 = b * (p * r - q ^ 2) := by
    rw [ht]
    linear_combination -r * hr
  calc
    ((q : ℂ) - lam * p) * ((t : ℂ) - lam * r) - ((r : ℂ) - lam * q) ^ 2 =
        ((p * r - q ^ 2 : ℝ) : ℂ) * lam ^ 2 +
          ((q * r - p * t : ℝ) : ℂ) * lam + ((q * t - r ^ 2 : ℝ) : ℂ) := by
            push_cast
            ring
    _ = ((p * r - q ^ 2 : ℝ) : ℂ) *
          (lam ^ 2 - (2 * a : ℂ) * lam + (b : ℂ)) := by
          rw [hlin, hconst]
          push_cast
          ring

private theorem twoPole_roots_quadratic (ζ lam : ℂ) :
    (lam - ζ) * (lam - starRingEnd ℂ ζ) =
      lam ^ 2 - (2 * ζ.re : ℂ) * lam + (Complex.normSq ζ : ℂ) := by
  have hsum : ζ + starRingEnd ℂ ζ = (2 * ζ.re : ℂ) := by
    apply Complex.ext
    · simp [Complex.conj_re]
      ring
    · simp [Complex.conj_im]
  have hprod : ζ * starRingEnd ℂ ζ = (Complex.normSq ζ : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    · simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
  calc
    (lam - ζ) * (lam - starRingEnd ℂ ζ) =
        lam ^ 2 - lam * (ζ + starRingEnd ℂ ζ) + ζ * starRingEnd ℂ ζ := by ring
    _ = lam ^ 2 - (2 * ζ.re : ℂ) * lam + (Complex.normSq ζ : ℂ) := by
      rw [hsum, hprod]
      ring

/-- The signed auxiliary pencil factors exactly at the conjugate nodes. -/
theorem twoPolePencil_characteristic (m : ℝ) (ζ : ℂ) (s : ℕ) (lam : ℂ) :
    ((twoPoleShifted m ζ s).map (algebraMap ℝ ℂ) - lam •
        (twoPoleGram m ζ s).map (algebraMap ℝ ℂ)).det =
      ((algebraMap ℝ ℂ) ((twoPoleGram m ζ s).det)) *
        (lam - ζ) * (lam - starRingEnd ℂ ζ) := by
  let p := twoPoleMoment m ζ s
  let q := twoPoleMoment m ζ (s + 1)
  let r := twoPoleMoment m ζ (s + 2)
  let t := twoPoleMoment m ζ (s + 3)
  have hr : r = 2 * ζ.re * q - Complex.normSq ζ * p := by
    dsimp [r, q, p]
    simpa [twoPoleMoment, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      twoPoleMoment_recurrence m ζ s
  have ht : t = 2 * ζ.re * r - Complex.normSq ζ * q := by
    dsimp [t, r, q]
    simpa [twoPoleMoment, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      twoPoleMoment_recurrence m ζ (s + 1)
  have hdet : (twoPoleGram m ζ s).det = p * r - q ^ 2 := by
    simp [p, q, r, twoPoleGram, Matrix.det_fin_two]
    ring
  let M := (twoPoleShifted m ζ s).map (algebraMap ℝ ℂ) -
    lam • (twoPoleGram m ζ s).map (algebraMap ℝ ℂ)
  have m00 : M 0 0 = (q : ℂ) - lam * p := by
    simp [M, p, q, twoPoleShifted, twoPoleGram, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, twoPoleMoment]
  have m01 : M 0 1 = (r : ℂ) - lam * q := by
    simp [M, q, r, twoPoleShifted, twoPoleGram, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, twoPoleMoment]
  have m10 : M 1 0 = (r : ℂ) - lam * q := by
    simp [M, q, r, twoPoleShifted, twoPoleGram, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, twoPoleMoment]
  have m11 : M 1 1 = (t : ℂ) - lam * r := by
    simp [M, r, t, twoPoleShifted, twoPoleGram, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, twoPoleMoment]
  have hmatrix : M.det =
        ((q : ℂ) - lam * p) * ((t : ℂ) - lam * r) - ((r : ℂ) - lam * q) ^ 2 := by
    rw [Matrix.det_fin_two, m00, m11, m01, m10]
    ring
  change M.det = _
  rw [hmatrix, twoPole_char_factor_generic p q r t ζ.re (Complex.normSq ζ) lam hr ht,
    hdet]
  change ((p * r - q ^ 2 : ℝ) : ℂ) *
      (lam ^ 2 - (2 * ζ.re : ℂ) * lam + (Complex.normSq ζ : ℂ)) =
    ((p * r - q ^ 2 : ℝ) : ℂ) * (lam - ζ) * (lam - starRingEnd ℂ ζ)
  calc
    ((p * r - q ^ 2 : ℝ) : ℂ) *
        (lam ^ 2 - (2 * ζ.re : ℂ) * lam + (Complex.normSq ζ : ℂ)) =
        ((p * r - q ^ 2 : ℝ) : ℂ) * ((lam - ζ) * (lam - starRingEnd ℂ ζ)) := by
          rw [twoPole_roots_quadratic]
    _ = ((p * r - q ^ 2 : ℝ) : ℂ) * (lam - ζ) * (lam - starRingEnd ℂ ζ) := by
          rw [mul_assoc]

/-- Auxiliary real two-pole moments. They describe the coalesced-displacement
model with two distinct positive heights; they are not identified with the
original sigma jets without a continuation hypothesis. -/
def twoRealPoleMoment (m₁ m₂ ρ₁ ρ₂ : ℝ) (n : ℕ) : ℝ :=
  m₁ * ρ₁ ^ (n + 1) + m₂ * ρ₂ ^ (n + 1)

def twoRealPoleGram (m₁ m₂ ρ₁ ρ₂ : ℝ) (s : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (s + i.val + j.val)

def twoRealPoleShifted (m₁ m₂ ρ₁ ρ₂ : ℝ) (s : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (s + 1 + i.val + j.val)

theorem twoRealPoleMoment_recurrence (m₁ m₂ ρ₁ ρ₂ : ℝ) (n : ℕ) :
    twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (n + 2) =
      (ρ₁ + ρ₂) * twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (n + 1) -
        ρ₁ * ρ₂ * twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ n := by
  simp [twoRealPoleMoment, pow_succ, Nat.add_left_comm,
    Nat.add_comm]
  ring

theorem twoRealPoleGram_det (m₁ m₂ ρ₁ ρ₂ : ℝ) (s : ℕ) :
    (twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).det =
      m₁ * m₂ * (ρ₁ * ρ₂) ^ (s + 1) * (ρ₁ - ρ₂) ^ 2 := by
  have h0 : twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ s =
      m₁ * ρ₁ ^ (s + 1) + m₂ * ρ₂ ^ (s + 1) := rfl
  have h1 : twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (s + 1) =
      m₁ * ρ₁ ^ (s + 1) * ρ₁ + m₂ * ρ₂ ^ (s + 1) * ρ₂ := by
    simp [twoRealPoleMoment, pow_succ, Nat.add_assoc]
    ring
  have h2 : twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (s + 2) =
      m₁ * ρ₁ ^ (s + 1) * ρ₁ ^ 2 + m₂ * ρ₂ ^ (s + 1) * ρ₂ ^ 2 := by
    simp [twoRealPoleMoment, pow_succ, Nat.add_assoc]
    ring
  have hdet : (twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).det =
      twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ s * twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (s + 2) -
        twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (s + 1) ^ 2 := by
    simp [twoRealPoleGram, Matrix.det_fin_two]
    ring
  rw [hdet, h0, h1, h2]
  calc
    (m₁ * ρ₁ ^ (s + 1) + m₂ * ρ₂ ^ (s + 1)) *
        (m₁ * ρ₁ ^ (s + 1) * ρ₁ ^ 2 + m₂ * ρ₂ ^ (s + 1) * ρ₂ ^ 2) -
        (m₁ * ρ₁ ^ (s + 1) * ρ₁ + m₂ * ρ₂ ^ (s + 1) * ρ₂) ^ 2 =
      m₁ * m₂ * (ρ₁ ^ (s + 1) * ρ₂ ^ (s + 1)) * (ρ₁ - ρ₂) ^ 2 := by ring
    _ = m₁ * m₂ * (ρ₁ * ρ₂) ^ (s + 1) * (ρ₁ - ρ₂) ^ 2 := by
      rw [← mul_pow]

theorem twoRealPoleGram_det_pos (m₁ m₂ ρ₁ ρ₂ : ℝ) (s : ℕ)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hneq : ρ₁ ≠ ρ₂) :
    0 < (twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).det := by
  rw [twoRealPoleGram_det]
  positivity

private theorem twoRealPole_roots_quadratic (ρ₁ ρ₂ : ℝ) (lam : ℂ) :
    (lam - (ρ₁ : ℂ)) * (lam - (ρ₂ : ℂ)) =
      lam ^ 2 - ((ρ₁ + ρ₂ : ℝ) : ℂ) * lam + ((ρ₁ * ρ₂ : ℝ) : ℂ) := by
  push_cast
  ring

/-- The coalesced two-real-pole model has exactly its two real nodes as
generalized pencil roots at every shift. -/
theorem twoRealPolePencil_characteristic
    (m₁ m₂ ρ₁ ρ₂ : ℝ) (s : ℕ) (lam : ℂ) :
    ((twoRealPoleShifted m₁ m₂ ρ₁ ρ₂ s).map (algebraMap ℝ ℂ) -
      lam • (twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).map (algebraMap ℝ ℂ)).det =
      ((twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).det : ℂ) *
        (lam - (ρ₁ : ℂ)) * (lam - (ρ₂ : ℂ)) := by
  let p := twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ s
  let q := twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (s + 1)
  let r := twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (s + 2)
  let t := twoRealPoleMoment m₁ m₂ ρ₁ ρ₂ (s + 3)
  let a : ℝ := (ρ₁ + ρ₂) / 2
  let b : ℝ := ρ₁ * ρ₂
  have h2a : 2 * a = ρ₁ + ρ₂ := by dsimp [a]; ring
  have hr : r = 2 * a * q - b * p := by
    dsimp [r, q, p, b]
    rw [h2a]
    exact twoRealPoleMoment_recurrence m₁ m₂ ρ₁ ρ₂ s
  have ht : t = 2 * a * r - b * q := by
    dsimp [t, r, q, b]
    rw [h2a]
    simpa [Nat.add_assoc] using twoRealPoleMoment_recurrence m₁ m₂ ρ₁ ρ₂ (s + 1)
  have hdet : (twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).det = p * r - q ^ 2 := by
    simp [p, q, r, twoRealPoleGram, Matrix.det_fin_two]
    ring
  let M := (twoRealPoleShifted m₁ m₂ ρ₁ ρ₂ s).map (algebraMap ℝ ℂ) -
    lam • (twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).map (algebraMap ℝ ℂ)
  have m00 : M 0 0 = (q : ℂ) - lam * p := by
    simp [M, p, q, twoRealPoleShifted, twoRealPoleGram, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, twoRealPoleMoment]
  have m01 : M 0 1 = (r : ℂ) - lam * q := by
    simp [M, q, r, twoRealPoleShifted, twoRealPoleGram, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, twoRealPoleMoment]
  have m10 : M 1 0 = (r : ℂ) - lam * q := by
    simp [M, q, r, twoRealPoleShifted, twoRealPoleGram, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, twoRealPoleMoment]
  have m11 : M 1 1 = (t : ℂ) - lam * r := by
    simp [M, r, t, twoRealPoleShifted, twoRealPoleGram, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, twoRealPoleMoment]
  have hmatrix : M.det =
      ((q : ℂ) - lam * p) * ((t : ℂ) - lam * r) - ((r : ℂ) - lam * q) ^ 2 := by
    rw [Matrix.det_fin_two, m00, m11, m01, m10]
    ring
  change M.det = _
  rw [hmatrix, twoPole_char_factor_generic p q r t a b lam hr ht, hdet]
  have h2aC : (2 : ℂ) * (a : ℂ) = ((ρ₁ + ρ₂ : ℝ) : ℂ) := by
    exact_mod_cast h2a
  have hbC : (b : ℂ) = ((ρ₁ * ρ₂ : ℝ) : ℂ) := by simp [b]
  have hpoly : lam ^ 2 - 2 * (a : ℂ) * lam + (b : ℂ) =
      lam ^ 2 - ((ρ₁ + ρ₂ : ℝ) : ℂ) * lam + ((ρ₁ * ρ₂ : ℝ) : ℂ) := by
    rw [h2aC, hbC]
  rw [hpoly]
  calc
    ((p * r - q ^ 2 : ℝ) : ℂ) *
        (lam ^ 2 - ((ρ₁ + ρ₂ : ℝ) : ℂ) * lam + ((ρ₁ * ρ₂ : ℝ) : ℂ)) =
        ((p * r - q ^ 2 : ℝ) : ℂ) *
          ((lam - (ρ₁ : ℂ)) * (lam - (ρ₂ : ℂ))) := by
            rw [twoRealPole_roots_quadratic]
    _ = ((p * r - q ^ 2 : ℝ) : ℂ) *
          (lam - (ρ₁ : ℂ)) * (lam - (ρ₂ : ℂ)) := by rw [mul_assoc]

/-- With two positive weights and distinct positive real nodes, the coalesced
model has a regular Gram window and its two pencil roots are exactly the two
real nodes at every shift. -/
theorem twoRealPolePencil_real_roots
    (m₁ m₂ ρ₁ ρ₂ : ℝ) (s : ℕ)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hneq : ρ₁ ≠ ρ₂) :
    0 < (twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).det ∧
      ((twoRealPoleShifted m₁ m₂ ρ₁ ρ₂ s).map (algebraMap ℝ ℂ) -
        (ρ₁ : ℂ) • (twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).map
          (algebraMap ℝ ℂ)).det = 0 ∧
      ((twoRealPoleShifted m₁ m₂ ρ₁ ρ₂ s).map (algebraMap ℝ ℂ) -
        (ρ₂ : ℂ) • (twoRealPoleGram m₁ m₂ ρ₁ ρ₂ s).map
          (algebraMap ℝ ℂ)).det = 0 := by
  refine ⟨twoRealPoleGram_det_pos m₁ m₂ ρ₁ ρ₂ s hm₁ hm₂ hρ₁ hρ₂ hneq, ?_, ?_⟩
  · simpa using twoRealPolePencil_characteristic m₁ m₂ ρ₁ ρ₂ s (ρ₁ : ℂ)
  · simpa using twoRealPolePencil_characteristic m₁ m₂ ρ₁ ρ₂ s (ρ₂ : ℂ)

/-- The inverse-square node for a pair of heights. -/
def inverseSquareNode (γ δ : ℝ) : ℂ := ((γ : ℂ) + (δ : ℂ) * Complex.I)⁻¹ ^ 2

private theorem inverseSquareNode_aux (γ δ : ℝ) :
    let w : ℂ := (γ : ℂ) + (δ : ℂ) * Complex.I
    w.re = γ ∧ w.im = δ ∧ Complex.normSq w = γ ^ 2 + δ ^ 2 := by
  dsimp
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im]
  ring

/-- Real part of the inverse-square node. -/
theorem inverseSquareNode_re (γ δ : ℝ) (hγ : 0 < γ) :
    (inverseSquareNode γ δ).re = (γ ^ 2 - δ ^ 2) / (γ ^ 2 + δ ^ 2) ^ 2 := by
  let w : ℂ := (γ : ℂ) + (δ : ℂ) * Complex.I
  obtain ⟨hwre, hwim, hnorm⟩ := inverseSquareNode_aux γ δ
  have hS : 0 < γ ^ 2 + δ ^ 2 := by positivity
  have hInvRe : w⁻¹.re = γ / (γ ^ 2 + δ ^ 2) := by
    rw [Complex.inv_re, hwre, hnorm]
  have hInvIm : w⁻¹.im = -δ / (γ ^ 2 + δ ^ 2) := by
    rw [Complex.inv_im, hwim, hnorm]
  change (w⁻¹ ^ 2).re = _
  rw [pow_two, Complex.mul_re, hInvRe, hInvIm]
  field_simp [hS.ne']

/-- Imaginary part of the inverse-square node. -/
theorem inverseSquareNode_im (γ δ : ℝ) (hγ : 0 < γ) :
    (inverseSquareNode γ δ).im = -(2 * γ * δ) / (γ ^ 2 + δ ^ 2) ^ 2 := by
  let w : ℂ := (γ : ℂ) + (δ : ℂ) * Complex.I
  obtain ⟨hwre, hwim, hnorm⟩ := inverseSquareNode_aux γ δ
  have hS : 0 < γ ^ 2 + δ ^ 2 := by positivity
  have hInvRe : w⁻¹.re = γ / (γ ^ 2 + δ ^ 2) := by
    rw [Complex.inv_re, hwre, hnorm]
  have hInvIm : w⁻¹.im = -δ / (γ ^ 2 + δ ^ 2) := by
    rw [Complex.inv_im, hwim, hnorm]
  change (w⁻¹ ^ 2).im = _
  rw [pow_two, Complex.mul_im, hInvRe, hInvIm]
  field_simp [hS.ne']
  ring

/-- Norm square of the inverse-square node. -/
theorem inverseSquareNode_normSq (γ δ : ℝ) (hγ : 0 < γ) :
    Complex.normSq (inverseSquareNode γ δ) = 1 / (γ ^ 2 + δ ^ 2) ^ 2 := by
  let w : ℂ := (γ : ℂ) + (δ : ℂ) * Complex.I
  obtain ⟨_, _, hnorm⟩ := inverseSquareNode_aux γ δ
  have hS : 0 < γ ^ 2 + δ ^ 2 := by positivity
  change Complex.normSq (w⁻¹ ^ 2) = _
  rw [normSq_pow_aux, Complex.normSq_inv, hnorm]
  field_simp

/-- Closed determinant formula after inverse-square specialization. -/
theorem inverseSquare_twoPoleGram_det (m γ δ : ℝ) (s : ℕ)
    (hγ : 0 < γ) :
    (twoPoleGram m (inverseSquareNode γ δ) s).det =
      -4 * m ^ 2 * γ ^ 2 * δ ^ 2 / (γ ^ 2 + δ ^ 2) ^ (2 * s + 6) := by
  let S := γ ^ 2 + δ ^ 2
  have hS : 0 < S := by dsimp [S]; positivity
  have hpow : S ^ 4 * (S ^ 2) ^ (s + 1) = S ^ (2 * s + 6) := by
    calc
      S ^ 4 * (S ^ 2) ^ (s + 1) = S ^ 4 * S ^ (2 * (s + 1)) := by rw [pow_mul]
      _ = S ^ (4 + 2 * (s + 1)) := by rw [← pow_add]
      _ = S ^ (2 * s + 6) := by congr 1; omega
  rw [twoPoleGram_det, inverseSquareNode_im γ δ hγ,
    inverseSquareNode_normSq γ δ hγ]
  change -m ^ 2 * (-(2 * γ * δ) / S ^ 2) ^ 2 * (1 / S ^ 2) ^ (s + 1) = _
  calc
    -m ^ 2 * (-(2 * γ * δ) / S ^ 2) ^ 2 * (1 / S ^ 2) ^ (s + 1) =
        -4 * m ^ 2 * γ ^ 2 * δ ^ 2 / (S ^ 4 * (S ^ 2) ^ (s + 1)) := by
          simp only [div_pow, one_pow, neg_sq]
          field_simp [hS.ne']
          ring
    _ = -4 * m ^ 2 * γ ^ 2 * δ ^ 2 / S ^ (2 * s + 6) := by rw [hpow]

/-- The inverse-square specialization has a negative direction at every shift. -/
theorem inverseSquare_twoPole_negative_direction (m γ δ : ℝ) (s : ℕ)
    (hm : 0 < m) (hγ : 0 < γ) (hδ : δ ≠ 0) :
    ∃ v : Fin 2 → ℝ,
      v ⬝ᵥ (twoPoleGram m (inverseSquareNode γ δ) s *ᵥ v) < 0 := by
  apply twoPoleGram_negative_direction
  · exact hm
  · rw [inverseSquareNode_im γ δ hγ]
    apply div_ne_zero
    · exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hγ.ne') hδ)
    · positivity

/-- The two roots of the auxiliary pencil are non-real conjugates. -/
theorem inverseSquare_twoPole_roots (m γ δ : ℝ) (s : ℕ)
    (hγ : 0 < γ) (hδ : δ ≠ 0) :
    let ζ := inverseSquareNode γ δ
    ζ.im ≠ 0 ∧ ζ ≠ starRingEnd ℂ ζ ∧
      ((twoPoleShifted m ζ s).map (algebraMap ℝ ℂ) - ζ •
        (twoPoleGram m ζ s).map (algebraMap ℝ ℂ)).det = 0 ∧
      ((twoPoleShifted m ζ s).map (algebraMap ℝ ℂ) -
        (starRingEnd ℂ ζ) • (twoPoleGram m ζ s).map (algebraMap ℝ ℂ)).det = 0 := by
  dsimp
  have him : (inverseSquareNode γ δ).im ≠ 0 := by
    rw [inverseSquareNode_im γ δ hγ]
    apply div_ne_zero
    · exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hγ.ne') hδ)
    · positivity
  refine ⟨him, ?_, ?_, ?_⟩
  · intro heq
    have h := congrArg Complex.im heq
    rw [Complex.conj_im] at h
    have hz : (inverseSquareNode γ δ).im = 0 := by linarith
    exact him hz
  · simpa using twoPolePencil_characteristic m (inverseSquareNode γ δ) s
      (inverseSquareNode γ δ)
  · simpa using twoPolePencil_characteristic m (inverseSquareNode γ δ) s
      (starRingEnd ℂ (inverseSquareNode γ δ))

/-- At the coalesced parameter `delta = 0`, the auxiliary Gram window is
singular and its characteristic determinant vanishes for every spectral
parameter. Thus the regular-pencil root classification is not defined at the
limit, even though the two non-real roots converge to a real value. -/
theorem inverseSquare_zero_parameter_pencil_characteristic
    (m γ : ℝ) (s : ℕ) (lam : ℂ) (hγ : 0 < γ) :
    ((twoPoleShifted m (inverseSquareNode γ 0) s).map (algebraMap ℝ ℂ) -
      lam • (twoPoleGram m (inverseSquareNode γ 0) s).map
        (algebraMap ℝ ℂ)).det = 0 := by
  have hdet : (twoPoleGram m (inverseSquareNode γ 0) s).det = 0 := by
    rw [inverseSquare_twoPoleGram_det m γ 0 s hγ]
    simp
  rw [twoPolePencil_characteristic, hdet]
  simp

/-- The inverse-square roots recover both heights as real parts. -/
theorem inverseSquare_roots_recover_height (γ δ : ℝ) (hγ : 0 < γ) :
    ∃ wPos wNeg : ℂ,
      wPos ^ 2 = (inverseSquareNode γ δ)⁻¹ ∧
      wNeg ^ 2 = (starRingEnd ℂ (inverseSquareNode γ δ))⁻¹ ∧
      wPos.re = γ ∧ wPos.im = δ ∧ wNeg.re = γ ∧ wNeg.im = -δ := by
  let w : ℂ := (γ : ℂ) + (δ : ℂ) * Complex.I
  have hw : w ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp [w] at hr
    exact hγ.ne' hr
  refine ⟨w, starRingEnd ℂ w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change w ^ 2 = (w⁻¹ ^ 2)⁻¹
    rw [inv_pow, inv_inv]
  · simp [inverseSquareNode, w, map_pow, inv_pow, inv_inv]
  · simp [w]
  · simp [w]
  · simp [w]
  · simp [w]

end
end CarrySigmaPade

#print axioms CarrySigmaPade.twoPoleGram_det
#print axioms CarrySigmaPade.twoPoleGram_negative_direction
#print axioms CarrySigmaPade.twoPoleMoment_recurrence
#print axioms CarrySigmaPade.twoPolePencil_characteristic
#print axioms CarrySigmaPade.inverseSquare_twoPoleGram_det
#print axioms CarrySigmaPade.inverseSquare_twoPole_roots
#print axioms CarrySigmaPade.inverseSquare_zero_parameter_pencil_characteristic
#print axioms CarrySigmaPade.inverseSquare_roots_recover_height
