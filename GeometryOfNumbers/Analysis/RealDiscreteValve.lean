import GeometryOfNumbers.Analysis.QuadraticCenteredBracket
import Mathlib.Tactic

/-! # Exact vertical discrete Green reconstruction

Local rewrite of the historical finite algebra; see SOURCE_PROVENANCE.md.
-/

namespace GeometryOfNumbers.Analysis.DiscreteValve

variable {E : Type*} [AddCommGroup E]

/-- Forward difference along the discrete vertical index. -/
def fdiff (f : ℕ → E) (k : ℕ) : E := f (k + 1) - f k

/-- Vertical curvature: right minus twice center plus left. -/
def bracket (f : ℕ → E) (j : ℕ) : E := f (j + 2) - 2 • f (j + 1) + f j

theorem bracket_eq_fdiff_sub (f : ℕ → E) (j : ℕ) :
    bracket f j = fdiff f (j + 1) - fdiff f j := by
  simp only [bracket, fdiff, two_smul]; abel

/-- Historical Green sum reconstructing coordinate n+1. -/
def greenSum (f : ℕ → E) (n : ℕ) : E :=
  ∑ j ∈ Finset.range n, (n - j) • bracket f j

theorem sum_range_bracket (f : ℕ → E) (n : ℕ) :
    ∑ j ∈ Finset.range n, bracket f j = fdiff f n - fdiff f 0 := by
  simp only [bracket_eq_fdiff_sub]
  exact Finset.sum_range_sub (fdiff f) n

theorem greenSum_succ (f : ℕ → E) (n : ℕ) :
    greenSum f (n + 1) = greenSum f n + (fdiff f (n + 1) - fdiff f 0) := by
  have e1 : greenSum f (n + 1)
      = (∑ j ∈ Finset.range n, ((n - j) • bracket f j + bracket f j))
        + bracket f n := by
    unfold greenSum
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
      have hsub : n + 1 - j = (n - j) + 1 := by omega
      rw [hsub, succ_nsmul]
    · have hlast : n + 1 - n = 1 := by omega
      rw [hlast, one_smul]
  have hB : (∑ j ∈ Finset.range n, bracket f j) + bracket f n
      = fdiff f (n + 1) - fdiff f 0 := by
    rw [← Finset.sum_range_succ]
    exact sum_range_bracket f (n + 1)
  rw [e1, Finset.sum_add_distrib]
  show (greenSum f n + ∑ j ∈ Finset.range n, bracket f j) + bracket f n
      = greenSum f n + (fdiff f (n + 1) - fdiff f 0)
  rw [← hB]; abel

/-- The complete state is affine boundary return plus causal Green interior. -/
theorem realDiscreteGreenReconstruction (f : ℕ → E) (n : ℕ) :
    f (n + 1) = f 0 + (n + 1) • (f 1 - f 0) + greenSum f n := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, greenSum, Finset.range_zero, Finset.sum_empty,
      add_zero, one_smul]
    abel
  | succ n ih =>
    have hstep : f (n + 1 + 1) = f (n + 1) + fdiff f (n + 1) := by
      simp only [fdiff]; abel
    have hf0 : fdiff f 0 = f 1 - f 0 := rfl
    have hsmul : (n + 1 + 1) • (f 1 - f 0) = (n + 1) • (f 1 - f 0) + (f 1 - f 0) := by
      rw [succ_nsmul]
    rw [hstep, ih, greenSum_succ, hf0, hsmul]
    abel

theorem bracket_greenSum (f : ℕ → E) (n : ℕ) :
    greenSum f (n + 1 + 1) - 2 • greenSum f (n + 1) + greenSum f n
      = bracket f (n + 1) := by
  rw [greenSum_succ f (n + 1), greenSum_succ f n, bracket_eq_fdiff_sub f (n + 1),
    two_smul]
  abel

theorem greenSum_zero (f : ℕ → E) : greenSum f 0 = 0 := by
  simp [greenSum]

theorem bracket_eq_zero_iff_affine (f : ℕ → E) :
    (∀ j, bracket f j = 0) ↔ ∀ n, f n = f 0 + n • (f 1 - f 0) := by
  constructor
  · intro hbr n
    cases n with
    | zero => simp
    | succ m =>
      have hg : greenSum f m = 0 := by
        unfold greenSum
        apply Finset.sum_eq_zero
        intro j _
        rw [hbr j, smul_zero]
      rw [realDiscreteGreenReconstruction f m, hg, add_zero]
  · intro haff j
    rw [bracket_eq_fdiff_sub]
    have hf : ∀ k, fdiff f k = f 1 - f 0 := by
      intro k
      unfold fdiff
      rw [haff (k + 1), haff k, succ_nsmul]
      abel
    rw [hf (j + 1), hf j, sub_self]

theorem bracket_add (f g : ℕ → E) (j : ℕ) :
    bracket (f + g) j = bracket f j + bracket g j := by
  simp only [bracket, Pi.add_apply]
  abel

theorem greenSum_add (f g : ℕ → E) (n : ℕ) :
    greenSum (f + g) n = greenSum f n + greenSum g n := by
  unfold greenSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [bracket_add, smul_add]


/-- The vertical stencil uses the existing real three-point readout.
This identifies the readout only, never horizontal and vertical indices. -/
theorem bracket_eq_realCenteredReadout (f : ℕ → ℝ) (k : ℕ) :
    bracket f k = realCenteredReadout (f k) (f (k + 1)) (f (k + 2)) := by
  simp only [bracket, realCenteredReadout, nsmul_eq_mul]
  ring

end GeometryOfNumbers.Analysis.DiscreteValve

namespace GeometryOfNumbers.Analysis

variable {A : Type*} [AddCommGroup A]

def causalUnitBracket (x : ℕ → A) (left : ℕ) : A :=
  x left - 2 • x (left + 1) + x (left + 2)

theorem rightLeg_eq_bracket_sub_left_add_two_center
    (x : ℕ → A) (left : ℕ) :
    x (left + 2) =
      causalUnitBracket x left - x left + 2 • x (left + 1) := by
  unfold causalUnitBracket
  abel

theorem rightLeg_eq_of_left_center_bracket_eq
    {x y : ℕ → A} {left : ℕ}
    (hleft : x left = y left)
    (hcenter : x (left + 1) = y (left + 1))
    (hbracket : causalUnitBracket x left = causalUnitBracket y left) :
    x (left + 2) = y (left + 2) := by
  calc
    x (left + 2) =
        causalUnitBracket x left - x left + 2 • x (left + 1) :=
      rightLeg_eq_bracket_sub_left_add_two_center x left
    _ = causalUnitBracket y left - y left + 2 • y (left + 1) := by
      rw [hbracket, hleft, hcenter]
    _ = y (left + 2) :=
      (rightLeg_eq_bracket_sub_left_add_two_center y left).symm

structure CausalBracketData (A : Type*) where
  leftSeed : A
  centerSeed : A
  bracket : ℕ → A

def causalBracketReconstruction (data : CausalBracketData A) : ℕ → A :=
  Nat.twoStepInduction data.leftSeed data.centerSeed
    (fun n left center ↦ data.bracket n - left + 2 • center)

@[simp] theorem causalBracketReconstruction_zero
    (data : CausalBracketData A) :
    causalBracketReconstruction data 0 = data.leftSeed := rfl

@[simp] theorem causalBracketReconstruction_one
    (data : CausalBracketData A) :
    causalBracketReconstruction data 1 = data.centerSeed := rfl

theorem causalBracketReconstruction_step
    (data : CausalBracketData A) (n : ℕ) :
    causalBracketReconstruction data (n + 2) =
      data.bracket n - causalBracketReconstruction data n +
        2 • causalBracketReconstruction data (n + 1) := rfl

@[simp] theorem causalUnitBracket_reconstruction
    (data : CausalBracketData A) (n : ℕ) :
    causalUnitBracket (causalBracketReconstruction data) n =
      data.bracket n := by
  rw [causalUnitBracket, causalBracketReconstruction_step]
  abel

theorem eq_of_seed_eq_of_causalUnitBracket_eq
    {x y : ℕ → A}
    (hleft : x 0 = y 0) (hcenter : x 1 = y 1)
    (hbracket : ∀ n, causalUnitBracket x n = causalUnitBracket y n) :
    x = y := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => exact hleft
  | one => exact hcenter
  | more n hn hn1 =>
      exact rightLeg_eq_of_left_center_bracket_eq hn hn1 (hbracket n)


end GeometryOfNumbers.Analysis
