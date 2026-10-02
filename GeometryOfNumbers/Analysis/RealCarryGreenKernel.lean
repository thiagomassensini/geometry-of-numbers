import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-! # Summable vertical Green kernel and bounded shift-series operator

Real rewrite of the historical vertical construction; no prime specialization.
The parameter eta is vertical and independent of center-leg deformation.
-/

open scoped BigOperators
open Filter

namespace GeometryOfNumbers.Analysis.RealCarry

noncomputable section

def carryWeightedVerticalGreenKernel (eta : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) * eta ^ r

@[simp] theorem carryWeightedVerticalGreenKernel_zero (eta : ℝ) :
    carryWeightedVerticalGreenKernel eta 0 = 0 := by
  simp [carryWeightedVerticalGreenKernel]

theorem carryWeightedVerticalGreenKernel_nonneg
    {eta : ℝ} (heta : 0 ≤ eta) (r : ℕ) :
    0 ≤ carryWeightedVerticalGreenKernel eta r := by
  unfold carryWeightedVerticalGreenKernel
  positivity

def carryConjugatedVerticalGreenKernel
    (eta : ℝ) (k j : ℕ) : ℝ :=
  if j < k then carryWeightedVerticalGreenKernel eta (k - j) else 0

@[simp] theorem carryConjugatedVerticalGreenKernel_of_lt
    (eta : ℝ) {k j : ℕ} (hjk : j < k) :
    carryConjugatedVerticalGreenKernel eta k j =
      carryWeightedVerticalGreenKernel eta (k - j) := by
  simp [carryConjugatedVerticalGreenKernel, hjk]

@[simp] theorem carryConjugatedVerticalGreenKernel_of_not_lt
    (eta : ℝ) {k j : ℕ} (hjk : ¬j < k) :
    carryConjugatedVerticalGreenKernel eta k j = 0 := by
  simp [carryConjugatedVerticalGreenKernel, hjk]

theorem carryWeightedVerticalGreenKernel_summable
    {eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    Summable (carryWeightedVerticalGreenKernel eta) := by
  let a : ℝ := (eta + 1) / 2
  have hetaa : eta < a := by
    dsimp [a]
    linarith
  have ha1 : a < 1 := by
    dsimp [a]
    linarith
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith
  have hgeom : Summable (fun n : ℕ => a ^ n) :=
    summable_geometric_of_lt_one ha0 ha1
  have hnorm : ‖eta‖ < a := by
    simpa [Real.norm_eq_abs, abs_of_nonneg heta0] using hetaa
  have hlittle :
      (fun n : ℕ => (n : ℝ) * eta ^ n) =o[atTop]
        (fun n : ℕ => a ^ n) := by
    simpa only [pow_one] using
      (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
        (R := ℝ) 1 hnorm)
  rcases hlittle.isBigO.exists_pos with ⟨C, _hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * a ^ n) :=
    hgeom.mul_left C
  refine hmajor.of_norm_bounded_eventually_nat ?_
  filter_upwards [hC.bound] with n hn
  simpa [carryWeightedVerticalGreenKernel, Real.norm_eq_abs,
    abs_of_nonneg heta0, abs_of_nonneg ha0] using hn

structure CarryVerticalShiftFamily (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  shift : ℕ → H →L[ℝ] H
  norm_shift_le_one : ∀ r : ℕ, ‖shift r‖ ≤ 1

section ShiftFamily

variable {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

def carryWeightedVerticalGreenTerm
    (S : CarryVerticalShiftFamily H) (eta : ℝ) (r : ℕ) : H →L[ℝ] H :=
  (carryWeightedVerticalGreenKernel eta r : ℝ) • S.shift r

theorem carryWeightedVerticalGreenTerm_norm_le
    (S : CarryVerticalShiftFamily H) {eta : ℝ} (heta0 : 0 ≤ eta) (r : ℕ) :
    ‖carryWeightedVerticalGreenTerm S eta r‖ ≤
      carryWeightedVerticalGreenKernel eta r := by
  have hk0 : 0 ≤ carryWeightedVerticalGreenKernel eta r :=
    carryWeightedVerticalGreenKernel_nonneg heta0 r
  calc
    ‖carryWeightedVerticalGreenTerm S eta r‖ ≤
        ‖(carryWeightedVerticalGreenKernel eta r : ℝ)‖ * ‖S.shift r‖ := by
      rw [carryWeightedVerticalGreenTerm]
      exact norm_smul_le
        (carryWeightedVerticalGreenKernel eta r : ℝ) (S.shift r)
    _ = carryWeightedVerticalGreenKernel eta r * ‖S.shift r‖ := by
      simp [abs_of_nonneg hk0]
    _ ≤ carryWeightedVerticalGreenKernel eta r * 1 :=
      mul_le_mul_of_nonneg_left (S.norm_shift_le_one r) hk0
    _ = carryWeightedVerticalGreenKernel eta r := by ring

theorem carryWeightedVerticalGreenTerm_summable
    [CompleteSpace H]
    (S : CarryVerticalShiftFamily H) {eta : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    Summable (fun r : ℕ => carryWeightedVerticalGreenTerm S eta r) :=
  (carryWeightedVerticalGreenKernel_summable heta0 heta1).of_norm_bounded
    (fun r => carryWeightedVerticalGreenTerm_norm_le S heta0 r)

def carryWeightedVerticalGreen
    (S : CarryVerticalShiftFamily H) (eta : ℝ) : H →L[ℝ] H :=
  ∑' r : ℕ, carryWeightedVerticalGreenTerm S eta r

theorem carryWeightedVerticalGreen_norm_le_kernelMass
    (S : CarryVerticalShiftFamily H) {eta : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    ‖carryWeightedVerticalGreen S eta‖ ≤
      ∑' r : ℕ, carryWeightedVerticalGreenKernel eta r := by
  have hk : Summable (carryWeightedVerticalGreenKernel eta) :=
    carryWeightedVerticalGreenKernel_summable heta0 heta1
  have hnorm :
      Summable (fun r : ℕ => ‖carryWeightedVerticalGreenTerm S eta r‖) :=
    Summable.of_nonneg_of_le
      (fun r => norm_nonneg (carryWeightedVerticalGreenTerm S eta r))
      (fun r => carryWeightedVerticalGreenTerm_norm_le S heta0 r)
      hk
  rw [carryWeightedVerticalGreen]
  calc
    ‖∑' r : ℕ, carryWeightedVerticalGreenTerm S eta r‖ ≤
        ∑' r : ℕ, ‖carryWeightedVerticalGreenTerm S eta r‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r : ℕ, carryWeightedVerticalGreenKernel eta r :=
      hnorm.tsum_le_tsum
        (fun r => carryWeightedVerticalGreenTerm_norm_le S heta0 r) hk

end ShiftFamily
end
end GeometryOfNumbers.Analysis.RealCarry
