import AllOrderTail

namespace CarryAtomicControl
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Algebraic control sequence: it is not a replacement for the native source. -/
def twoAtomMoment (j : ℕ) : ℝ :=
  (1/100:ℝ)^(j+1)+(1/1000:ℝ)*(1/10:ℝ)^(j+1)

def criticalParameter : ℝ := twoAtomMoment 2 / twoAtomMoment 1

def criticalResidual : ℝ := twoAtomMoment 3 - twoAtomMoment 2^2/twoAtomMoment 1

def criticalCorrection : ℝ :=
  -10*criticalParameter^2*twoAtomMoment 2+168*criticalParameter*twoAtomMoment 3-
    60*twoAtomMoment 4

/-- Exact two-atom measure gives a positive quadratic form for every N. -/
theorem two_atom_gram (N : ℕ) (x : Fin N → ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, x i*x j*twoAtomMoment ((i:ℕ)+(j:ℕ))) =
      (1/100:ℝ)*(∑ i : Fin N, x i*(1/100:ℝ)^(i:ℕ))^2+
      (1/10000:ℝ)*(∑ i : Fin N, x i*(1/10:ℝ)^(i:ℕ))^2 := by
  calc
    _ = ∑ i : Fin N, ∑ j : Fin N,
        ((1/100:ℝ)*(x i*(1/100:ℝ)^(i:ℕ))*(x j*(1/100:ℝ)^(j:ℕ)) +
         (1/10000:ℝ)*(x i*(1/10:ℝ)^(i:ℕ))*(x j*(1/10:ℝ)^(j:ℕ))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [twoAtomMoment,pow_add,pow_succ]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, pow_two, Finset.mul_sum, Finset.sum_mul]
      apply congrArg₂ (· + ·)
      all_goals
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring

theorem two_atom_positive (N : ℕ) (x : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N, x i*x j*twoAtomMoment ((i:ℕ)+(j:ℕ)) := by
  rw [two_atom_gram]
  positivity

/-- Strong source majorant holds in every order, independently of the
negative critical correction below. -/
theorem two_atom_majorant (j : ℕ) :
    |twoAtomMoment j| ≤ (22/175:ℝ)^(j+1)-(1/25:ℝ)^(j+1) := by
  have h1 : (1/100:ℝ)^j ≤ (1/10:ℝ)^j := by exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h2 : (1/25:ℝ)^j ≤ (1/10:ℝ)^j := by exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h3 : (1/10:ℝ)^j ≤ (22/175:ℝ)^j := by exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hp : 0 ≤ (1/10:ℝ)^j := by positivity
  have hq : 0 ≤ (22/175:ℝ)^j := by positivity
  have hn : 0 ≤ twoAtomMoment j := by unfold twoAtomMoment; positivity
  rw [abs_of_nonneg hn]
  unfold twoAtomMoment
  simp only [pow_succ]
  nlinarith

theorem exact_parameter : criticalParameter = 1/55 := by
  norm_num [criticalParameter,twoAtomMoment]

theorem exact_positive_residual : criticalResidual = 81/1100000000 ∧ 0 < criticalResidual := by
  norm_num [criticalResidual,twoAtomMoment]

theorem exact_negative_correction : criticalCorrection = -3347/12100000000 ∧ criticalCorrection < 0 := by
  norm_num [criticalCorrection,criticalParameter,twoAtomMoment]

end
end CarryAtomicControl
